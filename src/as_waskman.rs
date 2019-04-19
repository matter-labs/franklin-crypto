use rand::{
    Rng
};

const EMPTY_STATE: u64 = std::u64::MAX;

// this is basically a grid of size x columns
pub struct AsWaksmanTopology {
    pub topology: Vec<Vec<(u64, u64)>>,
}

impl AsWaksmanTopology {
    pub fn new(size: usize) -> Self {
        assert!(size > 1, "don't make strange moves");

        let num_colunms = Self::num_colunms(size);

        // make the grid
        let mut topology = vec![vec![(EMPTY_STATE, EMPTY_STATE); size]; num_colunms];

        let destinations: Vec<u64> = (0..(size as u64)).collect();

        // recursively iterate and construct the topology
        Self::construct_inner(0, num_colunms-1, 0, size-1, &destinations, &mut topology);

        Self {
            topology
        }
    }

    fn construct_inner(left: usize, right: usize, 
                        low: usize, high: usize,
                        destinations: &[u64],
                        topology: &mut [Vec<(u64, u64)>]) 
    {
        if left > right {
            return;
        }

        // we should be working with a proper size
        let rows_to_generate = high - low + 1;
        assert_eq!(destinations.len(), rows_to_generate);

        let columns_to_generate = Self::num_colunms(rows_to_generate);
        let num_columns = right - left + 1;
        assert!(num_columns >= columns_to_generate);

        if num_columns > columns_to_generate
        {
            // 
            // If there is more space for the routing network than needed,
            // just add straight edges. This also handles the size-1 base case.
            //
            for idx in low..=high {
                topology[low][idx].0 = idx as u64;
                topology[low][idx].1 = idx as u64;

                topology[high][idx].0 = destinations[idx - low];
                topology[high][idx].1 = destinations[idx - low];
            }

            let mut subdestinations = vec![EMPTY_STATE; rows_to_generate];

            for idx in low..=high {
                subdestinations[idx-low] = idx as u64;
            }

            Self::construct_inner(left+1, right-1, low, high, &subdestinations, topology);
        } else if rows_to_generate == 2 {
            topology[left][low].0 = destinations[0];
            topology[left][high].0 = destinations[0];

            topology[left][low].1 = destinations[1];
            topology[left][high].1 = destinations[1];
        } else {
            // recursion step

            let mut subdestinations = vec![EMPTY_STATE; rows_to_generate];
            let subnet_is_even = rows_to_generate % 2 == 0;
            let mut limit = high;
            if !subnet_is_even {
                limit += 1;
            }

            for idx in (low..limit).step_by(2) {
                let top_idx = Self::calculate_in_out_index(rows_to_generate, low, idx, true);
                topology[left][idx].0 = top_idx;
                topology[left][idx+1].1 = top_idx;

                let bottom_idx = Self::calculate_in_out_index(rows_to_generate, low, idx, false);
                topology[left][idx].1 = bottom_idx;
                topology[left][idx+1].0 = bottom_idx;

                subdestinations[(top_idx as usize)-low] = idx as u64;
                subdestinations[(bottom_idx as usize)-low] = (idx + 1) as u64;

                topology[right][idx].0 = subdestinations[idx - low];
                topology[right][idx+1].1 = subdestinations[idx - low];

                topology[right][idx].1 = subdestinations[idx + 1 - low];
                topology[right][idx+1].0 = subdestinations[idx + 1 - low];
            }

            if rows_to_generate % 2 == 1
            {
                topology[left][high].0 = high as u64;
                topology[left][high].1 = high as u64;

                topology[right][high].0 = destinations[high - low];
                topology[right][high].1 = destinations[high - low];

                subdestinations[high - low] = high as u64;
            }
            else
            {
                topology[left][high-1].1 = topology[left][high-1].0;
                topology[left][high].1 = topology[left][high].0;
            }

            let d = rows_to_generate / 2;
            let top_subnet_destinations = &subdestinations[..d];
            let bottom_subnet_destinations = &subdestinations[d..];

            Self::construct_inner(left+1, right-1, low, low + d - 1, top_subnet_destinations, topology);
            Self::construct_inner(left+1, right-1, low + d, high, bottom_subnet_destinations, topology);
        }
    }

    pub fn num_colunms(size: usize) -> usize {
        if size <= 1 {
            return 0;
        }

        let mut c = size;
        let mut num_colunms = 0;
        while c != 0 {
            num_colunms += 1;
            c = c << 1;
        }

        2*num_colunms - 1
    }

    fn calculate_in_out_index(
        size: usize,
        offset: usize,
        index: usize,
        is_top: bool
    ) -> u64 {
        let relative_position = index - offset;
        assert!(relative_position % 2 == 0 && relative_position + 1 < size);
        let mut suboffset = 0;
        if is_top {
            suboffset = size / 2;
        }

        (offset + relative_position/2 + suboffset) as u64
    }
}

pub struct ASWaksman
{
    m_top: Vec<ASWaksman>,
    m_bot: Vec<ASWaksman>,
    m_gate_size: usize,
    m_size: usize,
    m_inputs: Vec<u32>,
    m_outputs: Vec<u32>,
    m_gates: Vec<bool>,
}

impl ASWaksman
{
    fn calculate_gate_size(size: usize) -> usize
    {
        if size == 0 {return 0;}
        if size == 1 {return 0;}
        if size == 2 {return 1;}
        if size == 3 {return 3;}
        if size == 4 {return 5;}

        let is_odd = size % 2 != 0;
        if is_odd == true
        {
            return ASWaksman::calculate_gate_size((size / 2) + 1) + ASWaksman::calculate_gate_size(size / 2) + size - 1;
        }
        return ASWaksman::calculate_gate_size(size / 2) + ASWaksman::calculate_gate_size(size / 2) + size - 1;
    }

    fn set_inputs(&mut self, input: Vec<u32>)
    {
        for i in 0..input.len()
        {
            self.m_inputs[i] = input[i];
        }
    }

    fn calculate_outputs(&mut self)
    {
        if self.m_size == 0 {return;}

        if self.m_size == 1
        {
            self.m_outputs[0] = self.m_inputs[0];
            return;
        }

        if self.m_size == 2 
        {

             if self.m_gates[0] == true
            {
                self.m_outputs[0] = self.m_inputs[1];
                self.m_outputs[1] = self.m_inputs[0];
            }
            else
            {
                self.m_outputs[0] = self.m_inputs[0];
                self.m_outputs[1] = self.m_inputs[1];
            }
            return;
        }

        if self.m_size == 3
        {
            if self.m_gates[0] == true
            {
                self.m_outputs[0] = self.m_inputs[1];
                self.m_outputs[1] = self.m_inputs[0];
            }
            else
            {
                self.m_outputs[0] = self.m_inputs[0];
                self.m_outputs[1] = self.m_inputs[1];
            }

             self.m_outputs[2] = self.m_inputs[2];

             if self.m_gates[2] == true // the "passthrough"
            {
                let tmp = self.m_outputs[1];
                self.m_outputs[1] = self.m_outputs[2];
                self.m_outputs[2] = tmp;
            }

             if self.m_gates[1] == true // the rightmost
            {
                let tmp = self.m_outputs[0];
                self.m_outputs[0] = self.m_outputs[1];
                self.m_outputs[1] = tmp;
            }
            return;
        }

        if self.m_size == 4
        {
            if self.m_gates[0] == true
            {
                self.m_outputs[0] = self.m_inputs[1];
                self.m_outputs[1] = self.m_inputs[0];
            }
            else
            {
                self.m_outputs[0] = self.m_inputs[0];
                self.m_outputs[1] = self.m_inputs[1];
            }

             if self.m_gates[1] == true
            {
                self.m_outputs[2] = self.m_inputs[3];
                self.m_outputs[3] = self.m_inputs[2];
            }
            else
            {
                self.m_outputs[2] = self.m_inputs[2];
                self.m_outputs[3] = self.m_inputs[3];
            }

            // first flip top only line 1 and 2 are flipped
            let tmp = self.m_outputs[1];
            self.m_outputs[1] = self.m_outputs[2];
            self.m_outputs[2] = tmp;

            if self.m_gates[3] == true // middle top gate
            {
                let tmp = self.m_outputs[0];
                self.m_outputs[0] = self.m_outputs[1];
                self.m_outputs[1] = tmp;
            }

            if self.m_gates[4] == true // middle bot gate
            {
                let tmp = self.m_outputs[2];
                self.m_outputs[2] = self.m_outputs[3];
                self.m_outputs[3] = tmp;
            }

             // final flip top only line 1 and 2 are flipped
            let tmp = self.m_outputs[1];
            self.m_outputs[1] = self.m_outputs[2];
            self.m_outputs[2] = tmp;

            if self.m_gates[2] == true // end top gate
            {
                let tmp = self.m_outputs[0];
                self.m_outputs[0] = self.m_outputs[1];
                self.m_outputs[1] = tmp;
            }
            return;
        }

         // size is at least 5
        let num_of_left_gates:usize = self.m_size / 2;
        let my_size = self.m_size;
        let mut tmp_input = vec![0; my_size];        
        // copy to tmp
        for i in 0..my_size
        {
            tmp_input[i] = self.m_inputs[i];
        }

         // first gate check
        for i in 0..num_of_left_gates
        {
            if self.m_gates[i] == true
            {
                let tmp = tmp_input[i*2];
                tmp_input[i * 2] = tmp_input[i * 2 + 1];
                tmp_input[i * 2 + 1] = tmp;
            }
        }

        let mut tmp_input_top = vec![0; num_of_left_gates];
        let mut tmp_input_bot = vec![0; my_size - num_of_left_gates];
        let mut countleft = 0;
        let mut countright = 0;       
        // spliting the inputs to top and bottom
        for i in 0..my_size
        {
            if i % 2 == 0 // counting from 0 is funny..
            {
                if i == (my_size - 1)
                {
                   tmp_input_bot[countright] = tmp_input[i];
                    countright += 1;
                }
                else
                {
                    tmp_input_top[countleft] = tmp_input[i];
                    countleft += 1;
                }  
            }
            else
            {
                tmp_input_bot[countright] = tmp_input[i];
                countright += 1;
            }
        }

         // copy back
        for i in 0..my_size
        {
            if i >= tmp_input_top.len()
            {
                tmp_input[i] = tmp_input_bot[i - tmp_input_top.len()];
            }
            else
            {
                tmp_input[i] = tmp_input_top[i];
            }
        }

         // send into recursive wakeman
        if self.m_top.len() != 0
        {
            let top_size = self.m_top[0].m_size;
            let mut tmp_top_input = vec![0; top_size];
            for i in 0..top_size
            {
                tmp_top_input[i] = tmp_input[i];
            }
            self.m_top[0].set_inputs(tmp_top_input);
            self.m_top[0].calculate_outputs();
        }

         if self.m_bot.len() != 0
        {
            let bot_size = self.m_bot[0].m_size;
            let mut tmp_bot_input = vec![0; bot_size];
            for i in 0..bot_size
            {
                let mut top_size_for_bot:usize = 0;
                if self.m_top.len() != 0
                {
                    top_size_for_bot = self.m_top[0].m_size;
                }
                let offset_counter_bottom = i + top_size_for_bot;
                if offset_counter_bottom >= my_size
                {
                    tmp_bot_input[i] = tmp_input[tmp_input.len()-1];
                }
                else
                {
                    tmp_bot_input[i] = tmp_input[offset_counter_bottom];
                }
            }
            self.m_bot[0].set_inputs(tmp_bot_input);
            self.m_bot[0].calculate_outputs();
        }

         // extraction of data from internal structures
        if self.m_top.len() != 0
        {
            let top_size:usize = self.m_top[0].m_size;
            for i in 0..top_size
            {
                tmp_input[i] = self.m_top[0].m_outputs[i];
            }
        }

         if self.m_bot.len() != 0
        {
            let bot_size:usize = self.m_bot[0].m_size;
            for i in 0..bot_size
            {
                let mut top_size_out:usize = 0;
                if self.m_top.len() != 0 
                {
                    top_size_out = self.m_top[0].m_size;
                }
                tmp_input[i + top_size_out] = self.m_bot[0].m_outputs[i];
            }
        }

         // last gate check
        let mut num_of_right_gates:usize = my_size / 2;
        if my_size % 2 == 0
        {
            num_of_right_gates -= 1
        }

         // spliting the inputs to top and bottom
        countleft = 0;
        countright = 0;
        for i in 0..my_size
        {
            if i % 2 == 0 // counting from 0 is funny..
            {
                if i == my_size - 1
                {
                    tmp_input_bot[countright] = tmp_input[i];
                    countright += 1;
                }
                else
                {
                    tmp_input_top[countleft] = tmp_input[i];
                    countleft += 1;
                }  
            }
            else
            {
                tmp_input_bot[countright] = tmp_input[i];
                countright += 1;
            }
        }

         // copy back
        for i in 0..my_size
        {
            if i >= tmp_input_top.len()
            {
                tmp_input[i] = tmp_input_bot[i - tmp_input_top.len()];
            }
            else
            {
                tmp_input[i] = tmp_input_top[i];
            }
        }

         for i in 0..num_of_right_gates
        {
            let counter_final_gate = i + num_of_left_gates - 1;
            if self.m_gates[counter_final_gate] == true 
            {
                let right_gate_tmp = tmp_input[i * 2];
                tmp_input[i * 2] = tmp_input[i * 2 + 1];
                tmp_input[i * 2 + 1] = right_gate_tmp;
            }
        }

         // copy to outputs
        for i in 0..my_size
        {
            self.m_outputs[i] = tmp_input[i];
        }
        return;
    }

     fn calculate_witness(self)-> Vec<bool>
    {
        let max_count = 2_u64.pow(self.m_gate_size as u32); // this is max permutations to bruteforce
        let failed_permuation = vec![];
        let mut cur_permuation = vec![false; self.m_gate_size];
        for j in 0..max_count
        {
            // change the configuration to handle stuffs.
            for i in 0..self.m_gate_size
            {
                let currentindex = j & (1 << i);
                if currentindex != 0
                {
                    cur_permuation[i] = true;
                }
                else
                {
                    cur_permuation[i] = false;
                }
            }


             // calculate a new permutation
            let mut test_aswaksman = ASWaksman::new_internal(self.m_size, self.m_inputs.clone(), self.m_outputs.clone(), cur_permuation.clone());
            test_aswaksman.calculate_outputs();

             let mut is_result_good = true;
            for i in 0..self.m_size
            {
                if test_aswaksman.m_outputs[i] != self.m_outputs[i]
                {
                    is_result_good = false;
                    break;
                }
            }

             if is_result_good
            {
                return cur_permuation;
            }
        }

         return failed_permuation;
    }

     #[allow(dead_code)]
    fn new(size: usize) -> ASWaksman
    {
        return ASWaksman::new_internal(size, vec![], vec![], vec![])
    }

     fn new_internal(size: usize, input: Vec<u32>, output: Vec<u32>, _gates: Vec<bool>) -> ASWaksman
    {
        let gate_size = ASWaksman::calculate_gate_size(size);
        let mut top = vec![];
        let mut bot = vec![];

         // recursive creation
        let top_size:usize = size / 2;
        let mut bot_size = top_size + 1;
        if size % 2 == 0 {bot_size = top_size}
        let rounded_down_gates:usize;
        if size % 2 == 0 {rounded_down_gates = size} else {rounded_down_gates = size - 1}

         // only split if its more than 4
        if size > 4
        {
            // handle gates
            // handle top gate
            let top_gate_size = ASWaksman::calculate_gate_size(top_size);
            let mut top_gates = vec![false; top_gate_size];
            if top_gate_size != 0
            {
                for i in 0..top_gate_size
                {
                    let offset_count = i + rounded_down_gates - 1;
                    top_gates[i] = _gates[offset_count];
                }
            }
            // handle bot gate
            let bot_gate_size = ASWaksman::calculate_gate_size(bot_size);
            let mut bot_gates = vec![false; bot_gate_size];
            if bot_gate_size != 0
            {
                for i in 0..bot_gate_size
                {                   
                    let offset_count = i + rounded_down_gates - 1 + top_gate_size;
                    bot_gates[i] = _gates[offset_count];
                }
            }

             // handle inputs
            // handle top half of aswakeman inputs
            let mut top_inputs = vec![0; top_size];
            if top_size != 0
            {
                for i in 0..top_size
                {
                    let offset_count = i * 2; //-> 0, 2, 4
                    top_inputs[i] = input[offset_count];
                }
            }

             let mut bot_inputs = vec![0; bot_size];
            if bot_size != 0
            {
                for i in 0..bot_size
                {
                    let offset_count = (i * 2) + 1; // -> 1,3,5,7 i
                    if offset_count >= size
                    { 
                        bot_inputs[bot_size - 1] = input[offset_count - 1];
                    }
                    else
                    {
                        bot_inputs[i] = input[offset_count];
                    }

                 }
            }

             // handle outputs
            // handle top half of aswakeman outputs
            let mut top_outputs = vec![0; top_size];
            if top_size != 0
            {
                for i in 0..top_size
                {
                    let offset_count = i*2;
                    top_outputs[i] = output[offset_count];
                }
            }

             let mut bot_outputs = vec![0; bot_size];
            if bot_size != 0
            {
                for i in 0..bot_size
                {
                    let offset_count = (i*2) + 1;
                    if offset_count >= (size) {break;}
                    bot_outputs[i] = output[offset_count];
                }
            }

             // recursive construction
            if top_size > 1
            {
                top.push(ASWaksman::new_internal(top_size, top_inputs, top_outputs, top_gates));
            }

             if bot_size > 1
            {
                bot.push(ASWaksman::new_internal(bot_size, bot_inputs, bot_outputs, bot_gates));
            }
        }
        return ASWaksman 
        {
            m_top: top,
            m_bot: bot,
            m_gate_size: gate_size,
            m_size: size,
            m_inputs: input,
            m_outputs: output,
            m_gates: _gates,
        };
    }

     #[allow(dead_code)]
    fn print(&self) -> String
    {
        return String::from(format!("ASWaksman: {} {:?} {:?} {:?}",self.m_size, self.m_inputs, self.m_outputs, self.m_gates));
    }
}

pub struct IntegerPermutation {
    pub elements: Vec<u64>,
    pub elements_permuted: Vec<u64>,
    pub min: u64,
    pub max: u64
}

impl IntegerPermutation {
    pub fn new(size: usize) -> Self {
        Self::new_from(0, size)
    }

    pub fn new_from(from: usize, size: usize) -> Self {
        let elements: Vec<u64> = ((from as u64)..((from+size) as u64)).map(|e| e).collect();

        Self {
            elements,
            elements_permuted: vec![],
            min: from as u64,
            max: (from+size - 1) as u64
        }
    }

    pub fn size(&self) -> usize {
        self.elements.len()
    }

    pub fn make_permutation<R: Rng>(&mut self, rng: &mut R) {
        let mut copy = self.elements.clone();
        rng.shuffle(&mut copy);
        self.elements_permuted = copy;
    }

    pub fn get(&self, index: usize) -> u64 {
        self.elements_permuted[index]
    }

    pub fn inverse(&self) -> Self {
        let mut new_permutation = vec![0u64; self.size()];
        for idx in 0..self.size() {
            new_permutation[(self.elements_permuted[idx] - self.min) as usize] = (idx as u64) + self.min;
        }

        Self {
            elements: self.elements.clone(),
            elements_permuted: self.elements.clone(),
            min: self.min,
            max: self.max
        }
    }

    pub fn is_valid(&self) -> bool {
        if self.elements_permuted.len() == 0 {
            return false;
        }
        let mut set: std::collections::HashSet<u64, > = std::collections::HashSet::with_capacity(self.elements.len());
        for element in self.elements_permuted.iter() {
            if *element < self.min || *element > self.max {
                return false;
            }
            if set.contains(element) {
                return false;
            }
            set.insert(*element);
        }

        true
    }    
}

// this is basically a grid of size x columns
pub struct AsWaksmanRoute {
    pub topology: AsWaksmanTopology
}

impl AsWaksmanRoute {
    pub fn new(permutation: &IntegerPermutation) -> Self {
        unimplemented!();
    }
}