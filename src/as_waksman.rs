use rand::{
    Rng
};

const EMPTY_STATE: usize = std::usize::MAX;

// this is basically a grid of size x columns
pub struct AsWaksmanTopology {
    pub topology: Vec<Vec<(usize, usize)>>,
    pub size: usize
    // pub switches: Vec<std::collections::HashMap<usize, bool>>
}

impl AsWaksmanTopology {
    pub fn new(size: usize) -> Self {
        assert!(size > 1, "don't make strange moves");

        let num_colunms = Self::num_colunms(size);

        // make the grid
        let mut topology = vec![vec![(EMPTY_STATE, EMPTY_STATE); size]; num_colunms];

        let destinations: Vec<usize> = (0..size).collect();

        // recursively iterate and construct the topology
        Self::construct_inner(0, num_colunms-1, 0, size-1, &destinations, &mut topology);

        Self {
            topology,
            size
        }
    }

    fn calculate_top_height(size: usize) -> usize {
        size / 2
    }

    fn construct_inner(left: usize, right: usize, 
                        low: usize, high: usize,
                        destinations: &[usize],
                        topology: &mut [Vec<(usize, usize)>]) 
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
                topology[left][idx].0 = idx;
                topology[left][idx].1 = idx;

                topology[right][idx].0 = destinations[idx - low];
                topology[right][idx].1 = destinations[idx - low];
            }
            let mut subdestinations = vec![EMPTY_STATE; rows_to_generate];

            for idx in low..=high {
                subdestinations[idx-low] = idx;
            }

            Self::construct_inner(left+1, right-1, low, high, &subdestinations, topology);
        } else if rows_to_generate == 2 {
            topology[left][low].0 = destinations[0];
            topology[left][high].1 = destinations[0];

            topology[left][low].1 = destinations[1];
            topology[left][high].0 = destinations[1];
        } else {
            // recursion step

            let mut subdestinations = vec![EMPTY_STATE; rows_to_generate];
            let limit = if rows_to_generate % 2 == 1 {
                high
            } else {
                high + 1
            };

            for idx in (low..limit).step_by(2) {
                let top_idx = Self::calculate_in_out_index(rows_to_generate, low, idx, true);
                topology[left][idx].0 = top_idx;
                topology[left][idx+1].1 = top_idx;

                let bottom_idx = Self::calculate_in_out_index(rows_to_generate, low, idx, false);
                topology[left][idx].1 = bottom_idx;
                topology[left][idx+1].0 = bottom_idx;

                subdestinations[(top_idx as usize) - low] = idx;
                subdestinations[(bottom_idx as usize) - low] = idx + 1;

                topology[right][idx].0 = destinations[idx - low];
                topology[right][idx+1].1 = destinations[idx - low];

                topology[right][idx].1 = destinations[idx + 1 - low];
                topology[right][idx+1].0 = destinations[idx + 1 - low];
            }

            if rows_to_generate % 2 == 1
            {
                topology[left][high].0 = high;
                topology[left][high].1 = high;

                topology[right][high].0 = destinations[high - low];
                topology[right][high].1 = destinations[high - low];

                subdestinations[high - low] = high;
            }
            else
            {
                topology[left][high-1].1 = topology[left][high-1].0;
                topology[left][high].1 = topology[left][high].0;
            }

            let d = AsWaksmanTopology::calculate_top_height(rows_to_generate);
            let top_subnet_destinations = &subdestinations[..d];
            let bottom_subnet_destinations = &subdestinations[d..];

            Self::construct_inner(left+1, right-1, low, low + d - 1, top_subnet_destinations, topology);
            Self::construct_inner(left+1, right-1, low + d, high, bottom_subnet_destinations, topology);
        }
    }

    pub(crate) fn num_colunms(size: usize) -> usize {
        if size <= 1 {
            return 0;
        }

        let as_float = f64::from(size as u32);

        let ceil = as_float.log(2.0).ceil();
        let num_colunms = ceil as usize;

        2*num_colunms - 1
    }

    fn calculate_in_out_index(
        size: usize,
        offset: usize,
        index: usize,
        is_top: bool
    ) -> usize {
        let mut relative_position = index - offset;
        assert!(relative_position % 2 == 0 && relative_position + 1 < size);
        relative_position >>= 1;
        let mut suboffset = 0;
        if !is_top {
            suboffset = AsWaksmanTopology::calculate_top_height(size);
        }

        offset + relative_position + suboffset
    }
}

// Integer representation should always be generated starting from 0 and only internal calls should
// generate it from non-zero start

#[derive(Debug)]
pub struct IntegerPermutation {
    pub elements: Vec<usize>,
    pub min: usize,
    pub max: usize
}

impl IntegerPermutation {
    pub fn new(size: usize) -> Self {
        Self::new_for_max_and_min(0, size - 1)
    }

    pub fn new_from_permutation(permutation: Vec<u64>) -> Self {
        unimplemented!();
    }

    pub(crate) fn new_for_max_and_min(min: usize, max: usize) -> Self {
        let elements: Vec<usize> = (min..=max).collect();

        Self {
            elements,
            min: min,
            max: max
        }
    }

    pub fn size(&self) -> usize {
        self.max - self.min + 1
        // self.elements.len()
    }

    pub fn make_permutation<R: Rng>(&mut self, rng: &mut R) {
        let mut copy = self.elements.clone();
        rng.shuffle(&mut copy);
        self.elements = copy;
    }

    pub fn get(&self, index: usize) -> usize {
        assert!(index >= self.min && index <= self.max);
        self.elements[index - self.min]
    }

    pub fn set(&mut self, index: usize, value: usize) {
        assert!(index >= self.min && index <= self.max);
        self.elements[index - self.min] = value;
    }

    pub fn slice(&self, min: usize, max: usize) -> Self {
        assert!(self.min <= min && min <= max && max <= self.max);

        let result = Self {
            elements: self.elements[(min - self.min)..(max - self.min + 1)].to_vec(),
            min: min,
            max: max
        };

        assert!(result.size() == result.elements.len());

        result
    }

    pub fn inverse(&self) -> Self {
        let mut new = Self::new_for_max_and_min(self.min, self.max);
        for idx in self.min..=self.max {
            new.elements[self.elements[idx - self.min] - self.min] = idx;
        }

        new
    }

    pub fn is_valid(&self) -> bool {
        if self.elements.len() == 0 {
            return true;
        }

        let mut set: std::collections::HashSet<usize, > = std::collections::HashSet::with_capacity(self.elements.len());
        for element in self.elements.iter() {
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
    pub switches: Vec<std::collections::HashMap<usize, bool>>,
    pub size: usize
}

impl AsWaksmanRoute {
    pub fn new(permutation: &IntegerPermutation) -> Self {
        let size = permutation.size();
        let num_columns = AsWaksmanTopology::num_colunms(size);
        let empty_assignment: std::collections::HashMap<usize, bool> = std::collections::HashMap::new();
        let mut assignments = vec![empty_assignment; num_columns];

        let inversed_permutation = permutation.inverse();
        assert!(inversed_permutation.inverse().elements == permutation.elements);
        Self::construct_inner(0, num_columns-1, 0, size-1, permutation, &inversed_permutation, &mut assignments);

        Self {
            switches: assignments,
            size
        }
    }

    fn get_canonical_row_index(offset: usize, row_index: usize) -> usize {
        let suboffset = row_index - offset;

        let mask = std::usize::MAX - 1;

        (suboffset & mask) + offset
    }

    fn get_switch_setting_from_top_bottom_decision(offset: usize, packet_index: usize, is_top: bool) -> bool {
        let row_index = Self::get_canonical_row_index(offset, packet_index);

        (packet_index == row_index) ^ is_top
    }

    fn get_top_bottom_decision_from_switch_setting(offset: usize, packet_index: usize, is_on: bool) -> bool {
        let row_index = Self::get_canonical_row_index(offset, packet_index);

        (row_index == packet_index) ^ is_on
    }

    fn calculate_other_position(offset: usize, packet_index: usize) -> usize {
        let row_index = Self::get_canonical_row_index(offset, packet_index);
        (1 - (packet_index - row_index)) + row_index
    }

    fn construct_inner(
        left: usize, right: usize,
        low: usize, high: usize,
        permutation: &IntegerPermutation,
        permutation_inversed: &IntegerPermutation,
        switches: &mut [std::collections::HashMap<usize, bool>]
    ) {
        if left > right
        {
            return;
        }

        let rows_to_generate = high - low + 1;
        let columns_to_generate = AsWaksmanTopology::num_colunms(rows_to_generate);
        let num_columns = right - left + 1;
        assert!(num_columns >= columns_to_generate);

        assert!(permutation.min == low);
        assert!(permutation.max == high);
        assert!(permutation.size() == rows_to_generate);
        assert!(permutation.is_valid());
        assert!(permutation.inverse().elements == permutation_inversed.elements);
        assert!(permutation_inversed.inverse().elements == permutation.elements);

        if num_columns > columns_to_generate
        {
            Self::construct_inner(left+1, right - 1, low, high, permutation, permutation_inversed, switches);
        }
        else if rows_to_generate == 2
        {
            assert!(permutation.get(low) == low || permutation.get(low) == low+1);
            assert!(permutation.get(low+1) == low || permutation.get(low+1) == low+1);
            assert!(permutation.get(low) != permutation.get(low+1));

            switches[left].insert(low, permutation.get(low) != low);
        }
        else
        {
            //
            // The algorithm first assigns a setting to a LHS switch,
            // route its target to RHS, which will enforce a RHS switch setting.
            // Then, it back-routes the RHS value back to LHS.
            // If this enforces a LHS switch setting, then forward-route that;
            // otherwise we will select the next value from LHS to route.
            //
            let mut new_permutation = IntegerPermutation::new_for_max_and_min(low, high);
            let mut new_permutation_inversed = IntegerPermutation::new_for_max_and_min(low, high);
            let mut lhs_is_routed = vec![false; rows_to_generate];

            let mut to_route;
            let mut max_unrouted;

            let mut should_route_left;

            if rows_to_generate % 2 == 1
            {
                //
                // ODD CASE: we first deal with the bottom-most straight wire,
                // which is not connected to any of the switches at this level
                // of recursion and just passed into the lower subnetwork.
                //
                if permutation.get(high) == high
                {
                    //
                    // Easy sub-case: it is routed directly to the bottom-most
                    // wire on RHS, so no switches need to be touched.
                    //
                    new_permutation.set(high, high);
                    new_permutation_inversed.set(high, high);
                    to_route = high - 1;
                    should_route_left = true;
                }
                else
                {
                    //
                    // Other sub-case: the straight wire is routed to a switch
                    // on RHS, so route the other value from that switch
                    // using the lower subnetwork.
                    //
                    let rhs_switch = Self::get_canonical_row_index(low, permutation.get(high));
                    let rhs_switch_setting = Self::get_switch_setting_from_top_bottom_decision(low, permutation.get(high), false);
                    switches[right].insert(rhs_switch, rhs_switch_setting);

                    let tprime = AsWaksmanTopology::calculate_in_out_index(rows_to_generate, low, rhs_switch, false);
                    new_permutation.set(high, tprime);
                    new_permutation_inversed.set(tprime, high);

                    to_route = Self::calculate_other_position(low, permutation.get(high));

                    should_route_left = false;
                }

                lhs_is_routed[high - low] = true;
                max_unrouted = high - 1;
            }
            else
            {
                //
                // EVEN CASE: the bottom-most switch is fixed to a constant
                // straight setting. So we route wire hi accordingly.
                //
                switches[left].insert(high - 1, false);
                to_route = high;
                should_route_left = true;
                max_unrouted = high;
            }

            loop
            {
                //
                // INVARIANT: the wire `to_route' on LHS (if route_left = true),
                // resp., RHS (if route_left = false) can be routed.
                //
                if should_route_left
                {
                    // If switch value has not been assigned, assign it arbitrarily.
                    let lhs_switch = Self::get_canonical_row_index(low, to_route);
                    if switches[left].get(&lhs_switch).is_none()
                    {
                        switches[left].insert(lhs_switch, false);
                    }
                    let lhs_switch_setting = *switches[left].get(&lhs_switch).unwrap();
                    let should_use_top = Self::get_top_bottom_decision_from_switch_setting(low, to_route, lhs_switch_setting);
                    let t = AsWaksmanTopology::calculate_in_out_index(rows_to_generate, low, lhs_switch, should_use_top);
                    if permutation.get(to_route) == high
                    {
                        //
                        // We have routed to the straight wire for the odd case,
                        // so now we back-route from it.
                        //
                        new_permutation.set(t, high);
                        new_permutation_inversed.set(high, t);
                        lhs_is_routed[to_route - low] = true;
                        to_route = max_unrouted;
                        should_route_left = true;
                    }
                    else
                    {
                        let rhs_switch = Self::get_canonical_row_index(low, permutation.get(to_route));
                        //
                        // We know that the corresponding switch on the right-hand side
                        // cannot be set, so we set it according to the incoming wire.
                        //
                        assert!(switches[right].get(&rhs_switch).is_none());

                        let switch_setting = Self::get_switch_setting_from_top_bottom_decision(low, permutation.get(to_route), should_use_top);
                        switches[right].insert(rhs_switch, switch_setting);
                        let tprime = AsWaksmanTopology::calculate_in_out_index(rows_to_generate, low, rhs_switch, should_use_top);
                        new_permutation.set(t, tprime);
                        new_permutation_inversed.set(tprime, t);

                        lhs_is_routed[to_route - low] = true;
                        to_route = Self::calculate_other_position(low, permutation.get(to_route));
                        should_route_left = false;
                    }
                }
                else
                {
                    //
                    // We have arrived on the right-hand side, so the switch setting is fixed.
                    // Next, we back route from here.
                    //
                    let rhs_switch = Self::get_canonical_row_index(low, to_route);
                    let lhs_switch = Self::get_canonical_row_index(low, permutation_inversed.get(to_route));
                    assert!(switches[right].get(&rhs_switch).is_some());
                    let rhs_switch_setting = *switches[right].get(&rhs_switch).unwrap();
                    let should_use_top = Self::get_top_bottom_decision_from_switch_setting(low, to_route, rhs_switch_setting);
                    let lhs_switch_setting = Self::get_switch_setting_from_top_bottom_decision(low, permutation_inversed.get(to_route) as usize, should_use_top);

                    // The value on the left-hand side is either the same or not set
                    if let Some(value) = switches[left].get(&lhs_switch) {
                        assert!(*value == lhs_switch_setting);
                    }

                    switches[left].insert(lhs_switch, lhs_switch_setting);

                    let t = AsWaksmanTopology::calculate_in_out_index(rows_to_generate, low, rhs_switch, should_use_top);
                    let tprime = AsWaksmanTopology::calculate_in_out_index(rows_to_generate, low, lhs_switch, should_use_top);
                    new_permutation.set(tprime, t);
                    new_permutation_inversed.set(t, tprime);

                    lhs_is_routed[permutation_inversed.get(to_route) - low] = true;
                    to_route = Self::calculate_other_position(low, permutation_inversed.get(to_route));
                    should_route_left = true;
                }

                /* If the next packet to be routed hasn't been routed before, then try routing it. */
                if !should_route_left || !lhs_is_routed[to_route-low]
                {
                    continue;
                }

                /* Otherwise just find the next unrouted packet. */
                while max_unrouted > low && lhs_is_routed[max_unrouted-low]
                {
                    max_unrouted -= 1;
                }

                if max_unrouted < low || (max_unrouted == low && lhs_is_routed[0])
                {
                    /* All routed! */
                    break;
                }
                else
                {
                    to_route = max_unrouted;
                    should_route_left = true;
                }
            }

            if rows_to_generate % 2 == 0
            {
                /* Remove the AS-Waksman switch with the fixed value. */
                switches[left].remove(&(high - 1));
            }

            assert!(new_permutation.is_valid());
            assert!(new_permutation_inversed.is_valid());

            let d = AsWaksmanTopology::calculate_top_height(rows_to_generate);
            let new_permutation_upper = new_permutation.slice(low, low + d - 1);
            let new_permutation_lower = new_permutation.slice(low + d, high);

            let new_permutation_inversed_upper = new_permutation_inversed.slice(low, low + d - 1);
            let new_permutation_inversed_lower = new_permutation_inversed.slice(low + d, high);

            Self::construct_inner(left+1, right-1, low, low + d - 1, &new_permutation_upper, &new_permutation_inversed_upper, switches);
            Self::construct_inner(left+1, right-1, low + d, high, &new_permutation_lower, &new_permutation_inversed_lower, switches);
        }
    }

    fn validate_routing_for_permutation(permutation: &IntegerPermutation,
                                        routing: &Self) -> bool 
    {
        let size = permutation.size();
        let num_columns = AsWaksmanTopology::num_colunms(size);
        let topology = AsWaksmanTopology::new(size);

        let mut current_perm = IntegerPermutation::new(size);

        for column_idx in 0..num_columns {
            let mut next_perm = IntegerPermutation::new(size);
            for packet_idx in 0..size {
                let mut routed_index;
                if topology.topology[column_idx][packet_idx].0 == topology.topology[column_idx][packet_idx].1 {
                    // straight switch
                    routed_index = topology.topology[column_idx][packet_idx].0;
                }
                else
                {
                    let a = routing.switches[column_idx].get(&packet_idx);
                    let b = if packet_idx > 0 {
                        routing.switches[column_idx].get(&(packet_idx - 1))
                    } else {
                        None
                    };
                    assert!(a.is_some() ^ b.is_some());
                    let switch_setting = if a.is_some() {
                        *a.unwrap()
                    } else {
                        *b.unwrap()
                    };
                    
                    routed_index = if switch_setting {
                        topology.topology[column_idx][packet_idx].1
                    } else {
                        topology.topology[column_idx][packet_idx].0
                    };
                }

                let val = current_perm.get(packet_idx);
                next_perm.set(routed_index, val);
            }

            current_perm = next_perm;
        }

        current_perm.elements == permutation.inverse().elements
    }

    fn get_number_of_gates(&self) -> usize {
        let mut result = 0;
        for column in self.switches.iter() {
            result += column.len();
        }

        result
    }

    fn assign_switches(&mut self, switch_assignments: &[bool]) {
        let required_switches = self.get_number_of_gates();
        assert!(switch_assignments.len() == required_switches);
        let mut i = 0;
        for column in self.switches.iter_mut() {
            let mut keys = column.keys().cloned().into_iter().collect::<Vec<_>>();
            keys.sort();
            keys.reverse();
            for k in keys.into_iter() {
                column.insert(k, switch_assignments[i]);
                i += 1;
            }
        }
    }

    fn dump_assignments(&self) -> Vec<bool> {
        let mut result = vec![false; self.get_number_of_gates()];
        let mut i = 0;
        for column in self.switches.iter() {
            let mut keys = column.keys().cloned().into_iter().collect::<Vec<_>>();
            keys.sort();
            keys.reverse();
            for k in keys.into_iter() {
                result[i] = *column.get(&k).unwrap();
                i += 1;
            }
        }

        result
    }


    // this function forwards newly created ordered set [0, n) into the permutation by switches
    // that were supplied to the router
    fn calculate_permutation(&self) -> IntegerPermutation 
    {
        let num_columns = AsWaksmanTopology::num_colunms(self.size);
        let topology = AsWaksmanTopology::new(self.size);

        let mut permutation = IntegerPermutation::new(self.size);

        for column_idx in 0..num_columns {
            let mut permutation_by_this_column = IntegerPermutation::new(self.size);
            for packet_idx in 0..self.size {
                let mut routed_into;
                if topology.topology[column_idx][packet_idx].0 == topology.topology[column_idx][packet_idx].1 {
                    // straight switch
                    routed_into = topology.topology[column_idx][packet_idx].0;
                }
                else
                {
                    let a = self.switches[column_idx].get(&packet_idx);
                    let b = if packet_idx > 0 {
                        self.switches[column_idx].get(&(packet_idx - 1))
                    } else {
                        None
                    };
                    assert!(a.is_some() ^ b.is_some());
                    let switch_setting = if a.is_some() {
                        *a.unwrap()
                    } else {
                        *b.unwrap()
                    };
                    
                    routed_into = if switch_setting {
                        topology.topology[column_idx][packet_idx].1
                    } else {
                        topology.topology[column_idx][packet_idx].0
                    };
                }

                let value_at_this_level = permutation.get(packet_idx);
                permutation_by_this_column.set(routed_into, value_at_this_level);
            }
            
            // permutation that we keep a track on is now replaced by result of permutation by this column
            permutation = permutation_by_this_column;
        }

        permutation.inverse()
    }
}

#[test]
fn test_aswaksman() {
    use rand::{Rand, thread_rng};
    let size = 3;

    let mut permutation = IntegerPermutation::new(size);
    let rng = &mut thread_rng();
    permutation.make_permutation(rng);
    // println!("Permutation = {:?}", permutation);
    // println!("Inverse = {:?}", permutation.inverse());
    // println!("Permutation = {:?}", permutation.elements);
    let no_permutation = IntegerPermutation::new(size);
    assert!(permutation.inverse().inverse().elements == permutation.elements);

    let router = AsWaksmanRoute::new(&permutation);

    let is_valid = AsWaksmanRoute::validate_routing_for_permutation(&permutation, &router);
}

#[test]
fn test_back_and_forward_pass() {
    use rand::{Rand, thread_rng};
    let rng = &mut thread_rng();
    for size in 3..4 {
        let mut permutation = IntegerPermutation::new(size);
        permutation.make_permutation(rng);

        let router = AsWaksmanRoute::new(&permutation);
        println!("Permutation = {:?}", permutation.elements);

        let is_valid = AsWaksmanRoute::validate_routing_for_permutation(&permutation, &router);
        assert!(is_valid);

        let new_shuffle = router.calculate_permutation();
        println!("Obtained shuffle = {:?}", new_shuffle.elements);
        assert!(new_shuffle.elements == permutation.elements);
    }
}

#[test]
fn test_forward_pass() {
    use rand::{Rand, thread_rng};
    let rng = &mut thread_rng();
    for size in 3..9 {
        let mut permutation = IntegerPermutation::new(size);
        permutation.make_permutation(rng);

        let router = AsWaksmanRoute::new(&permutation);

        let is_valid = AsWaksmanRoute::validate_routing_for_permutation(&permutation, &router);
        assert!(is_valid);

        let dump = router.dump_assignments();
        let no_permutation = IntegerPermutation::new(size);
        let mut router = AsWaksmanRoute::new(&no_permutation);
        router.assign_switches(&dump);
        let shuffle = router.calculate_permutation();

        assert!(shuffle.elements == permutation.elements);
    }
}

#[test]
fn test_trivial_permutations() {
    use rand::{Rand, thread_rng};
    let rng = &mut thread_rng();
    let topology = AsWaksmanTopology::new(3);
    // println!("Topology = {:?}", topology.topology);
    for _ in 0..100 {
        for size in 2..128 {
            let mut permutation = IntegerPermutation::new(size);
            permutation.make_permutation(rng);
            assert!(permutation.inverse().inverse().elements == permutation.elements);
        }
    }
}

#[test]
fn test_routing_for_permutation() {
    use rand::{Rand, thread_rng};
    let rng = &mut thread_rng();
    let topology = AsWaksmanTopology::new(3);
    // println!("Topology = {:?}", topology.topology);
    for size in 2..128 {
        println!("size = {}", size);
        for _ in 0..100 {
            let mut permutation = IntegerPermutation::new(size);
            // permutation.elements = vec![2, 1, 0];
            permutation.make_permutation(rng);
            // println!("P = {:?}, P_inv = {:?}", permutation, permutation.inverse());
            assert!(permutation.inverse().inverse().elements == permutation.elements);

            let router = AsWaksmanRoute::new(&permutation);

            let is_valid = AsWaksmanRoute::validate_routing_for_permutation(&permutation, &router);
            assert!(is_valid);
        }
    }
}

#[test]
fn test_uniformity() {
    use rand::{Rand, thread_rng};
    let rng = &mut thread_rng();
    let size = 64;
    let mut hists: Vec<std::collections::HashMap<usize, f64>> = vec![std::collections::HashMap::new(); size];
    let permutation = IntegerPermutation::new(size);
    let mut router = AsWaksmanRoute::new(&permutation);
    let num_switches = router.get_number_of_gates();
    let num_trials = 1000000;
    for _ in 0..num_trials {
        let switches: Vec<bool> = (0..num_switches).map(|_| rng.gen::<bool>()).collect();
        router.assign_switches(&switches);
        let shuffle = router.calculate_permutation();
        for i in 0..size {
            let subhist = &mut hists[i];
            let routed_into = shuffle.elements[i];
            if subhist.get(&routed_into).is_some() {
                let e = subhist.get_mut(&routed_into).unwrap();
                *e += 1.0;
            } else {
                subhist.insert(routed_into, 1.0);
            }
        }
    }

    let mut min_xi_squared = 10000000000f64;
    let mut max_xi_squared = 0.0f64;

    let mut max_idx = 0;
    let mut min_idx = 0;

    for i in 0..size {
        let subhist = &hists[i];
        let mut xi_squared = 0.0f64;
        let expected = (num_trials as f64) / (size as f64);
        for (_, v) in subhist.iter() {
            xi_squared += (v - expected)*(v - expected)/expected;
        }

        if xi_squared > max_xi_squared {
            max_xi_squared = xi_squared;
            max_idx = i;
        }

        if xi_squared < min_xi_squared {
            min_xi_squared = xi_squared;
            min_idx = i;
        }
    }

    println!("Max XI^2 = {} for bin {}", max_xi_squared, max_idx);
    println!("Min XI^2 = {} for bin {}", min_xi_squared, min_idx);

    // let norm = num_trials as f64;
    // let mut reference_cdf = vec![0.0f64; size];
    // for i in 0..size {
    //     reference_cdf[i] = ((i+1) as f64)/(size as f64);
    // }
    // assert_eq!(reference_cdf[size-1], 1.0f64);

    // let mut global_max = 0.0f64;

    // for i in 0..size {
    //     let mut normalized = vec![0.0f64; size];
    //     let subhist = &hists[i];
    //     for (k, v) in subhist.iter() {
    //         normalized[*k] = v / norm;
    //     }
    //     let mut cdf = vec![0.0f64; size];
    //     cdf[0] = normalized[0];
    //     for k in 1..size {
    //         cdf[k] = normalized[k] + cdf[k-1]; 
    //     }
    //     assert!(cdf[size-1] >= 0.99999);
    //     let mut max = 0.0f64;
    //     for k in 0..size {
    //         if cdf[k] <= 0.01f64 {
    //             panic!();
    //         }
    //         let val = (cdf[k] - reference_cdf[k]).abs();
    //         if val > max {
    //             max = val;
    //         }
    //     }
    //     if max > global_max {
    //         global_max = max;
    //     }
    // }
    // // this is max cdf difference for Kolmogorov-Smirnov for sample size 1000000
    // // and P = 0.99
    // let alpha = 0.0015f64;
    // assert!(global_max < alpha);
}