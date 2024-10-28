// Number of Machines: 2
// Number of constraints: 16
// r1cs matrix: Some(ConstraintMatrices { 
//     num_instance_variables: 1, num_witness_variables: 15, num_constraints: 16, a_num_non_zero: 16, b_num_non_zero: 16, c_num_non_zero: 16, 
//     a: [
//         [(BigInt([1, 0, 0, 0]), 1)], 
//         [(BigInt([1, 0, 0, 0]), 4)], 
//         [(BigInt([1, 0, 0, 0]), 7)],
//         [(BigInt([1, 0, 0, 0]), 10)], 
//         [(BigInt([1, 0, 0, 0]), 13)], 
//         [(BigInt([1, 0, 0, 0]), 14)], 
//         [(BigInt([3, 0, 0, 0]), 0)], 
//         [(BigInt([1, 0, 0, 0]), 14)], 
//         [(BigInt([3, 0, 0, 0]), 0)], 
//         [(BigInt([1, 0, 0, 0]), 14)], 
//         [(BigInt([3, 0, 0, 0]), 0)], 
//         [(BigInt([1, 0, 0, 0]), 14)], 
//         [(BigInt([3, 0, 0, 0]), 0)], 
//         [(BigInt([1, 0, 0, 0]), 14)], 
//         [(BigInt([3, 0, 0, 0]), 0)], 
//         [(BigInt([1, 0, 0, 0]), 0)]], 
        
//         b: [[(BigInt([1, 0, 0, 0]), 2)], [(BigInt([1, 0, 0, 0]), 5)], [(BigInt([1, 0, 0, 0]), 8)], [(BigInt([1, 0, 0, 0]), 11)], [(BigInt([1, 0, 0, 0]), 14)], [(BigInt([2, 0, 0, 0]), 0)], [(BigInt([1, 0, 0, 0]), 13)], [(BigInt([2, 0, 0, 0]), 0)], [(BigInt([1, 0, 0, 0]), 13)], [(BigInt([2, 0, 0, 0]), 0)], [(BigInt([1, 0, 0, 0]), 13)], [(BigInt([2, 0, 0, 0]), 0)], [(BigInt([1, 0, 0, 0]), 13)], [(BigInt([2, 0, 0, 0]), 0)], [(BigInt([1, 0, 0, 0]), 13)], [(BigInt([1, 0, 0, 0]), 14)]], c: [[(BigInt([1, 0, 0, 0]), 3)], [(BigInt([1, 0, 0, 0]), 6)], [(BigInt([1, 0, 0, 0]), 9)], [(BigInt([1, 0, 0, 0]), 12)], [(BigInt([1, 0, 0, 0]), 15)], [(BigInt([1, 0, 0, 0]), 15)], [(BigInt([1, 0, 0, 0]), 15)], [(BigInt([1, 0, 0, 0]), 15)], [(BigInt([1, 0, 0, 0]), 15)], [(BigInt([1, 0, 0, 0]), 15)], [(BigInt([1, 0, 0, 0]), 15)], [(BigInt([1, 0, 0, 0]), 15)], [(BigInt([1, 0, 0, 0]), 15)], [(BigInt([1, 0, 0, 0]), 15)], [(BigInt([1, 0, 0, 0]), 15)], [(BigInt([1, 0, 0, 0]), 14)]] })
// witness vector: [BigInt([1, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([3, 0, 0, 0]), BigInt([6, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([3, 0, 0, 0]), BigInt([6, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([3, 0, 0, 0]), BigInt([6, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([3, 0, 0, 0]), BigInt([6, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([3, 0, 0, 0]), BigInt([6, 0, 0, 0])]
// r1cs preprocessing row info: [DeRowIndex { 
//     row_pa_low: 
//     [0, 1, 2, 2, 0, 2, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0], 
//     row_pa_high: 
//     [0, 0, 0, 1, 2, 2, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0], 
//     row_pb_low: [0, 1, 1, 3, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], 
//     row_pb_high: [0, 0, 1, 1, 2, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0], 
//     row_pc_low: [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 
//     row_pc_high: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }, 
//     DeRowIndex { 
//         row_pa_low: 
//         [3, 0, 1, 3, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], 
//         row_pa_high: 
//         [0, 1, 1, 1, 2, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0], 
//         row_pb_low: [2, 3, 0, 2, 0, 2, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0], 
//         row_pb_high: [0, 0, 1, 1, 2, 2, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0], 
//         row_pc_low: [2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 0], 
//         row_pc_high: [0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 0, 0] }]
// r1cs preprocessing col info: [DeColIndex { 
//     col_pa: [1, 4, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 
//     col_pb: [2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], col_pc: [3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }, 
//     DeColIndex { 
//         col_pa: [2, 5, 6, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0], col_pb: [0, 3, 6, 5, 5, 5, 5, 5, 6, 0, 0, 0, 0, 0, 0, 0], col_pc: [1, 4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 0, 0] }]
// r1cs preprocessing val info: [DeValEvals { evals_val_pa: [BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([3, 0, 0, 0]), BigInt([3, 0, 0, 0]), BigInt([3, 0, 0, 0]), BigInt([3, 0, 0, 0]), BigInt([3, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0])], 
//     evals_val_pb: [BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0])], 
//     evals_val_pc: [BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0])] }, 
//     DeValEvals { 
//         evals_val_pa: [BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0])], evals_val_pb: [BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0])], evals_val_pc: [BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0])] }]
// r1cs preprocessing lookup info: NEvals { row_pa_low: 
//     [BigInt([20, 0, 0, 0]), 
//     BigInt([4, 0, 0, 0]), 
//     BigInt([4, 0, 0, 0]), 
//     BigInt([4, 0, 0, 0]), 
//     BigInt([0, 0, 0, 0]), 
//     BigInt([0, 0, 0, 0]), 
//     BigInt([0, 0, 0, 0]), 
//     BigInt([0, 0, 0, 0])], 
//     row_pa_high: 
//     [BigInt([20, 0, 0, 0]), 
//     BigInt([4, 0, 0, 0]), 
//     BigInt([4, 0, 0, 0]), 
//     BigInt([4, 0, 0, 0]), 
//     BigInt([0, 0, 0, 0]), 
//     BigInt([0, 0, 0, 0]),
//      BigInt([0, 0, 0, 0]), 
//      BigInt([0, 0, 0, 0])], row_pb_low: [BigInt([20, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0])], row_pb_high: [BigInt([20, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0])], row_pc_low: [BigInt([20, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0])], row_pc_high: [BigInt([20, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([4, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([0, 0, 0, 0])], col_pa: [BigInt([22, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([5, 0, 0, 0]), BigInt([1, 0, 0, 0])], col_pb: [BigInt([22, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([6, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([0, 0, 0, 0])], col_pc: [BigInt([16, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([1, 0, 0, 0]), BigInt([0, 0, 0, 0]), BigInt([2, 0, 0, 0]), BigInt([11, 0, 0, 0])] }