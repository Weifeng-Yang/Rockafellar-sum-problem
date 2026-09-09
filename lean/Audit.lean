import BlockMassFinite
import BlockMassEndpoint
import BlockMassCurve
import BlockMassTriangular
import BlockMassC0Dual
import BlockMassRankOne
import BlockMassKernel
import BlockMassKernelTests
import BlockMassGraphModel
import BlockMassParameterReturn
import BlockMassWorkBound
import BlockMassSumWitness
import BlockMassPolar
import BlockMassConcreteWitness
import BlockMassCounterexample
import BlockMassPullback

/-! Read-only declaration inspection. No mathematical declarations are added. -/
set_option pp.universes true

#check @BlockMassC0Dual.globalC0_iff_tendsto
#print axioms BlockMassC0Dual.globalC0_iff_tendsto
#check @BlockMassC0Dual.globalC0_iff_zeroAtInfty
#print axioms BlockMassC0Dual.globalC0_iff_zeroAtInfty
#check @BlockMassC0Dual.globalC0_coe
#print axioms BlockMassC0Dual.globalC0_coe
#check @BlockMassC0Dual.ofGlobal_apply
#print axioms BlockMassC0Dual.ofGlobal_apply
#check @BlockMassC0Dual.abs_apply_le_norm
#print axioms BlockMassC0Dual.abs_apply_le_norm
#check @BlockMassC0Dual.norm_le_of_abs_le
#print axioms BlockMassC0Dual.norm_le_of_abs_le
#check @BlockMassC0Dual.finite_support_globalC0
#print axioms BlockMassC0Dual.finite_support_globalC0
#check @BlockMassC0Dual.finiteVector_apply
#print axioms BlockMassC0Dual.finiteVector_apply
#check @BlockMassC0Dual.basis_apply
#print axioms BlockMassC0Dual.basis_apply
#check @BlockMassC0Dual.sum_apply
#print axioms BlockMassC0Dual.sum_apply
#check @BlockMassC0Dual.finiteVector_eq_sum
#print axioms BlockMassC0Dual.finiteVector_eq_sum
#check @BlockMassC0Dual.functional_finiteVector
#print axioms BlockMassC0Dual.functional_finiteVector
#check @BlockMassC0Dual.signTest_norm_le
#print axioms BlockMassC0Dual.signTest_norm_le
#check @BlockMassC0Dual.functional_signTest
#print axioms BlockMassC0Dual.functional_signTest
#check @BlockMassC0Dual.coordinates_finite_abs_sum_le
#print axioms BlockMassC0Dual.coordinates_finite_abs_sum_le
#check @BlockMassC0Dual.coordinates_absSummable
#print axioms BlockMassC0Dual.coordinates_absSummable
#check @BlockMassC0Dual.coordinates_tsum_abs_le
#print axioms BlockMassC0Dual.coordinates_tsum_abs_le
#check @BlockMassC0Dual.finiteVector_tendsto
#print axioms BlockMassC0Dual.finiteVector_tendsto
#check @BlockMassC0Dual.basis_hasSum
#print axioms BlockMassC0Dual.basis_hasSum
#check @BlockMassC0Dual.functional_eq_tsum
#print axioms BlockMassC0Dual.functional_eq_tsum
#check @BlockMassC0Dual.pairing_summable
#print axioms BlockMassC0Dual.pairing_summable
#check @BlockMassC0Dual.pairing_absSummable
#print axioms BlockMassC0Dual.pairing_absSummable
#check @BlockMassC0Dual.pairing_bound
#print axioms BlockMassC0Dual.pairing_bound
#check @BlockMassC0Dual.ofAbsSummable_apply
#print axioms BlockMassC0Dual.ofAbsSummable_apply
#check @BlockMassC0Dual.coordinates_ofAbsSummable
#print axioms BlockMassC0Dual.coordinates_ofAbsSummable
#check @BlockMassC0Dual.ofAbsSummable_coordinates
#print axioms BlockMassC0Dual.ofAbsSummable_coordinates
#check @BlockMassC0Dual.ofAbsSummable_norm_le
#print axioms BlockMassC0Dual.ofAbsSummable_norm_le
#check @BlockMassC0Dual.functional_norm_eq
#print axioms BlockMassC0Dual.functional_norm_eq
#check @BlockMassC0Dual.ofAbsSummable_norm_eq
#print axioms BlockMassC0Dual.ofAbsSummable_norm_eq
#check @BlockMassC0Dual.full_dual_representation
#print axioms BlockMassC0Dual.full_dual_representation
#check @BlockMassC0Dual.norm_eq_iSup_abs
#print axioms BlockMassC0Dual.norm_eq_iSup_abs
#check @BlockMassConcreteWitness.graphA_row_data
#print axioms BlockMassConcreteWitness.graphA_row_data
#check @BlockMassConcreteWitness.actual_ne_zero
#print axioms BlockMassConcreteWitness.actual_ne_zero
#check @BlockMassConcreteWitness.graphA_primal_ne_zero
#print axioms BlockMassConcreteWitness.graphA_primal_ne_zero
#check @BlockMassConcreteWitness.graphA_zero_row_missing
#print axioms BlockMassConcreteWitness.graphA_zero_row_missing
#check @BlockMassConcreteWitness.graphA_zero_fibre_empty
#print axioms BlockMassConcreteWitness.graphA_zero_fibre_empty
#check @BlockMassConcreteWitness.graphA_zero_not_domain
#print axioms BlockMassConcreteWitness.graphA_zero_not_domain
#check @BlockMassConcreteWitness.actual_sign_sq
#print axioms BlockMassConcreteWitness.actual_sign_sq
#check @BlockMassConcreteWitness.wholeF_square_sum
#print axioms BlockMassConcreteWitness.wholeF_square_sum
#check @BlockMassConcreteWitness.actual_mass_square_sum
#print axioms BlockMassConcreteWitness.actual_mass_square_sum
#check @BlockMassConcreteWitness.actual_label_work_identity
#print axioms BlockMassConcreteWitness.actual_label_work_identity
#check @BlockMassConcreteWitness.actual_row_work_identity
#print axioms BlockMassConcreteWitness.actual_row_work_identity
#check @BlockMassConcreteWitness.actual_row_work_gt_seven_eighths
#print axioms BlockMassConcreteWitness.actual_row_work_gt_seven_eighths
#check @BlockMassConcreteWitness.actual_row_work_nonneg
#print axioms BlockMassConcreteWitness.actual_row_work_nonneg
#check @BlockMassConcreteWitness.actualSum_monotone
#print axioms BlockMassConcreteWitness.actualSum_monotone
#check @BlockMassConcreteWitness.actualSum_self_work_gt_seven_eighths
#print axioms BlockMassConcreteWitness.actualSum_self_work_gt_seven_eighths
#check @BlockMassConcreteWitness.actualSum_zero_polar
#print axioms BlockMassConcreteWitness.actualSum_zero_polar
#check @BlockMassConcreteWitness.actualSum_zero_nongraph
#print axioms BlockMassConcreteWitness.actualSum_zero_nongraph
#check @BlockMassConcreteWitness.actual_rankOne_domain
#print axioms BlockMassConcreteWitness.actual_rankOne_domain
#check @BlockMassConcreteWitness.actual_ordered_CQ
#print axioms BlockMassConcreteWitness.actual_ordered_CQ
#check @BlockMassConcreteWitness.actualSum_not_maximal
#print axioms BlockMassConcreteWitness.actualSum_not_maximal
#check @BlockMassConcreteWitness.actualSum_insert_zero_monotone
#print axioms BlockMassConcreteWitness.actualSum_insert_zero_monotone
#check @BlockMassConcreteWitness.actualSum_insert_zero_strict
#print axioms BlockMassConcreteWitness.actualSum_insert_zero_strict
#check @BlockMassConcreteWitness.g_basis00
#print axioms BlockMassConcreteWitness.g_basis00
#check @BlockMassConcreteWitness.g_ne_zero
#print axioms BlockMassConcreteWitness.g_ne_zero
#check @BlockMassConcreteWitness.rankOne_basis00
#print axioms BlockMassConcreteWitness.rankOne_basis00
#check @BlockMassConcreteWitness.actual_rankOne_ne_zero
#print axioms BlockMassConcreteWitness.actual_rankOne_ne_zero
#check @BlockMassConcreteWitness.actual_rankOne_range
#print axioms BlockMassConcreteWitness.actual_rankOne_range
#check @BlockMassConcreteWitness.actual_rankOne_positive
#print axioms BlockMassConcreteWitness.actual_rankOne_positive
#check @BlockMassConcreteWitness.actual_rankOne_maximal
#print axioms BlockMassConcreteWitness.actual_rankOne_maximal
#check @BlockMassConcreteWitness.conditional_certificate
#print axioms BlockMassConcreteWitness.conditional_certificate
#check @BlockMassCounterexample.exact_counterexample
#print axioms BlockMassCounterexample.exact_counterexample
#check @BlockMassCounterexample.operatorGraph_A
#print axioms BlockMassCounterexample.operatorGraph_A
#check @BlockMassCounterexample.operatorGraph_B
#print axioms BlockMassCounterexample.operatorGraph_B
#check @BlockMassCounterexample.operator_sum_graph
#print axioms BlockMassCounterexample.operator_sum_graph
#check @BlockMassCounterexample.exact_operator_counterexample
#print axioms BlockMassCounterexample.exact_operator_counterexample
#check @BlockMassCounterexample.not_universal_sum_claim
#print axioms BlockMassCounterexample.not_universal_sum_claim
#check @BlockMassCurve.coeff_pos
#print axioms BlockMassCurve.coeff_pos
#check @BlockMassCurve.coeff_fourth
#print axioms BlockMassCurve.coeff_fourth
#check @BlockMassCurve.omega_nonneg
#print axioms BlockMassCurve.omega_nonneg
#check @BlockMassCurve.omega_le_harmonic
#print axioms BlockMassCurve.omega_le_harmonic
#check @BlockMassCurve.omega_zero_of_threshold
#print axioms BlockMassCurve.omega_zero_of_threshold
#check @BlockMassCurve.omega_zero_above
#print axioms BlockMassCurve.omega_zero_above
#check @BlockMassCurve.finite_support_of_zero_above
#print axioms BlockMassCurve.finite_support_of_zero_above
#check @BlockMassCurve.omega_finite_support
#print axioms BlockMassCurve.omega_finite_support
#check @BlockMassCurve.omega_summable
#print axioms BlockMassCurve.omega_summable
#check @BlockMassCurve.omega_sq_summable
#print axioms BlockMassCurve.omega_sq_summable
#check @BlockMassCurve.omega_sq_diff_summable
#print axioms BlockMassCurve.omega_sq_diff_summable
#check @BlockMassCurve.square_summable_of_summable
#print axioms BlockMassCurve.square_summable_of_summable
#check @BlockMassCurve.omega_error_sq_summable
#print axioms BlockMassCurve.omega_error_sq_summable
#check @BlockMassCurve.omega_tendsto
#print axioms BlockMassCurve.omega_tendsto
#check @BlockMassCurve.slope_nonneg
#print axioms BlockMassCurve.slope_nonneg
#check @BlockMassCurve.omega_coordinate_lipschitz
#print axioms BlockMassCurve.omega_coordinate_lipschitz
#check @BlockMassCurve.omega_coordinate_sq_bound
#print axioms BlockMassCurve.omega_coordinate_sq_bound
#check @BlockMassCurve.weight_eq_rpow
#print axioms BlockMassCurve.weight_eq_rpow
#check @BlockMassCurve.weight_summable
#print axioms BlockMassCurve.weight_summable
#check @BlockMassCurve.rpow_sum_le_four
#print axioms BlockMassCurve.rpow_sum_le_four
#check @BlockMassCurve.curveConstant_eq
#print axioms BlockMassCurve.curveConstant_eq
#check @BlockMassCurve.curveConstant_nonneg
#print axioms BlockMassCurve.curveConstant_nonneg
#check @BlockMassCurve.curveConstant_le_quarter
#print axioms BlockMassCurve.curveConstant_le_quarter
#check @BlockMassCurve.omega_sq_lipschitz
#print axioms BlockMassCurve.omega_sq_lipschitz
#check @BlockMassCurve.actual_gap_pos
#print axioms BlockMassCurve.actual_gap_pos
#check @BlockMassCurve.wholeF_finite_support
#print axioms BlockMassCurve.wholeF_finite_support
#check @BlockMassCurve.wholeF_summable
#print axioms BlockMassCurve.wholeF_summable
#check @BlockMassCurve.wholeF_sq_summable
#print axioms BlockMassCurve.wholeF_sq_summable
#check @BlockMassCurve.wholeF_sq_diff_summable
#print axioms BlockMassCurve.wholeF_sq_diff_summable
#check @BlockMassCurve.sign_abs_gap_bound
#print axioms BlockMassCurve.sign_abs_gap_bound
#check @BlockMassCurve.wholeF_sq_lipschitz
#print axioms BlockMassCurve.wholeF_sq_lipschitz
#check @BlockMassCurve.wholeF_lipschitz_distance
#print axioms BlockMassCurve.wholeF_lipschitz_distance
#check @BlockMassEndpoint.harmonicQuarter_pos
#print axioms BlockMassEndpoint.harmonicQuarter_pos
#check @BlockMassEndpoint.harmonicQuarter_block_lower
#print axioms BlockMassEndpoint.harmonicQuarter_block_lower
#check @BlockMassEndpoint.not_summable_harmonicQuarter
#print axioms BlockMassEndpoint.not_summable_harmonicQuarter
#check @BlockMassEndpoint.coordinates_eq_of_all_endpoint_bounds
#print axioms BlockMassEndpoint.coordinates_eq_of_all_endpoint_bounds
#check @BlockMassEndpoint.no_summable_endpoint
#print axioms BlockMassEndpoint.no_summable_endpoint
#check @BlockMassEndpoint.no_summable_endpoint_positiveN
#print axioms BlockMassEndpoint.no_summable_endpoint_positiveN
#check @BlockMassEndpoint.no_absolutely_summable_endpoint
#print axioms BlockMassEndpoint.no_absolutely_summable_endpoint
#check @BlockMassEndpoint.summable_tail
#print axioms BlockMassEndpoint.summable_tail
#check @BlockMassEndpoint.endpoint_bounds_of_actual_rows
#print axioms BlockMassEndpoint.endpoint_bounds_of_actual_rows
#check @BlockMassEndpoint.cutoff_tendsto
#print axioms BlockMassEndpoint.cutoff_tendsto
#check @BlockMassEndpoint.no_summable_actual_cutoff_rows
#print axioms BlockMassEndpoint.no_summable_actual_cutoff_rows
#check @BlockMassEndpoint.finite_sq_bound_of_tsum
#print axioms BlockMassEndpoint.finite_sq_bound_of_tsum
#check @BlockMassEndpoint.no_summable_mass_cutoff_tsum_rows
#print axioms BlockMassEndpoint.no_summable_mass_cutoff_tsum_rows
#check @BlockMassEndpoint.tau_outside_of_summable_mass_rows
#print axioms BlockMassEndpoint.tau_outside_of_summable_mass_rows
#check @BlockMassFinite.c5_square_completion
#print axioms BlockMassFinite.c5_square_completion
#check @BlockMassFinite.finite_sq_distance
#print axioms BlockMassFinite.finite_sq_distance
#check @BlockMassFinite.c5_finite_square_completion
#print axioms BlockMassFinite.c5_finite_square_completion
#check @BlockMassFinite.c8_weighted_endpoint_identity
#print axioms BlockMassFinite.c8_weighted_endpoint_identity
#check @BlockMassFinite.c8_of_endpoint_bounds
#print axioms BlockMassFinite.c8_of_endpoint_bounds
#check @BlockMassFinite.c8_finite_endpoint_cancellation
#print axioms BlockMassFinite.c8_finite_endpoint_cancellation
#check @BlockMassGraphModel.coords_absSummable
#print axioms BlockMassGraphModel.coords_absSummable
#check @BlockMassGraphModel.coords_injective
#print axioms BlockMassGraphModel.coords_injective
#check @BlockMassGraphModel.coords_add
#print axioms BlockMassGraphModel.coords_add
#check @BlockMassGraphModel.coords_sub
#print axioms BlockMassGraphModel.coords_sub
#check @BlockMassGraphModel.coords_neg
#print axioms BlockMassGraphModel.coords_neg
#check @BlockMassGraphModel.coords_smul
#print axioms BlockMassGraphModel.coords_smul
#check @BlockMassGraphModel.coords_zero
#print axioms BlockMassGraphModel.coords_zero
#check @BlockMassGraphModel.E_apply
#print axioms BlockMassGraphModel.E_apply
#check @BlockMassGraphModel.mass_absSummable
#print axioms BlockMassGraphModel.mass_absSummable
#check @BlockMassGraphModel.mass_add
#print axioms BlockMassGraphModel.mass_add
#check @BlockMassGraphModel.mass_smul
#print axioms BlockMassGraphModel.mass_smul
#check @BlockMassGraphModel.mass_neg
#print axioms BlockMassGraphModel.mass_neg
#check @BlockMassGraphModel.mass_sub
#print axioms BlockMassGraphModel.mass_sub
#check @BlockMassGraphModel.mass_zero
#print axioms BlockMassGraphModel.mass_zero
#check @BlockMassGraphModel.r_add
#print axioms BlockMassGraphModel.r_add
#check @BlockMassGraphModel.r_sub
#print axioms BlockMassGraphModel.r_sub
#check @BlockMassGraphModel.r_smul
#print axioms BlockMassGraphModel.r_smul
#check @BlockMassGraphModel.r_zero
#print axioms BlockMassGraphModel.r_zero
#check @BlockMassGraphModel.E_add
#print axioms BlockMassGraphModel.E_add
#check @BlockMassGraphModel.E_smul
#print axioms BlockMassGraphModel.E_smul
#check @BlockMassGraphModel.E_neg
#print axioms BlockMassGraphModel.E_neg
#check @BlockMassGraphModel.E_sub
#print axioms BlockMassGraphModel.E_sub
#check @BlockMassGraphModel.L_sub
#print axioms BlockMassGraphModel.L_sub
#check @BlockMassGraphModel.apply_h
#print axioms BlockMassGraphModel.apply_h
#check @BlockMassGraphModel.E_pairing
#print axioms BlockMassGraphModel.E_pairing
#check @BlockMassGraphModel.E_symmetric_work
#print axioms BlockMassGraphModel.E_symmetric_work
#check @BlockMassGraphModel.mass_square_summable
#print axioms BlockMassGraphModel.mass_square_summable
#check @BlockMassGraphModel.E_quadratic_work
#print axioms BlockMassGraphModel.E_quadratic_work
#check @BlockMassGraphModel.L_work
#print axioms BlockMassGraphModel.L_work
#check @BlockMassGraphModel.L_difference_work
#print axioms BlockMassGraphModel.L_difference_work
#check @BlockMassGraphModel.mass_difference_square_summable
#print axioms BlockMassGraphModel.mass_difference_square_summable
#check @BlockMassGraphModel.delta_absSummable
#print axioms BlockMassGraphModel.delta_absSummable
#check @BlockMassGraphModel.coords_unitDual
#print axioms BlockMassGraphModel.coords_unitDual
#check @BlockMassGraphModel.unitDual_apply
#print axioms BlockMassGraphModel.unitDual_apply
#check @BlockMassGraphModel.g_apply
#print axioms BlockMassGraphModel.g_apply
#check @BlockMassGraphModel.E_unitDual
#print axioms BlockMassGraphModel.E_unitDual
#check @BlockMassGraphModel.E_g
#print axioms BlockMassGraphModel.E_g
#check @BlockMassGraphModel.r_g
#print axioms BlockMassGraphModel.r_g
#check @BlockMassGraphModel.mass_unitDual
#print axioms BlockMassGraphModel.mass_unitDual
#check @BlockMassGraphModel.mass_g
#print axioms BlockMassGraphModel.mass_g
#check @BlockMassGraphModel.g_E
#print axioms BlockMassGraphModel.g_E
#check @BlockMassGraphModel.g_L
#print axioms BlockMassGraphModel.g_L
#check @BlockMassGraphModel.coordinate_difference_work
#print axioms BlockMassGraphModel.coordinate_difference_work
#check @BlockMassGraphModel.graphA_monotone
#print axioms BlockMassGraphModel.graphA_monotone
#check @BlockMassGraphModel.mem_graphA_iff_coordinates
#print axioms BlockMassGraphModel.mem_graphA_iff_coordinates
#check @BlockMassGraphModel.liftCoeff_finite_support
#print axioms BlockMassGraphModel.liftCoeff_finite_support
#check @BlockMassGraphModel.mass_liftCoeff
#print axioms BlockMassGraphModel.mass_liftCoeff
#check @BlockMassGraphModel.sectionCoords_formula
#print axioms BlockMassGraphModel.sectionCoords_formula
#check @BlockMassGraphModel.sectionCoords_finite_support
#print axioms BlockMassGraphModel.sectionCoords_finite_support
#check @BlockMassGraphModel.sectionCoords_absSummable
#print axioms BlockMassGraphModel.sectionCoords_absSummable
#check @BlockMassGraphModel.coords_sectionLabel
#print axioms BlockMassGraphModel.coords_sectionLabel
#check @BlockMassGraphModel.r_sectionLabel
#print axioms BlockMassGraphModel.r_sectionLabel
#check @BlockMassGraphModel.sectionLabel_decomposition
#print axioms BlockMassGraphModel.sectionLabel_decomposition
#check @BlockMassGraphModel.mass_sectionLabel
#print axioms BlockMassGraphModel.mass_sectionLabel
#check @BlockMassGraphModel.sectionLabel_mem_D
#print axioms BlockMassGraphModel.sectionLabel_mem_D
#check @BlockMassGraphModel.D_nonempty
#print axioms BlockMassGraphModel.D_nonempty
#check @BlockMassGraphModel.graphA_nonempty
#print axioms BlockMassGraphModel.graphA_nonempty
#check @BlockMassGraphModel.mem_fibre_iff
#print axioms BlockMassGraphModel.mem_fibre_iff
#check @BlockMassGraphModel.fibre_eq_translate
#print axioms BlockMassGraphModel.fibre_eq_translate
#check @BlockMassGraphModel.D_fibre_eq_translate
#print axioms BlockMassGraphModel.D_fibre_eq_translate
#check @BlockMassGraphModel.L_symmetric_work
#print axioms BlockMassGraphModel.L_symmetric_work
#check @BlockMassGraphModel.L_pairing_absSummable
#print axioms BlockMassGraphModel.L_pairing_absSummable
#check @BlockMassGraphModel.L_difference_pairing
#print axioms BlockMassGraphModel.L_difference_pairing
#check @BlockMassKernel.globalC0_iff_finite_superlevels
#print axioms BlockMassKernel.globalC0_iff_finite_superlevels
#check @BlockMassKernel.constant_injective_slice_eq_zero
#print axioms BlockMassKernel.constant_injective_slice_eq_zero
#check @BlockMassKernel.nonzero_block_vanishes
#print axioms BlockMassKernel.nonzero_block_vanishes
#check @BlockMassKernel.zero_block_tail_vanishes
#print axioms BlockMassKernel.zero_block_tail_vanishes
#check @BlockMassKernel.difference_tests_force_head_span
#print axioms BlockMassKernel.difference_tests_force_head_span
#check @BlockMassKernelTests.pointMass_finite_support
#print axioms BlockMassKernelTests.pointMass_finite_support
#check @BlockMassKernelTests.pointMass_absSummable
#print axioms BlockMassKernelTests.pointMass_absSummable
#check @BlockMassKernelTests.difference_finite_support
#print axioms BlockMassKernelTests.difference_finite_support
#check @BlockMassKernelTests.difference_absSummable
#print axioms BlockMassKernelTests.difference_absSummable
#check @BlockMassKernelTests.pointMass_pairing_summable
#print axioms BlockMassKernelTests.pointMass_pairing_summable
#check @BlockMassKernelTests.pairing_pointMass
#print axioms BlockMassKernelTests.pairing_pointMass
#check @BlockMassKernelTests.pairing_difference
#print axioms BlockMassKernelTests.pairing_difference
#check @BlockMassKernelTests.m_pointMass
#print axioms BlockMassKernelTests.m_pointMass
#check @BlockMassKernelTests.m_difference
#print axioms BlockMassKernelTests.m_difference
#check @BlockMassKernelTests.m_sameBlock_difference
#print axioms BlockMassKernelTests.m_sameBlock_difference
#check @BlockMassKernelTests.nonzeroBlock_difference_mem_K
#print axioms BlockMassKernelTests.nonzeroBlock_difference_mem_K
#check @BlockMassKernelTests.zeroBlock_tail_difference_mem_K
#print axioms BlockMassKernelTests.zeroBlock_tail_difference_mem_K
#check @BlockMassKernelTests.head_difference_mem_K
#print axioms BlockMassKernelTests.head_difference_mem_K
#check @BlockMassKernelTests.annihilatesK_differenceTests
#print axioms BlockMassKernelTests.annihilatesK_differenceTests
#check @BlockMassKernelTests.globalC0_iff_kernel_globalC0
#print axioms BlockMassKernelTests.globalC0_iff_kernel_globalC0
#check @BlockMassKernelTests.K_pairing_absSummable
#print axioms BlockMassKernelTests.K_pairing_absSummable
#check @BlockMassKernelTests.annihilatesK_force_head_span
#print axioms BlockMassKernelTests.annihilatesK_force_head_span
#check @BlockMassKernelTests.headProfile_eq_pointMass
#print axioms BlockMassKernelTests.headProfile_eq_pointMass
#check @BlockMassKernelTests.headProfile_finite_support
#print axioms BlockMassKernelTests.headProfile_finite_support
#check @BlockMassKernelTests.pairing_headProfile
#print axioms BlockMassKernelTests.pairing_headProfile
#check @BlockMassKernelTests.pairing_head_multiple
#print axioms BlockMassKernelTests.pairing_head_multiple
#check @BlockMassKernelTests.head_multiple_globalC0
#print axioms BlockMassKernelTests.head_multiple_globalC0
#check @BlockMassKernelTests.head_multiple_annihilatesK
#print axioms BlockMassKernelTests.head_multiple_annihilatesK
#check @BlockMassKernelTests.globalC0_annihilator_iff_head_span
#print axioms BlockMassKernelTests.globalC0_annihilator_iff_head_span
#check @BlockMassParameterReturn.error_sq_summable
#print axioms BlockMassParameterReturn.error_sq_summable
#check @BlockMassParameterReturn.positive_row_bound
#print axioms BlockMassParameterReturn.positive_row_bound
#check @BlockMassParameterReturn.negative_row_bound
#print axioms BlockMassParameterReturn.negative_row_bound
#check @BlockMassParameterReturn.tau_actual
#print axioms BlockMassParameterReturn.tau_actual
#check @BlockMassParameterReturn.parameter_return
#print axioms BlockMassParameterReturn.parameter_return
#check @BlockMassParameterReturn.actual_parameters_satisfy_rows
#print axioms BlockMassParameterReturn.actual_parameters_satisfy_rows
#check @BlockMassParameterReturn.actual_row_bounds_iff
#print axioms BlockMassParameterReturn.actual_row_bounds_iff
#check @BlockMassPolar.coords_K_iff
#print axioms BlockMassPolar.coords_K_iff
#check @BlockMassPolar.of_coords_mem_K
#print axioms BlockMassPolar.of_coords_mem_K
#check @BlockMassPolar.h_apply_profile
#print axioms BlockMassPolar.h_apply_profile
#check @BlockMassPolar.annihilator_full_dual
#print axioms BlockMassPolar.annihilator_full_dual
#check @BlockMassPolar.K_smul
#print axioms BlockMassPolar.K_smul
#check @BlockMassPolar.D_add_K
#print axioms BlockMassPolar.D_add_K
#check @BlockMassPolar.L_add
#print axioms BlockMassPolar.L_add
#check @BlockMassPolar.L_smul
#print axioms BlockMassPolar.L_smul
#check @BlockMassPolar.L_kernel_pair
#print axioms BlockMassPolar.L_kernel_pair
#check @BlockMassPolar.K_self_work
#print axioms BlockMassPolar.K_self_work
#check @BlockMassPolar.actual_kernel_line_bracket
#print axioms BlockMassPolar.actual_kernel_line_bracket
#check @BlockMassPolar.affine_coefficient_zero
#print axioms BlockMassPolar.affine_coefficient_zero
#check @BlockMassPolar.polar_annihilates_kernel
#print axioms BlockMassPolar.polar_annihilates_kernel
#check @BlockMassPolar.polar_point_representation
#print axioms BlockMassPolar.polar_point_representation
#check @BlockMassPolar.represented_bracket
#print axioms BlockMassPolar.represented_bracket
#check @BlockMassPolar.polar_actual_row_bounds
#print axioms BlockMassPolar.polar_actual_row_bounds
#check @BlockMassPolar.every_polar_point_in_graph
#print axioms BlockMassPolar.every_polar_point_in_graph
#check @BlockMassPolar.graphA_polar_eq
#print axioms BlockMassPolar.graphA_polar_eq
#check @BlockMassPolar.graphA_maximally_monotone
#print axioms BlockMassPolar.graphA_maximally_monotone
#check @BlockMassPullback.gap_self
#print axioms BlockMassPullback.gap_self
#check @BlockMassPullback.gap_comm
#print axioms BlockMassPullback.gap_comm
#check @BlockMassPullback.monotone_iff_subset_polar
#print axioms BlockMassPullback.monotone_iff_subset_polar
#check @BlockMassPullback.monotone_insert_iff
#print axioms BlockMassPullback.monotone_insert_iff
#check @BlockMassPullback.maximal_iff_monotone_polar_subset
#print axioms BlockMassPullback.maximal_iff_monotone_polar_subset
#check @BlockMassPullback.maximal_iff_eq_polar
#print axioms BlockMassPullback.maximal_iff_eq_polar
#check @BlockMassPullback.dualMap_apply
#print axioms BlockMassPullback.dualMap_apply
#check @BlockMassPullback.mem_pullback_iff
#print axioms BlockMassPullback.mem_pullback_iff
#check @BlockMassPullback.gap_pullback
#print axioms BlockMassPullback.gap_pullback
#check @BlockMassPullback.monotone_pullback
#print axioms BlockMassPullback.monotone_pullback
#check @BlockMassPullback.pullback_nonempty
#print axioms BlockMassPullback.pullback_nonempty
#check @BlockMassPullback.kernel_line_mem
#print axioms BlockMassPullback.kernel_line_mem
#check @BlockMassPullback.polar_annihilates_kernel
#print axioms BlockMassPullback.polar_annihilates_kernel
#check @BlockMassPullback.exists_dual_factor_of_norm_lift
#print axioms BlockMassPullback.exists_dual_factor_of_norm_lift
#check @BlockMassPullback.exists_dual_factor
#print axioms BlockMassPullback.exists_dual_factor
#check @BlockMassPullback.polar_descends
#print axioms BlockMassPullback.polar_descends
#check @BlockMassPullback.polar_pullback_subset
#print axioms BlockMassPullback.polar_pullback_subset
#check @BlockMassPullback.maximalMonotone_pullback
#print axioms BlockMassPullback.maximalMonotone_pullback
#check @BlockMassRankOne.bracket_self
#print axioms BlockMassRankOne.bracket_self
#check @BlockMassRankOne.bracket_symm
#print axioms BlockMassRankOne.bracket_symm
#check @BlockMassRankOne.graphMonotone_iff_subset_polar
#print axioms BlockMassRankOne.graphMonotone_iff_subset_polar
#check @BlockMassRankOne.graphMonotone_insert_iff
#print axioms BlockMassRankOne.graphMonotone_insert_iff
#check @BlockMassRankOne.maximallyMonotone_iff_polar_eq
#print axioms BlockMassRankOne.maximallyMonotone_iff_polar_eq
#check @BlockMassRankOne.rankOne_apply
#print axioms BlockMassRankOne.rankOne_apply
#check @BlockMassRankOne.rankOne_apply_apply
#print axioms BlockMassRankOne.rankOne_apply_apply
#check @BlockMassRankOne.rankOne_continuous
#print axioms BlockMassRankOne.rankOne_continuous
#check @BlockMassRankOne.rankOne_add
#print axioms BlockMassRankOne.rankOne_add
#check @BlockMassRankOne.rankOne_smul
#print axioms BlockMassRankOne.rankOne_smul
#check @BlockMassRankOne.rankOne_norm_le
#print axioms BlockMassRankOne.rankOne_norm_le
#check @BlockMassRankOne.rankOne_opNorm_le
#print axioms BlockMassRankOne.rankOne_opNorm_le
#check @BlockMassRankOne.mem_rankOneGraph
#print axioms BlockMassRankOne.mem_rankOneGraph
#check @BlockMassRankOne.rankOne_full_domain
#print axioms BlockMassRankOne.rankOne_full_domain
#check @BlockMassRankOne.rankOne_pairing_sub
#print axioms BlockMassRankOne.rankOne_pairing_sub
#check @BlockMassRankOne.rankOne_graph_monotone
#print axioms BlockMassRankOne.rankOne_graph_monotone
#check @BlockMassRankOne.linear_coefficient_eq_zero
#print axioms BlockMassRankOne.linear_coefficient_eq_zero
#check @BlockMassRankOne.rankOne_line_bracket
#print axioms BlockMassRankOne.rankOne_line_bracket
#check @BlockMassRankOne.polar_difference_apply_eq_zero
#print axioms BlockMassRankOne.polar_difference_apply_eq_zero
#check @BlockMassRankOne.polar_difference_eq_zero
#print axioms BlockMassRankOne.polar_difference_eq_zero
#check @BlockMassRankOne.rankOne_polar_mem_iff
#print axioms BlockMassRankOne.rankOne_polar_mem_iff
#check @BlockMassRankOne.rankOne_polar_eq
#print axioms BlockMassRankOne.rankOne_polar_eq
#check @BlockMassRankOne.rankOne_maximally_monotone
#print axioms BlockMassRankOne.rankOne_maximally_monotone
#check @BlockMassRankOne.rankOne_no_proper_monotone_extension
#print axioms BlockMassRankOne.rankOne_no_proper_monotone_extension
#check @BlockMassSumWitness.graphSum_monotone
#print axioms BlockMassSumWitness.graphSum_monotone
#check @BlockMassSumWitness.rankOne_domain
#print axioms BlockMassSumWitness.rankOne_domain
#check @BlockMassSumWitness.rankOne_ordered_CQ
#print axioms BlockMassSumWitness.rankOne_ordered_CQ
#check @BlockMassSumWitness.zero_polar_of_self_work
#print axioms BlockMassSumWitness.zero_polar_of_self_work
#check @BlockMassSumWitness.rankOne_sum_self_work
#print axioms BlockMassSumWitness.rankOne_sum_self_work
#check @BlockMassSumWitness.zero_missing_from_sum
#print axioms BlockMassSumWitness.zero_missing_from_sum
#check @BlockMassSumWitness.nonmaximal_of_polar_nongraph
#print axioms BlockMassSumWitness.nonmaximal_of_polar_nongraph
#check @BlockMassSumWitness.rankOne_sum_certificate
#print axioms BlockMassSumWitness.rankOne_sum_certificate
#check @BlockMassTriangular.absSummable_iff_summable
#print axioms BlockMassTriangular.absSummable_iff_summable
#check @BlockMassTriangular.absSummable_iff_summable_norm
#print axioms BlockMassTriangular.absSummable_iff_summable_norm
#check @BlockMassTriangular.globalC0_iff_tendsto
#print axioms BlockMassTriangular.globalC0_iff_tendsto
#check @BlockMassTriangular.summable_globalC0
#print axioms BlockMassTriangular.summable_globalC0
#check @BlockMassTriangular.tail_summable
#print axioms BlockMassTriangular.tail_summable
#check @BlockMassTriangular.tail_eq_shift
#print axioms BlockMassTriangular.tail_eq_shift
#check @BlockMassTriangular.tail_tendsto_zero
#print axioms BlockMassTriangular.tail_tendsto_zero
#check @BlockMassTriangular.E_tendsto_zero
#print axioms BlockMassTriangular.E_tendsto_zero
#check @BlockMassTriangular.E_globalC0
#print axioms BlockMassTriangular.E_globalC0
#check @BlockMassTriangular.weight_nonneg
#print axioms BlockMassTriangular.weight_nonneg
#check @BlockMassTriangular.weight_le_two
#print axioms BlockMassTriangular.weight_le_two
#check @BlockMassTriangular.weight_symmetric
#print axioms BlockMassTriangular.weight_symmetric
#check @BlockMassTriangular.weight_summable
#print axioms BlockMassTriangular.weight_summable
#check @BlockMassTriangular.E_eq_kernel
#print axioms BlockMassTriangular.E_eq_kernel
#check @BlockMassTriangular.E_abs_le
#print axioms BlockMassTriangular.E_abs_le
#check @BlockMassTriangular.pairing_absSummable_of_bound
#print axioms BlockMassTriangular.pairing_absSummable_of_bound
#check @BlockMassTriangular.globalC0_bounded
#print axioms BlockMassTriangular.globalC0_bounded
#check @BlockMassTriangular.c0_pairing_absSummable
#print axioms BlockMassTriangular.c0_pairing_absSummable
#check @BlockMassTriangular.E_pairing_absSummable
#print axioms BlockMassTriangular.E_pairing_absSummable
#check @BlockMassTriangular.kernelProduct_absSummable
#print axioms BlockMassTriangular.kernelProduct_absSummable
#check @BlockMassTriangular.pairing_E_eq_double
#print axioms BlockMassTriangular.pairing_E_eq_double
#check @BlockMassTriangular.E_symmetric_identity
#print axioms BlockMassTriangular.E_symmetric_identity
#check @BlockMassTriangular.E_quadratic_identity
#print axioms BlockMassTriangular.E_quadratic_identity
#check @BlockMassTriangular.sourceIndexEquiv_apply
#print axioms BlockMassTriangular.sourceIndexEquiv_apply
#check @BlockMassTriangular.block_absSummable
#print axioms BlockMassTriangular.block_absSummable
#check @BlockMassTriangular.blockSize_summable
#print axioms BlockMassTriangular.blockSize_summable
#check @BlockMassTriangular.blockSize_nonneg
#print axioms BlockMassTriangular.blockSize_nonneg
#check @BlockMassTriangular.blockSize_total
#print axioms BlockMassTriangular.blockSize_total
#check @BlockMassTriangular.m_abs_le_blockSize
#print axioms BlockMassTriangular.m_abs_le_blockSize
#check @BlockMassTriangular.m_absSummable
#print axioms BlockMassTriangular.m_absSummable
#check @BlockMassTriangular.m_l1Size_le
#print axioms BlockMassTriangular.m_l1Size_le
#check @BlockMassTriangular.blockE_abs_le_blockSize
#print axioms BlockMassTriangular.blockE_abs_le_blockSize
#check @BlockMassTriangular.blockE_abs_le
#print axioms BlockMassTriangular.blockE_abs_le
#check @BlockMassTriangular.blockE_globalC0
#print axioms BlockMassTriangular.blockE_globalC0
#check @BlockMassTriangular.blockE_pairing_absSummable
#print axioms BlockMassTriangular.blockE_pairing_absSummable
#check @BlockMassTriangular.massProduct_absSummable
#print axioms BlockMassTriangular.massProduct_absSummable
#check @BlockMassTriangular.blockE_pairing_eq_iterated
#print axioms BlockMassTriangular.blockE_pairing_eq_iterated
#check @BlockMassTriangular.blockE_symmetric_identity
#print axioms BlockMassTriangular.blockE_symmetric_identity
#check @BlockMassTriangular.m_square_summable
#print axioms BlockMassTriangular.m_square_summable
#check @BlockMassTriangular.blockE_quadratic_identity
#print axioms BlockMassTriangular.blockE_quadratic_identity
#check @BlockMassTriangular.E_add
#print axioms BlockMassTriangular.E_add
#check @BlockMassTriangular.E_smul
#print axioms BlockMassTriangular.E_smul
#check @BlockMassTriangular.m_add
#print axioms BlockMassTriangular.m_add
#check @BlockMassTriangular.m_smul
#print axioms BlockMassTriangular.m_smul
#check @BlockMassTriangular.blockE_add
#print axioms BlockMassTriangular.blockE_add
#check @BlockMassTriangular.blockE_smul
#print axioms BlockMassTriangular.blockE_smul
#check @BlockMassWorkBound.inverseSquare_nonneg
#print axioms BlockMassWorkBound.inverseSquare_nonneg
#check @BlockMassWorkBound.reciprocal_square_step
#print axioms BlockMassWorkBound.reciprocal_square_step
#check @BlockMassWorkBound.inverseSquare_tail_step
#print axioms BlockMassWorkBound.inverseSquare_tail_step
#check @BlockMassWorkBound.inverseSquare_tail_partial
#print axioms BlockMassWorkBound.inverseSquare_tail_partial
#check @BlockMassWorkBound.inverseSquare_partial_split
#print axioms BlockMassWorkBound.inverseSquare_partial_split
#check @BlockMassWorkBound.inverseSquare_partial_le_seven_fourths
#print axioms BlockMassWorkBound.inverseSquare_partial_le_seven_fourths
#check @BlockMassWorkBound.inverseSquare_summable
#print axioms BlockMassWorkBound.inverseSquare_summable
#check @BlockMassWorkBound.inverseSquare_tsum_le_seven_fourths
#print axioms BlockMassWorkBound.inverseSquare_tsum_le_seven_fourths
#check @BlockMassWorkBound.harmonicQuarter_sq_eq
#print axioms BlockMassWorkBound.harmonicQuarter_sq_eq
#check @BlockMassWorkBound.harmonicQuarter_sq_summable
#print axioms BlockMassWorkBound.harmonicQuarter_sq_summable
#check @BlockMassWorkBound.harmonicQuarter_sq_hasSum
#print axioms BlockMassWorkBound.harmonicQuarter_sq_hasSum
#check @BlockMassWorkBound.sigmaSeries_eq_scaled
#print axioms BlockMassWorkBound.sigmaSeries_eq_scaled
#check @BlockMassWorkBound.sigmaSeries_nonneg
#print axioms BlockMassWorkBound.sigmaSeries_nonneg
#check @BlockMassWorkBound.sigmaSeries_le_seven_sixtyfourths
#print axioms BlockMassWorkBound.sigmaSeries_le_seven_sixtyfourths
#check @BlockMassWorkBound.sigmaSeries_lt_one_eighth
#print axioms BlockMassWorkBound.sigmaSeries_lt_one_eighth
#check @BlockMassWorkBound.omega_sq_le_harmonicQuarter_sq
#print axioms BlockMassWorkBound.omega_sq_le_harmonicQuarter_sq
#check @BlockMassWorkBound.W_hasSum
#print axioms BlockMassWorkBound.W_hasSum
#check @BlockMassWorkBound.W_nonneg
#print axioms BlockMassWorkBound.W_nonneg
#check @BlockMassWorkBound.W_le_sigmaSeries
#print axioms BlockMassWorkBound.W_le_sigmaSeries
#check @BlockMassWorkBound.W_bounds
#print axioms BlockMassWorkBound.W_bounds
#check @BlockMassWorkBound.W_lt_one_eighth
#print axioms BlockMassWorkBound.W_lt_one_eighth
#check @BlockMassWorkBound.actual_square_gt_one
#print axioms BlockMassWorkBound.actual_square_gt_one
#check @BlockMassWorkBound.actual_work_gt_one_sub_sigma
#print axioms BlockMassWorkBound.actual_work_gt_one_sub_sigma
#check @BlockMassWorkBound.actual_work_gt_fiftyseven_sixtyfourths
#print axioms BlockMassWorkBound.actual_work_gt_fiftyseven_sixtyfourths
#check @BlockMassWorkBound.sum_witness_work_bound
#print axioms BlockMassWorkBound.sum_witness_work_bound
#check @BlockMassWorkBound.actual_work_certificate
#print axioms BlockMassWorkBound.actual_work_certificate

#print BlockMassC0Dual.Y
#print BlockMassGraphModel.Dual
#print BlockMassGraphModel.D
#print BlockMassGraphModel.graphA
#print BlockMassRankOne.bracket
#print BlockMassRankOne.GraphMonotone
#print BlockMassRankOne.MaximallyMonotone
#print BlockMassSumWitness.graphSum
#print BlockMassCounterexample.UniversalSumClaim
