import LinearAssemblies

set_option autoImplicit false

/-! Run `lake env lean Audit.lean` to inspect foundational proof dependencies.
Explicit hypotheses are part of theorem types, not part of this axiom listing.
-/

#print axioms LinearAssemblies.OnePad.maximizing_degree_le_three
#print axioms LinearAssemblies.OnePad.reduced_recurrence
#print axioms LinearAssemblies.OnePad.closed_form_scaled
#print axioms LinearAssemblies.OnePad.fastF_eq_F
#print axioms LinearAssemblies.OnePad.minimumBudget_eq_threeCandidates
#print axioms LinearAssemblies.OnePad.recurrenceCost_100
#print axioms LinearAssemblies.OnePad.ResetProgram.attainable_iff
#print axioms LinearAssemblies.System.card_interfaces_le_cost
#print axioms LinearAssemblies.System.entryProbability_sum
#print axioms LinearAssemblies.onePad_embedding
#print axioms LinearAssemblies.Probability.FiniteChain.partial_mass_le_one
#print axioms LinearAssemblies.Probability.FiniteChain.absorption_atom_bound
#print axioms LinearAssemblies.Probability.FiniteChain.mem_window_iff
#print axioms LinearAssemblies.Probability.FiniteChain.accuracy_lower_bound
#print axioms LinearAssemblies.Probability.UniformGraph.haltable_of_potential
#print axioms LinearAssemblies.Probability.UniformGraph.chain_mass_eq
#print axioms LinearAssemblies.Probability.UniformGraph.restrict_mass
#print axioms LinearAssemblies.Probability.UniformGraph.restrict_haltable
#print axioms LinearAssemblies.System.onePad_graph_cost_le
#print axioms LinearAssemblies.System.length_atom_bound
#print axioms LinearAssemblies.System.attachmentWindow_eq_chain
#print axioms LinearAssemblies.System.accuracy_lower_bound
#print axioms LinearAssemblies.System.accuracy_small_target
#print axioms LinearAssemblies.System.expectedLength_eq
#print axioms LinearAssemblies.System.summable_length
#print axioms LinearAssemblies.OnePad.potential_le_F_cost
#print axioms LinearAssemblies.OnePad.CertifiedBlock.compile_exists
#print axioms LinearAssemblies.OnePad.TileCompiler.choices_sum
#print axioms LinearAssemblies.OnePad.TileCompiler.system_potential
#print axioms LinearAssemblies.OnePad.mean_le_F
#print axioms LinearAssemblies.OnePad.exact_characterization
#print axioms LinearAssemblies.OnePad.minimum_tile_cost
#print axioms LinearAssemblies.OnePad.minimum_tile_cost_100
#print axioms LinearAssemblies.Forest.det_incidence_rooted
#print axioms LinearAssemblies.Forest.det_incidence_not_rooted
#print axioms LinearAssemblies.Forest.rooted_redirect_iff
#print axioms LinearAssemblies.Forest.det_laplacian
#print axioms LinearAssemblies.Forest.det_updateCol_termination
#print axioms LinearAssemblies.Forest.Counts.positive_forest
#print axioms LinearAssemblies.Forest.Counts.B_nonneg
#print axioms LinearAssemblies.Forest.Counts.H_nonneg
#print axioms LinearAssemblies.Forest.Counts.B_degree
#print axioms LinearAssemblies.Forest.Counts.B_one_le_product
#print axioms LinearAssemblies.Forest.Counts.B_zero_eq_H_zero
#print axioms LinearAssemblies.Forest.Counts.B_zero_pos
#print axioms LinearAssemblies.Forest.Counts.B_eq_determinant
#print axioms LinearAssemblies.Forest.Counts.H_eq_cramer
#print axioms LinearAssemblies.Forest.Counts.nonnegative_integer_representation
#print axioms LinearAssemblies.Probability.UniformGraph.transient_haltable
#print axioms LinearAssemblies.System.tile_polynomial_representation
#print axioms LinearAssemblies.System.general_coefficient_bounds
#print axioms LinearAssemblies.System.onePad_coefficient_bounds

-- Print the explicit external assumption boundary as well as foundational axioms.
#check LinearAssemblies.Probability.FiniteAbsorptionLaw.normalized
#check LinearAssemblies.Probability.FiniteAbsorptionLaw.finite_mean
#check LinearAssemblies.Probability.FiniteAbsorptionLaw.first_step
#check LinearAssemblies.Probability.FiniteAbsorptionLaw.unique
#check LinearAssemblies.OnePad.exact_characterization
#check LinearAssemblies.OnePad.minimum_tile_cost
#check LinearAssemblies.System.accuracy_lower_bound
#check LinearAssemblies.Forest.Counts.nonnegative_integer_representation
#check LinearAssemblies.System.tile_polynomial_representation
#check LinearAssemblies.System.general_coefficient_bounds
#check LinearAssemblies.System.onePad_coefficient_bounds

-- Stopping transform and complete concentration lower bounds.
#print axioms LinearAssemblies.Probability.UniformGraph.pgf_first_step
#print axioms LinearAssemblies.Probability.UniformGraph.transform_hasDerivAt
#print axioms LinearAssemblies.Probability.UniformGraph.transform_eq_ratio
#print axioms LinearAssemblies.Forest.weighted_degree_le
#print axioms LinearAssemblies.Forest.log_coeff_sum_bound
#print axioms LinearAssemblies.Probability.UniformGraph.logarithmic_derivative_bound
#print axioms LinearAssemblies.Probability.UniformGraph.tiltedMean_lower
#print axioms LinearAssemblies.Probability.alarm_survival
#print axioms LinearAssemblies.Probability.UniformGraph.confidence_polynomial_bounds
#print axioms LinearAssemblies.System.confidence_polynomial_bounds
#print axioms LinearAssemblies.System.general_confidence_bounds
#print axioms LinearAssemblies.System.onePad_confidence_bounds
#print axioms LinearAssemblies.Probability.growth_inverse_bound
#print axioms LinearAssemblies.System.general_concentration_lower_bound
#print axioms LinearAssemblies.System.onePad_concentration_lower_bound
#check LinearAssemblies.System.general_concentration_lower_bound
#check LinearAssemblies.System.onePad_concentration_lower_bound

-- Quantitative one-pad bounds, explicit shared-reset construction, and general mean bound.
#print axioms LinearAssemblies.PositiveDigits.represents
#print axioms LinearAssemblies.PositiveDigits.reset_valid
#print axioms LinearAssemblies.OnePad.ternary_cost_cube
#print axioms LinearAssemblies.OnePad.logarithmic_upper_bound
#print axioms LinearAssemblies.OnePad.F_cube_bound
#print axioms LinearAssemblies.OnePad.F_exponential_bound
#print axioms LinearAssemblies.OnePad.logarithmic_constant_lt
#print axioms LinearAssemblies.OnePad.logarithmic_lower_bound
#print axioms LinearAssemblies.OnePad.CertifiedBlock.compile_bounded_exists
#print axioms LinearAssemblies.OnePad.onePad_block_exists
#print axioms LinearAssemblies.Presentation.system_potential
#print axioms LinearAssemblies.Presentation.system_mean
#print axioms LinearAssemblies.DigitData.represents
#print axioms LinearAssemblies.DigitData.count_log_bound
#print axioms LinearAssemblies.TwoPad.row_sum
#print axioms LinearAssemblies.TwoPad.tile_cost
#print axioms LinearAssemblies.TwoPad.certificate
#print axioms LinearAssemblies.TwoPad.exact_construction
#print axioms LinearAssemblies.TwoPad.block_remaining_bound
#print axioms LinearAssemblies.TwoPad.flexible_mean
#print axioms LinearAssemblies.Probability.weighted_series_limit
#print axioms LinearAssemblies.Probability.UniformGraph.mean_le_coeff_sum
#print axioms LinearAssemblies.System.mean_growth_bound
#print axioms LinearAssemblies.System.expected_length_lower_bound
#check LinearAssemblies.OnePad.logarithmic_upper_bound
#check LinearAssemblies.OnePad.logarithmic_lower_bound
#check LinearAssemblies.OnePad.onePad_block_exists
#check LinearAssemblies.TwoPad.exact_construction
#check LinearAssemblies.TwoPad.block_remaining_bound
#check LinearAssemblies.System.expected_length_lower_bound

-- Uniform base selection and block tails.
#print axioms LinearAssemblies.selectedBase_le
#print axioms LinearAssemblies.selectedBase_cost
#print axioms LinearAssemblies.TwoPad.balanced_block_exists
#print axioms LinearAssemblies.TwoPad.logarithmic_upper_bound
#print axioms LinearAssemblies.Probability.FiniteChain.survival_markov
#print axioms LinearAssemblies.Probability.FiniteChain.survival_shift_le
#print axioms LinearAssemblies.Probability.FiniteChain.survival_blocks
#print axioms LinearAssemblies.Probability.UniformGraph.uniform_block_tail
#check LinearAssemblies.TwoPad.balanced_block_exists
#check LinearAssemblies.TwoPad.logarithmic_upper_bound
#check LinearAssemblies.Probability.UniformGraph.uniform_block_tail

-- Physical concatenation and concentration upper bounds.
#print axioms LinearAssemblies.Probability.UniformGraph.sequential_mass
#print axioms LinearAssemblies.Concatenation.cost
#print axioms LinearAssemblies.Concatenation.certificate
#print axioms LinearAssemblies.Concatenation.system_mass
#print axioms LinearAssemblies.Concatenation.onePadSeparation
#print axioms LinearAssemblies.Concatenation.twoPadSeparation
#print axioms LinearAssemblies.OnePadBlock.join_mass
#print axioms LinearAssemblies.TwoPadBlock.join_mass
#print axioms LinearAssemblies.OnePadBlock.join_cost
#print axioms LinearAssemblies.TwoPadBlock.join_cost
#print axioms LinearAssemblies.Probability.BlockLaw.real_tail
#print axioms LinearAssemblies.Probability.BlockLaw.centered_tail
#print axioms LinearAssemblies.Probability.block_concentration
#print axioms LinearAssemblies.balanced_squares
#print axioms LinearAssemblies.phi_mono
#print axioms LinearAssemblies.phi_double
#print axioms LinearAssemblies.Concentration.deterministic_one
#print axioms LinearAssemblies.Concentration.deterministic_two
#print axioms LinearAssemblies.Concentration.one_balanced
#print axioms LinearAssemblies.Concentration.two_balanced
#print axioms LinearAssemblies.Appendable.failure_eq_deviation
#print axioms LinearAssemblies.onePad_concentrated_upper
#print axioms LinearAssemblies.twoPad_concentrated_upper
#check LinearAssemblies.Probability.SubexponentialEquivalence
#print LinearAssemblies.Probability.SubexponentialEquivalence
#check LinearAssemblies.Probability.BernsteinLaw
#print LinearAssemblies.Probability.BernsteinLaw
#check LinearAssemblies.Probability.block_concentration
#check LinearAssemblies.onePad_concentrated_upper
#check LinearAssemblies.twoPad_concentrated_upper

-- Completed pad extensions, fixed regimes, and optimization algorithms.
#print axioms LinearAssemblies.System.failure_add_window
#print axioms LinearAssemblies.System.Concentrated.window
#print axioms LinearAssemblies.twoToPads_rule
#print axioms LinearAssemblies.twoToPads_injective
#print axioms LinearAssemblies.Appendable.map_concentrated
#print axioms LinearAssemblies.kPad_concentrated_upper
#print axioms LinearAssemblies.fixed_confidence_regimes
#print axioms LinearAssemblies.polynomial_confidence_regimes
#print axioms LinearAssemblies.OnePad.Algorithms.binary_fuel
#print axioms LinearAssemblies.OnePad.Algorithms.scan_spec
#print axioms LinearAssemblies.OnePad.Algorithms.sequential_correct
#print axioms LinearAssemblies.OnePad.Algorithms.sequential_cost
#print axioms LinearAssemblies.OnePad.Algorithms.beta_bounds
#print axioms LinearAssemblies.OnePad.Algorithms.log_window
#print axioms LinearAssemblies.OnePad.Algorithms.threshold_window
#print axioms LinearAssemblies.OnePad.Algorithms.select_correct
#print axioms LinearAssemblies.Algorithms.power_correct
#print axioms LinearAssemblies.Algorithms.power_cost
#print axioms LinearAssemblies.OnePad.Algorithms.precision_error
#print axioms LinearAssemblies.OnePad.Algorithms.approximateBeta_correct
#print axioms LinearAssemblies.OnePad.Algorithms.approximation_output_size
#print axioms LinearAssemblies.OnePad.Algorithms.approximation_polynomial
#print axioms LinearAssemblies.OnePad.Algorithms.selectCosted_correct
#print axioms LinearAssemblies.OnePad.Algorithms.selection_cost
#print axioms LinearAssemblies.OnePad.Algorithms.fastThreshold_correct
#print axioms LinearAssemblies.OnePad.Algorithms.fast_correct
#print axioms LinearAssemblies.OnePad.Algorithms.eventually_polynomial_size
#print axioms LinearAssemblies.OnePad.Algorithms.fast_cost_raw
#print axioms LinearAssemblies.OnePad.Algorithms.fast_cost_bitlength
#print axioms LinearAssemblies.OnePad.Algorithms.theorem_six
#print axioms LinearAssemblies.OnePad.Algorithms.theorem_seven
#check LinearAssemblies.kPad_concentrated_upper
#check LinearAssemblies.fixed_confidence_regimes
#check LinearAssemblies.polynomial_confidence_regimes
#check LinearAssemblies.OnePad.Algorithms.theorem_six
#check LinearAssemblies.OnePad.Algorithms.theorem_seven
#print LinearAssemblies.Algorithms.Multiplication.Fast
#print LinearAssemblies.Algorithms.Multiplication.Fast.correct
#print LinearAssemblies.Algorithms.Multiplication.Fast.bound
#print LinearAssemblies.Algorithms.Logarithm.Polynomial
#print LinearAssemblies.Algorithms.Logarithm.Polynomial.accurate
#print LinearAssemblies.Algorithms.Logarithm.Polynomial.bound
