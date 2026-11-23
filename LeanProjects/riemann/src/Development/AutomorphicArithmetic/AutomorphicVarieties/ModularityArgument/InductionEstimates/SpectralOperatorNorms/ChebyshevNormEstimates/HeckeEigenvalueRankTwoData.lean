import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FixOfLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.EqZeroOfSlices
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.CompLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.EllLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompHecke
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RepOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.AmpRep
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem esymm_coeff (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (Polynomial.C a * Polynomial.X + 1 : Polynomial ℂ)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty => rcases n with _ | n <;> simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_C_mul, ih]
    rcases n with _ | n
    · simp [Multiset.esymm]
    · rw [Polynomial.coeff_X_mul, ih, add_comm]
      simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

private theorem esymm_two (s t : Multiset ℂ) (j : ℕ) :
    ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) j, s.esymm (a 0) * t.esymm (a 1) = (s + t).esymm j := by
  rw [← esymm_coeff (s + t), Multiset.map_add, Multiset.prod_add, Polynomial.coeff_mul]
  simp only [esymm_coeff]
  refine Finset.sum_nbij' (fun a => (a 0, a 1)) (fun p => ![p.1, p.2]) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simpa [Finset.mem_piAntidiag, Fin.sum_univ_two] using ha
  · intro p hp
    simpa [Finset.mem_piAntidiag, Fin.sum_univ_two] using hp
  · intro a _
    funext i
    fin_cases i <;> rfl
  · intro p _
    rfl
  · intro a _
    rfl

private theorem act_cc {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] {J : L V →ₗᵢ[ℂ] H} {Y : H →L[ℂ] H} {s : ℂ → V →L[ℂ] V} (h : Act J Y s)
    {u : ℝ → V} {U : L V} (hc : Continuous u) (hs : HasCompactSupport u) (hU : ∀ᵐ x : ℝ, U x = u x) :
    ∃ (u' : ℝ → V) (U' : L V), Continuous u' ∧ HasCompactSupport u' ∧ (∀ᵐ x : ℝ, U' x = u' x) ∧ Y (J U) = J U' ∧
      ∫ x, u' x = s 0 (∫ x, u x) := by
  obtain ⟨a, κ, hκ, hY, hs0⟩ := h
  have hκ' : Continuous fun t => κ (-t) := hκ.1.comp continuous_neg
  have hκs : HasCompactSupport fun t => κ (-t) := hκ.2.comp_homeomorph (Homeomorph.neg ℝ)
  have hκi := hκ'.integrable_of_hasCompactSupport (μ := volume) hκs
  have hui := hc.integrable_of_hasCompactSupport (μ := volume) hs
  let cv := convolution (fun t => κ (-t)) u (ContinuousLinearMap.id ℂ (V →L[ℂ] V)) volume
  have cvc : Continuous cv := hs.continuous_convolution_right _ hκi.locallyIntegrable hc
  have cvs : HasCompactSupport cv := hκs.convolution _ hs
  have cve : ∀ x, cv x = ∫ t, κ t (u (x + t)) := fun x => by
    rw [← integral_neg_eq_self]
    simp only [cv, convolution, ContinuousLinearMap.id_apply, sub_eq_add_neg]
  have cvi : ∫ x, cv x = symb κ 0 (∫ x, u x) := by
    rw [integral_convolution _ hκi hui, integral_neg_eq_self κ, symb]
    simp
  have tc : ∀ t, Continuous fun x => a t (u (x + t)) := fun t => (a t).continuous.comp (hc.comp (continuous_add_const t))
  have ts : ∀ t, HasCompactSupport fun x => a t (u (x + t)) := fun t =>
    (hs.comp_homeomorph (Homeomorph.addRight t)).comp_left (g := a t) (map_zero _)
  have sc : Continuous fun x => ∑ t ∈ a.support, a t (u (x + t)) := continuous_finset_sum _ fun t _ => tc t
  have ss : HasCompactSupport fun x => ∑ t ∈ a.support, a t (u (x + t)) := by
    induction a.support using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact HasCompactSupport.zero
    | insert t T ht ih =>
      simp only [Finset.sum_insert ht]
      exact (ts t).add ih
  refine ⟨fun x => ∑ t ∈ a.support, a t (u (x + t)) + cv x, _, sc.add cvc, ss.add cvs, ?_, hY U, ?_⟩
  · have h1 : ∀ᵐ x : ℝ, ∀ t ∈ a.support, (a t).compLpL 2 volume (sh V t U) x = a t (u (x + t)) := by
      refine (Filter.eventually_all_finset _).2 fun t _ => ?_
      filter_upwards [(a t).coeFn_compLpL (sh V t U), sh_ae V t U,
        (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hU] with x p q r
      rw [p, q, r]
    filter_upwards [h1, Lp.coeFn_add (a.sum fun t c => c.compLpL 2 volume (sh V t U)) (conv κ U), (convSpec κ hκ U).1,
      MeasureTheory.Lp.coeFn_finsetSum a.support fun t => (a t).compLpL 2 volume (sh V t U)] with x p q r o
    rw [q, Pi.add_apply, r, cve, Finsupp.sum, o]
    congr 1
    · rw [Finset.sum_apply]
      exact Finset.sum_congr rfl p
    · refine integral_congr_ae ?_
      filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae hU] with t ht
      rw [ht]
  · rw [integral_add (sc.integrable_of_hasCompactSupport ss) (cvc.integrable_of_hasCompactSupport cvs), cvi, hs0,
      integral_finset_sum _ fun t _ => (tc t).integrable_of_hasCompactSupport (ts t), ContinuousLinearMap.add_apply, Finsupp.sum,
      ContinuousLinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [(a t).integral_comp_comm (hui.comp_add_right t), integral_add_right_eq_self]
    simp

private theorem sign_data_rank_two {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} (b b' : BW.Blo S 2) :
    (dat2 b b').rho (0 : Fin 2) = -1 ∧ (dat2 b b').rho (1 : Fin 2) = 1 := by
  constructor
  · show ((∑ _l ∈ (∅ : Finset (Fin 2)), ((2 : ℕ) : ℝ)) - ((((2 : ℕ) : ℝ)) + 0)) / 2 = -1
    norm_num
  · show (((((2 : ℕ) : ℝ)) + 0) - ∑ _l ∈ (∅ : Finset (Fin 2)), ((2 : ℕ) : ℝ)) / 2 = 1
    norm_num

private theorem hecke_eigenvalue_rank_two_data {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} (b b' : BW.Blo S 2)
    (φ : GlobalTheory.CuspRep.Sm E (2 + 2)) (w : Pl E) (j : ℕ) (t : Fin 2 → ℝ) (h : BW.Umg φ) (hS : BW.Sph S φ) (hw : w ∉ S) (hj : j ≤ 2 + 2) :
    (dat2 b b').comp (BW.hk (2 + 2) w j φ).1 t = ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) j,
      (((b.sat w).map fun x : ℂˣ => (x : ℂ)).esymm (a 0) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-((-1 : ℝ) : ℂ) * a 0)) *
      (((b'.sat w).map fun x : ℂˣ => (x : ℂ)).esymm (a 1) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-((1 : ℝ) : ℂ) * a 1)) *
      (dat2 b b').comp φ.1 (fun l : Fin 2 => t l - a l * Real.log (Formalism.UG.qV E w)) := by
  refine (BW.compHecke E S (2 + 2) (dat2 b b') φ w j t h hS hw hj).trans (Finset.sum_congr rfl fun a _ => ?_)
  refine congrArg₂ (· * ·) ((Fin.prod_univ_two _).trans ?_) rfl
  rw [← (sign_data_rank_two b b').1]
  conv_rhs => enter [2]; rw [← (sign_data_rank_two b b').2]
  rfl

private theorem cancel {q : ℕ} (hq : q ≠ 0) (x : ℝ) (a b : ℕ) :
    (q : ℂ) ^ (-((-1 : ℝ) : ℂ) * a) * (q : ℂ) ^ (-((1 : ℝ) : ℂ) * b) *
      Complex.exp ((x - a * Real.log q - (-x - b * Real.log q) : ℝ) : ℂ) = Complex.exp ((x - -x : ℝ) : ℂ) := by
  have h : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [Complex.cpow_def_of_ne_zero h, Complex.cpow_def_of_ne_zero h, ← Complex.exp_add, ← Complex.exp_add, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.genT :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢) (w : Pl E), w ∉ 𝔢.S → ∀ i : Fin (2 + 2),
      (∃ s, Act 𝔵.A'.J (Tsph μ w i) s ∧ s 0 ∘L 𝔵.a₀ = hval 𝔵.t (w, i) • 𝔵.a₀) ∧ Tsph μ w i ∘L 𝔵.P = 𝔵.P ∘L Tsph μ w i := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 w hw i
  obtain ⟨⟨s, hs⟩, hP⟩ := genTk 𝔵 w hw i
  refine ⟨⟨s, hs, ?_⟩, hP⟩
  ext1 e
  obtain ⟨ρ, N, Lf, hL, -⟩ := BW.ampRep E (2 + 2) μ 𝔢.toAmp (by norm_num)
  let β : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have c₀ : Continuous fun x : ℝ => β.normed volume x • e := β.continuous_normed.smul continuous_const
  have s₀ : HasCompactSupport fun x : ℝ => β.normed volume x • e := β.hasCompactSupport_normed.smul_right
  have i₀ : ∫ x : ℝ, β.normed volume x • e = e := by rw [integral_smul_const, β.integral_normed, one_smul]
  have m₀ : MemLp (fun x : ℝ => β.normed volume x • e) 2 volume := c₀.memLp_of_hasCompactSupport s₀
  obtain ⟨u, U, uc, us, hU, hAU, iu⟩ := act_cc ((actLaws 𝔵.A'.J).2.1 _ _ 𝔵.a_acts.1 𝔵.a_acts.2.1) c₀ s₀ m₀.coeFn_toLp
  obtain ⟨u', U', uc', us', hU', hTU, iu'⟩ := act_cc hs uc us hU
  rw [i₀] at iu
  obtain ⟨hR, -, hS⟩ := hL (𝔵.A'.J m₀.toLp)
  set φ := Lf (𝔵.A'.J m₀.toLp)
  rw [← 𝔢.a_op, hAU] at hR
  have hR' := (BW.repOps E (2 + 2) μ (by norm_num) _ _ hR).2.2.2 w i (hS w hw)
  rw [hTU] at hR'
  refine sub_eq_zero.1 (bloEx 𝔵 _ fun b b' hb hb' k hk => ?_)
  obtain ⟨ℓ, hℓ⟩ := ellLin 𝔵 b b' hb hb' k
  obtain ⟨c, hc, hcl⟩ := compLine 𝔵 b b' hb hb'
  have h1 := hcl k hk u U φ uc us hU hR
  have h2 := hcl k hk u' U' _ uc' us' hU' hR'
  obtain ⟨hS', hcomm⟩ := ((BW.hkOps E (2 + 2) w (i + 1)).2.2.2 𝔢.S φ hw hS).2.2.1 ⟨_, hk⟩
  have hU2 := ((BW.umgOps E (2 + 2)).2 φ hR.umg).2.2.2.2.1 ((k : G1 E (2 + 2)) : GlobalTheory.CuspRep.GA E (2 + 2))
  have pw : ∀ x : ℝ, ℓ (u' x) = ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) (i + 1 : ℕ),
      (𝔵.B₂ w).esymm (a 0) * (𝔵.B₁ w).esymm (a 1) * ℓ (u (x - ((a 0 : ℝ) - a 1) * Real.log (Formalism.UG.qV E w) / 2)) := fun x => by
    have h3 := hecke_eigenvalue_rank_two_data b b' _ w (i + 1) ![x, -x] hU2 hS' hw i.2
    have h5 : c * Complex.exp ((x - -x : ℝ) : ℂ) * ell b b' k (𝔵.A'.sec (u' ((x - -x) / 2))) = _ :=
      (h2 (![x, -x] : Fin 2 → ℝ)).symm.trans ((congrArg (fun ψ : GlobalTheory.CuspRep.Sm E (2 + 2) => (dat2 b b').comp ψ.1 (![x, -x] : Fin 2 → ℝ))
        hcomm).trans h3)
    rw [show (x - -x) / 2 = x by ring] at h5
    refine mul_left_cancel₀ (mul_ne_zero hc (Complex.exp_ne_zero ((x - -x : ℝ) : ℂ))) ?_
    rw [hℓ, Finset.mul_sum, h5]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h6 : _ = c * Complex.exp ((x - a 0 * Real.log (Formalism.UG.qV E w) - (-x - a 1 * Real.log (Formalism.UG.qV E w)) : ℝ) : ℂ) *
        ell b b' k (𝔵.A'.sec (u ((x - a 0 * Real.log (Formalism.UG.qV E w) - (-x - a 1 * Real.log (Formalism.UG.qV E w))) / 2))) :=
      h1 fun l : Fin 2 => (![x, -x] : Fin 2 → ℝ) l - a l * Real.log (Formalism.UG.qV E w)
    rw [h6, hb.sat w hw, hb'.sat w hw, hℓ, ← cancel (GlobalTheory.LFun.qV_ne_zero w) x (a 0) (a 1),
      show x - ((a 0 : ℝ) - a 1) * Real.log (Formalism.UG.qV E w) / 2 =
        (x - a 0 * Real.log (Formalism.UG.qV E w) - (-x - a 1 * Real.log (Formalism.UG.qV E w))) / 2 by ring]
    ring
  have hui := uc.integrable_of_hasCompactSupport (μ := volume) us
  have h4 := integral_congr_ae (μ := volume) (Eventually.of_forall pw)
  rw [ℓ.integral_comp_comm (uc'.integrable_of_hasCompactSupport us'),
    integral_finset_sum _ fun a _ => (ℓ.integrable_comp (hui.comp_sub_right _)).const_mul _] at h4
  simp only [integral_const_mul, integral_sub_right_eq_self fun x => ℓ (u x)] at h4
  rw [← Finset.sum_mul, esymm_two, ℓ.integral_comp_comm hui, iu', iu, add_comm] at h4
  rw [← hℓ, map_sub, sub_eq_zero]
  exact h4.trans (ℓ.map_smul _ _).symm
