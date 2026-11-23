import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.HerbrandFinLen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.EventuallyMQGrFiniteAnnihilator
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocalizedLengthLeOfSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocLenAPieceIdeal2LeTwoPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocLenQuotientWeightPieceLeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.TspHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ValuationNonnegApplyDegreeZeroOfOnS
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.HomHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SignHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.GrEqRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FgHolds
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.up_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    SpansCot x 𝒜 (-1) Q.F → SpansCot x 𝒜 (-2) Q.G → M2 𝒜 Q.ideal → M3 𝒜 K x Q.ideal → M4 𝒜 K Q.ideal →
    ∀ a : 𝒜 0, M5 𝒜 K x Q.ideal a → ∀ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T →
    ∀ J : Ideal (mR Q), (GMod.self (mGr Q)).IsHomSub J → secs (ts Q) ≤ J → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ J) →
      ∀ᶠ d in atTop, (chi [(0, algebraMap (𝒜 0) (mR Q) a)] (mQ Q J) d : ℝ) ≤ 2 ^ (r + 1 + r') * ∑ ξ ∈ T, v (ξ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv A _ _ 𝒜 _ _ x hW r s r' s' m Q hF hG h2 h3 h4 a h5 T hT J hJ hsec hZ
  classical
  have hfg := fg_holds O A 𝒜 x hW
  have hN : ∀ i, (mN 𝒜 (Q.F (Fin.last r)) i).FG := by
    intro i
    fin_cases i
    · exact hfg _
    · exact hfg _
    · exact (Submodule.fg_span_singleton _).sup (((hfg _).mul (hfg _)).mul (hfg _))
  let X : HidaSetting 3 := { B := 𝒜 0, R := mR Q, 𝒜 := mGr Q, std := std_holds (𝒜 0) A 3 _ hN }
  have hself : (GMod.self (mGr Q)).IsGr (mGr Q) :=
    ⟨fun {d e} {p} {q : mR Q} (hp : p ∈ mGr Q d) (hq : q ∈ mGr Q e) => (SetLike.mul_mem_graded hp hq : p * q ∈ mGr Q (d + e)),
      rees_internal _, Module.Finite.self (mR Q)⟩
  have hGr : (mQ Q J).IsGr (mGr Q) := ((ruleGr 3 X _ hself).1 J hJ).2
  have hfin : ∀ d, Module.Finite (𝒜 0) ((mQ Q J).gr d) := (ruleFin 3 X _ hGr).1
  obtain ⟨hI, -, -⟩ := hom_holds O A 𝒜 x hW r s r' s' m Q
  have hD : ∀ ξ : A →ₐ[O] K, TwoSigned 𝒜 ξ ↔ ¬ idD 𝒜 ≤ RingHom.ker (res0 𝒜 ξ) := by
    intro ξ
    obtain ⟨hn, hp⟩ := sign_holds O A 𝒜 x hW K ξ
    rw [TwoSigned, hn, hp]
    constructor
    · rintro ⟨⟨f, hf, hf0⟩, g, hg, hg0⟩ hle
      have hm : f * g ∈ 𝒜 0 := by
        have := SetLike.GradedMul.mul_mem hf hg
        simpa using this
      have h1 : (⟨f * g, hm⟩ : 𝒜 0) ∈ idD 𝒜 := Ideal.subset_span ⟨f, hf, g, hg, rfl⟩
      have h2 : ξ (f * g) = 0 := hle h1
      rw [map_mul] at h2
      exact mul_ne_zero hf0 hg0 h2
    · intro h
      by_contra hc
      refine h (Ideal.span_le.2 ?_)
      rintro b ⟨f, hf, g, hg, hb⟩
      show ξ (b : A) = 0
      rw [hb, map_mul]
      by_contra hne
      exact hc ⟨⟨f, hf, left_ne_zero_of_mul hne⟩, g, hg, right_ne_zero_of_mul hne⟩
  have hpos : ∀ ξ ∈ T, ξ a ≠ 0 ∧ 0 ≤ v (ξ a) := fun ξ hξ =>
    ⟨h5.2.2 ξ (hT.1 ξ hξ).1 (hT.1 ξ hξ).2,
      valuation_nonneg_apply_degreeZero_of_onS O K v hv A 𝒜 x Q.ideal h2 ξ (hT.1 ξ hξ).1 a a.2 (h5.2.2 ξ (hT.1 ξ hξ).1 (hT.1 ξ hξ).2)⟩
  have hsum : ∑ σ ∈ T.image (res0 𝒜), v (σ a) ≤ ∑ ξ ∈ T, v (ξ a) :=
    Finset.sum_image_le_of_nonneg (f := fun σ : 𝒜 0 →ₐ[O] K => v (σ a)) (g := res0 𝒜) (s := T) fun σ hσ => by
      obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 hσ
      exact (hpos ξ hξ).2
  filter_upwards [eventually_mQ_gr_finite_annihilator O K A 𝒜 x hW r s r' s' m Q hF hG h2 h3 J hJ hsec hZ, eventually_ge_atTop 1] with d hd hd1
  haveI := hfin d
  have key := th_holds O K v hv (𝒜 0) ((mQ Q J).gr d) hd.1 a (T.image (res0 𝒜)) (2 ^ (r + 1 + r')) ?_ ?_
  · rw [chi_single0 _ hGr.internal]
    refine key.trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  · intro σ hσ
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 hσ
    refine ⟨(hpos ξ hξ).1, (hpos ξ hξ).2, ?_⟩
    have hσ' := (hD ξ).1 (hT.1 ξ hξ).2
    refine (locLen_mQ_gr_le_locLen_aPiece O K A 𝒜 x hW r s r' s' m Q J hsec hZ _ hσ' d hd1).trans ?_
    push_cast
    exact locLen_aPiece_ideal2_le_two_pow O K A 𝒜 x hW r s r' s' m Q _ (locLen_quotientWeightPiece_le_one O K A 𝒜 x hW _ hI h2 h4 _ hσ') _
  · intro σ hσ
    refine hd.2 σ ?_
    by_contra hc
    rw [not_or] at hc
    obtain ⟨ξ, hξ, rfl⟩ := tsp_holds O K A 𝒜 x hW _ hI σ fun b hb => by
      by_contra hne
      exact hc.2 ⟨b, hb, hne⟩
    obtain ⟨ξ', hξ', t, rfl⟩ := hT.2 ξ hξ ((hD ξ).2 hc.1)
    refine hσ (Finset.mem_image.2 ⟨ξ', hξ', AlgHom.ext fun b => ?_⟩)
    show ξ' (b : A) = act 𝒜 (tz t) ξ' (b : A)
    rw [act_of_mem 𝒜 _ _ b.2]
    simp
