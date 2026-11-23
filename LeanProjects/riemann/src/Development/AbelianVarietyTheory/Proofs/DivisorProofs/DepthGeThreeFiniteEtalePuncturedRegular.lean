import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfEtalePuncturedOfDepthPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEQuotientMapSpanSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleQuotientOfEtalePuncturedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDepthTwoHullOfEtalePuncturedSpectrumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFreeEtaleLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomOfEtalePuncturedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveAndSaturatedOfInjectiveModRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelTorsionOfFiniteLengthModElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLengthCokerOfEtalePuncturedSpectrumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEThreeOfFreeRegularLocalStatement

open IsLocalRing

namespace GlobalTheory.LocalLefschetz

lemma two_le_of_add_one {x y : WithBot ℕ∞} (h : x + 1 = y) (hy : 3 ≤ y) : 2 ≤ x := by
  subst h
  induction x using WithBot.recBotCoe with
  | bot => simp at hy
  | coe n =>
    have h3 : (3 : ℕ∞) ≤ n + 1 := WithBot.coe_le_coe.mp hy
    have : (2 : ℕ∞) ≤ n := by
      induction n using ENat.recTopCoe with
      | top => simp
      | coe m =>
        have : (3 : ℕ) ≤ m + 1 := by exact_mod_cast h3
        exact_mod_cast (by omega : 2 ≤ m)
    exact WithBot.coe_le_coe.mpr this

theorem depth_three : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ∉ maximalIdeal R ^ 2 → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], GlobalTheory.PurityFree (R ⧸ Ideal.span {f}) → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ReciprocityTheory.CA.ModDepthGE R A 3 := by
  intro R _ _ hcomp hdim f hf hf2 _ hpur A _ _ _ hdep hEt
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf2 (Ideal.zero_mem _)
  haveI : IsDomain R := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain R
  have hreg : IsSMulRegular A f :=
    GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' R A (ReciprocityTheory.CA.ModDepthGE.mono (by norm_num) hdep) hEt f hf0
  haveI hRb : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hf hf2
  have hdimb : 2 ≤ ringKrullDim (R ⧸ Ideal.span {f}) :=
    two_le_of_add_one
      (ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hf hf2) hdim
  haveI : Module.Finite R (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R ((Ideal.span {f}).map (algebraMap R A))).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hdepb := GlobalTheory.modDepthGE_quotient_map_span_singleton R A f hf hreg 1 hdep
  have hEtb := GlobalTheory.T.etale_quotient_of_etale_punctured' R A f hEt
  obtain ⟨A', _, _, hA'fin, ι, hι, hdep', hEt', k, hk⟩ := GlobalTheory.T.exists_finite_depth_two_hull_of_etale_punctured_spectrum _ hdimb _ hdepb hEtb
  have hfree : Module.Free (R ⧸ Ideal.span {f}) A' := hpur A' hdep' hEt'
  obtain ⟨_, _⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (R ⧸ Ideal.span {f})
  have hnf : ¬ IsField (R ⧸ Ideal.span {f}) := by
    intro hF
    have := ringKrullDim_eq_zero_of_isField hF
    rw [this] at hdimb
    exact absurd hdimb (by decide)
  have hEtA' : Algebra.Etale (R ⧸ Ideal.span {f}) A' := by
    refine GlobalTheory.T.etale_of_etale_at_height_one_primes _ A' hnf fun p _ hp => hEt' p ?_
    rintro rfl
    have h1 := maximalIdeal_height_eq_ringKrullDim (R := R ⧸ Ideal.span {f})
    rw [hp] at h1
    rw [← h1] at hdimb
    exact absurd hdimb (by decide)
  obtain ⟨B, _, _, hBfin, hBfree, hBet, ⟨e⟩⟩ := GlobalTheory.T.exists_finite_free_etale_lift_of_quotient_etale R hcomp f hf A'
  let φ : A →ₐ[R] B ⧸ (Ideal.span {f}).map (algebraMap R B) :=
    { toRingHom := e.symm.toRingHom.comp (ι.toRingHom.comp (Ideal.Quotient.mk _))
      commutes' := fun r => by
        have h1 : (Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R A)) (algebraMap R A r)) =
            algebraMap (R ⧸ Ideal.span {f}) _ (algebraMap R (R ⧸ Ideal.span {f}) r) := by
          rw [← IsScalarTower.algebraMap_apply]; rfl
        show e.symm (ι (Ideal.Quotient.mk _ (algebraMap R A r))) = _
        rw [h1, ι.commutes, e.symm.commutes, ← IsScalarTower.algebraMap_apply] }
  have hφ : ∀ a, φ a = e.symm (ι (Ideal.Quotient.mk _ a)) := fun a => rfl
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_lift_algHom_of_etale_punctured R hcomp hdim f hf hf0 A hEt B φ
  have hψa : ∀ a, Ideal.Quotient.mk _ (ψ a) = φ a := fun a => by
    rw [← hψ]; rfl
  have hBreg : IsSMulRegular B f := fun x y h => smul_right_injective B hf0 h
  have hsat : ∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) →
      a ∈ (Ideal.span {f}).map (algebraMap R A) := by
    intro a ha
    have h1 : φ a = 0 := by
      rw [← hψa]; exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [hφ] at h1
    have h2 : ι (Ideal.Quotient.mk _ a) = 0 := by
      simpa using h1
    have h3 : Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R A)) a = 0 :=
      hι (by rw [h2, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  obtain ⟨hinj, hfsat⟩ := GlobalTheory.T.injective_and_saturated_of_injective_mod_regular' R A B f hf hBreg ψ hsat
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {f})) ≤ maximalIdeal (R ⧸ Ideal.span {f}) := by
    rw [Ideal.map_le_iff_le_comap]
    have : (maximalIdeal (R ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal R := by
      haveI := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
        Ideal.Quotient.mk_surjective (K := maximalIdeal (R ⧸ Ideal.span {f}))
      exact IsLocalRing.eq_maximalIdeal this
    rw [this]
  have hspan : ∀ z : B, z ∈ (Ideal.span {f}).map (algebraMap R B) → ∃ c : B, z = f • c := by
    intro z hz
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hz
    obtain ⟨c, hc⟩ := hz
    exact ⟨c, by rw [Algebra.smul_def, ← hc, mul_comm]⟩
  have hcok : ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c := by
    refine ⟨k, fun x hx b => ?_⟩
    have hx' : Ideal.Quotient.mk (Ideal.span {f}) x ∈ maximalIdeal (R ⧸ Ideal.span {f}) ^ k := by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {f})) hx
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono hmap k this
    obtain ⟨abar, habar⟩ := hk _ hx' (e (Ideal.Quotient.mk _ b))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective abar
    refine ⟨a, ?_⟩
    have h1 : Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R B)) (x • b - ψ a) = 0 := by
      rw [map_sub, hψa, hφ]
      change Ideal.Quotient.mk _ (x • b) - e.symm (ι (Ideal.Quotient.mk _ a)) = 0
      have habar' : ι (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk (Ideal.span {f}) x • e (Ideal.Quotient.mk _ b) := habar
      have h2 : ∀ z, e.symm (Ideal.Quotient.mk (Ideal.span {f}) x • e z) =
          Ideal.Quotient.mk (Ideal.span {f}) x • z := fun z => by
        rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, AlgEquiv.symm_apply_apply, ← Algebra.smul_def]
      rw [habar', h2]
      change Ideal.Quotient.mkₐ R _ (x • b) - _ = 0
      rw [map_smul, ← algebraMap_smul (R ⧸ Ideal.span {f}) x, Ideal.Quotient.algebraMap_eq]
      exact sub_eq_zero.mpr rfl
    obtain ⟨c, hc⟩ := hspan _ (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    exact ⟨c, by rw [← hc]; abel⟩
  have hdim1 : 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) := le_trans (by decide) hdimb
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.cokernel_torsion_of_finiteLength_mod_element R f hdim1 A B ψ hcok
  have hEtB : ∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B) :=
    fun p _ _ => inferInstance
  obtain ⟨k2, hk2⟩ := GlobalTheory.T.finiteLength_coker_of_etale_punctured_spectrum R A B hEt hEtB ψ hinj ⟨s, hs0, hs⟩
  have hdesc : ∀ (n : ℕ) (b : B), f ^ n • b ∈ ψ.range → b ∈ ψ.range := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      apply ih
      apply hfsat
      rwa [← mul_smul, ← pow_succ']
  have hsurj : Function.Surjective ψ := fun b => by
    obtain ⟨a, ha⟩ := hdesc k2 b (hk2 _ (Ideal.pow_mem_pow hf k2) b)
    exact ⟨a, ha⟩
  let eqv : A ≃ₐ[R] B := AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  haveI : Module.Free R A := Module.Free.of_equiv eqv.symm.toLinearEquiv
  haveI : Nontrivial A := by
    obtain ⟨rs, -, -, hr⟩ := hdep
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hr.top_ne_smul (Subsingleton.elim _ _)
  exact GlobalTheory.T.modDepthGE_three_of_free_regularLocal R hdim A

end GlobalTheory.LocalLefschetz
