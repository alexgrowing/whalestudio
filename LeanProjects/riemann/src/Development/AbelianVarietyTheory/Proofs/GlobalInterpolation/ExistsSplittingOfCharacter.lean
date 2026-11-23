import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTensorCoord

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OverSplit

theorem ker_isMaximal {A : Type} [CommRing A] {T : ℕ} [Fact T.Prime] (ψ : A →+* ZMod T) :
    (RingHom.ker ψ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective ψ (ZMod.ringHom_surjective ψ)

theorem exists_roots {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {T : ℕ} [Fact T.Prime] (ψ : O →+* ZMod T)
    (p n : O) (x y : ZMod T) (hp : ψ p = x + y) (hn : ψ n = x * y) (hxy : x ≠ y) :
    ∃ r r' : O, r + r' = p ∧ r * r' = n ∧ ψ r = x ∧ ψ r' = y ∧ IsUnit (r - r') := by
  have hk : ∀ z, z ∈ IsLocalRing.maximalIdeal O ↔ ψ z = 0 := fun z => by
    rw [← IsLocalRing.eq_maximalIdeal (ker_isMaximal ψ), RingHom.mem_ker]
  have hu : ∀ z, ψ z ≠ 0 → IsUnit z := fun z hz => by
    by_contra h
    exact hz ((hk z).1 h)
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective ψ x
  have hxy' : x - y ≠ 0 := sub_ne_zero.2 hxy
  obtain ⟨r, hr, hra⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal O)
    (Polynomial.X ^ 2 - Polynomial.C p * Polynomial.X + Polynomial.C n) (by monicity!) a
    (by rw [hk]; simp [ha, hp, hn]; ring)
    (by
      refine IsUnit.map _ (hu _ ?_)
      have : ψ (Polynomial.eval a (Polynomial.derivative
          (Polynomial.X ^ 2 - Polynomial.C p * Polynomial.X + Polynomial.C n))) = x - y := by
        simp [ha, hp]; ring
      rwa [this])
  have hrx : ψ r = x := by
    rw [hk, map_sub, ha, sub_eq_zero] at hra; exact hra
  have hr' : r ^ 2 - p * r + n = 0 := by simpa using hr
  have hry : ψ (p - r) = y := by rw [map_sub, hp, hrx]; ring
  refine ⟨r, p - r, by ring, by linear_combination -hr', hrx, hry, hu _ ?_⟩
  rwa [map_sub, hrx, hry]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def inclO (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletionIntegers F →+* intV E v :=
  RingHom.codRestrict
    ((Algebra.TensorProduct.includeRight (R := F) (A := E) (B := v.adicCompletion F)).toRingHom.comp
      (v.adicCompletionIntegers F).subtype) _
    fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)

theorem coe_inclO (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletionIntegers F) :
    ((inclO E v a : intV E v) : E ⊗[F] v.adicCompletion F) =
      (1 : E) ⊗ₜ[F] (a : v.adicCompletion F) := rfl

theorem exists_inclO_eq (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 E)
    (hx : (x : E) ∈ (algebraMap F E).range) :
    ∃ p : v.adicCompletionIntegers F, inclO E v p = GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v x := by
  obtain ⟨b, hb⟩ := hx
  have hi : IsIntegral ℤ b := by
    rw [← isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective, hb]
    exact x.isIntegral_coe
  let b' : 𝓞 F := ⟨b, hi⟩
  have hx' : x = algebraMap (𝓞 F) (𝓞 E) b' := by
    apply Subtype.ext
    exact hb.symm
  refine ⟨algebraMap (𝓞 F) _ b', Subtype.ext ?_⟩
  rw [coe_inclO, GlobalTheory.OverCompare.coe_toIntV, hx', GlobalTheory.OverCompare.tmul_algebraMap]
  rfl

end GlobalTheory.OverSplit

open GlobalTheory.OverSplit in

theorem GlobalTheory.OverSplit.exists_splitting_of_character :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) → ∀ (v : HeightOneSpectrum (𝓞 F)) (T : ℕ), T.Prime → ∀ χ : intV E v →+* ZMod T, ∃ s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F, IsSplitting σ v s ∧ ∀ a : intV E v, Valued.v (prP s a) < 1 → χ a = 0 := by
  intro F E _ _ _ _ _ σ hdeg hσ hfix hunr v T hT χ
  have : Fact T.Prime := ⟨hT⟩
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set ι := GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v with hι
  obtain ⟨θ, t, ht, hθt⟩ := hunr _ (ker_isMaximal (χ.comp ι))
  have hxy : χ (ι θ) ≠ χ (ι t) := by
    intro h
    apply hθt
    rw [RingHom.mem_ker, map_sub, RingHom.comp_apply, RingHom.comp_apply, h, sub_self]
  have e1 : ((θ + t : 𝓞 E) : E) = θ + σ θ := by rw [← ht]; rfl
  have e2 : ((θ * t : 𝓞 E) : E) = θ * σ θ := by rw [← ht]; rfl
  obtain ⟨p, hp⟩ := exists_inclO_eq v (θ + t) (hfix _ (by rw [e1, map_add, hσ, add_comm]))
  obtain ⟨n, hn⟩ := exists_inclO_eq v (θ * t) (hfix _ (by rw [e2, map_mul, hσ, mul_comm]))
  obtain ⟨r, r', hs, hm, hr, hr', hu⟩ := exists_roots (χ.comp (inclO E v)) p n (χ (ι θ)) (χ (ι t))
    (by rw [RingHom.comp_apply, hp, map_add, map_add])
    (by rw [RingHom.comp_apply, hn, map_mul, map_mul]) hxy
  obtain ⟨s, hsp, hsθ⟩ := GlobalTheory.RootSplitting.exists_isSplitting F E σ hdeg hσ hfix v θ r r' θ.isIntegral_coe hu
    (by
      have := congrArg Subtype.val hp
      rw [← e1]
      refine this.symm.trans ?_
      rw [← hs]; rfl)
    (by
      have := congrArg Subtype.val hn
      rw [← e2]
      refine this.symm.trans ?_
      rw [← hm]; rfl)
  refine ⟨s, hsp, fun a ha => ?_⟩
  let a₁ : v.adicCompletionIntegers F := ⟨(s a).1, ((hsp.2.2 a).1 a.2).1⟩
  have ha₁ : χ (inclO E v a₁) = 0 := by
    have h1 : a₁ ∈ IsLocalRing.maximalIdeal _ :=
      (ValuationSubring.valuation_lt_one_iff _ _).2
        ((Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one.1 ha)
    rw [← IsLocalRing.eq_maximalIdeal (ker_isMaximal (χ.comp (inclO E v)))] at h1
    exact h1
  have key : (ι θ - inclO E v r') * a = (ι θ - inclO E v r') * inclO E v a₁ := by
    apply Subtype.ext
    apply s.injective
    have h0 : s ((ι θ - inclO E v r' : intV E v) : E ⊗[F] v.adicCompletion F) =
        ((r : v.adicCompletion F) - r', 0) := by
      rw [AddSubgroupClass.coe_sub, map_sub, coe_inclO, hsp.1, hι, GlobalTheory.OverCompare.coe_toIntV, hsθ]
      simp
    rw [Subring.coe_mul, Subring.coe_mul, map_mul, map_mul, h0, coe_inclO, hsp.1]
    ext <;> simp [a₁]
  have := congrArg χ key
  rw [map_mul, map_mul, ha₁, mul_zero, map_sub] at this
  have hr'' : χ (inclO E v r') = χ (ι t) := hr'
  rw [hr''] at this
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hxy)

end
