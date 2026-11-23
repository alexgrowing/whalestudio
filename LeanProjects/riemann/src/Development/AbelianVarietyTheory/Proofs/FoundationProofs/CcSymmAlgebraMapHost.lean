import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped Pointwise

namespace GlobalTheory.AntiRamConj

section General
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]

def moveVal (c : Ω ≃+* Ω) (B : ValuationSubring Ω) : ValuationSubring Ω :=
  B.comap (c.symm : Ω →+* Ω)

theorem mem_moveVal (c : Ω ≃+* Ω) (B : ValuationSubring Ω) (y : Ω) :
    y ∈ moveVal c B ↔ c.symm y ∈ B := Iff.rfl

theorem moveVal_lt_one (c : Ω ≃+* Ω) (B : ValuationSubring Ω) (y : Ω) :
    (moveVal c B).valuation y < 1 ↔ B.valuation (c.symm y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', mem_moveVal, mem_moveVal, map_inv₀,
    map_eq_zero_iff _ c.symm.injective]

def conjAut (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (σ : G E Ω) : G E Ω :=
  { (c.symm.trans (σ : Ω ≃+* Ω)).trans c with
    commutes' := fun x => by
      obtain ⟨y, hy⟩ := hc x
      show c (σ (c.symm (algebraMap E Ω x))) = algebraMap E Ω x
      rw [hy, σ.commutes, ← hy, RingEquiv.apply_symm_apply] }

theorem conjAut_apply (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) (σ : G E Ω) (x : Ω) :
    conjAut c hc σ x = c (σ (c.symm x)) := rfl

theorem conjAut_mem_ine [NumberField E] (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) {B : ValuationSubring Ω}
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) : conjAut c hc σ ∈ Ine (F := E) (moveVal c B) := by
  have hd : σ ∈ Dec (F := E) B := hσ.1
  refine ⟨?_, fun x hx => ?_⟩
  · show conjAut c hc σ ∈ Dec (F := E) (moveVal c B)
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    obtain ⟨z, rfl⟩ := (conjAut c hc σ).surjective x
    have h1 : ((conjAut c hc σ)⁻¹ : G E Ω) (conjAut c hc σ z) = z := (conjAut c hc σ).symm_apply_apply z
    rw [h1, mem_moveVal, mem_moveVal, conjAut_apply, RingEquiv.symm_apply_apply,
      apply_mem_iff_of_mem_Dec hd]
  · rw [moveVal_lt_one, map_sub, conjAut_apply, RingEquiv.symm_apply_apply]
    apply hσ.2
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact hx

end General

theorem host_conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  let φ : D.host.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := fun y => D.host.conjE_apply φ y
  exact (h _).trans ((congrArg (starRingEnd ℂ) (h x)).trans (Complex.conj_conj _))

theorem cc_algebraMap_host (D : D7) (x : D.host.E) :
    D.ntw.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x) := by
  obtain ⟨j, hj⟩ := D.ntw.cc_cm.1
  apply j.injective
  rw [hj]
  exact (D.host.conjE_apply
    (j.comp (algebraMap D.host.E D.nd.Om)) x).symm

theorem cc_symm_algebraMap_host (D : D7) (x : D.host.E) :
    D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x) := by
  rw [RingEquiv.symm_apply_eq, cc_algebraMap_host, host_conj_conj]

theorem isPlaceOver_moveVal (D : D7) {P P' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : IsConjPl D.host P P') {B : ValuationSubring D.nd.Om} (hB : IsPlaceOver B P) :
    IsPlaceOver (moveVal D.ntw.cc B) P' := by
  intro y
  have hi : IsIntegral ℤ (D.host.conj (y : D.host.E)) :=
    (y.isIntegral_coe).map_of_comp_eq (RingHom.id ℤ) (D.host.conj : D.host.E →+* D.host.E) (by ext; simp)
  let x : 𝓞 D.host.E := ⟨_, hi⟩
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := rfl
  rw [moveVal_lt_one, cc_symm_algebraMap_host, ← hx, hB x]
  exact h x y (by rw [hx, host_conj_conj])

end GlobalTheory.AntiRamConj
