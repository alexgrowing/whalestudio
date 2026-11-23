import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory.Ord2

private theorem locEmb_conj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, (∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A) ∧
      (∀ τ ∈ Dec (F := k) B, g⁻¹ * τ * g ∈ Dec (F := k) A) ∧
      ∀ τ ∈ Dec (F := k) A, g * τ * g⁻¹ ∈ Dec (F := k) B := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := k) hA hB
  have h : IsLift (RingEquiv.refl k) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have hm' : ∀ x, g.toRingEquiv.symm x ∈ A ↔ x ∈ B := fun x => by
    rw [← hm, RingEquiv.apply_symm_apply]
  exact ⟨g, fun τ hτ => conjGal_mem_Ine h hm hτ, fun τ hτ => conjGal_mem_Dec h hm hτ,
    fun τ hτ => conjGal_mem_Dec h.symm hm' hτ⟩

theorem bk_locEmb : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (A : ValuationSubring Ω), OverL l A → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → ∃ ι : GQ l →* G ℚ Ω, Continuous ι ∧ (∀ σ, ι σ ∈ Dec (F := ℚ) A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∃ σ, ι σ = s) ∧ (∀ σ ∈ Loc.Iq l, ι σ ∈ Ine (F := ℚ) A) ∧ (∀ σ, cycZ ℚ Ω l (ι σ) = Loc.cyc l l σ) ∧ (fun σ => z (ι σ)) ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
  intro l _ Ω _ iA _ W A hA z hz hb
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨v, hAv, hv⟩ := hA
  obtain ⟨j, -, -, x, hx⟩ := hb.above (algebraMap ℚ (Om l))
  obtain ⟨i1, i2, -, i4, i5, i6, -⟩ := Loc.iotaFacts j
  have h0 : (fun σ => z (Loc.iota j σ)) ∈
      Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp (Loc.iota j)) :=
    ⟨⟨hz.1.comp i1.continuous, fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩, x,
      fun σ => hx ⟨(Loc.iota j σ, σ), fun y => (Loc.iota_spec j σ y).symm⟩⟩
  obtain ⟨g, g1, g2, g3⟩ := locEmb_conj hAv ((i6 v).2 hv)
  let ι : GQ l →* G ℚ Ω := (MulAut.conj g⁻¹).toMonoidHom.comp (Loc.iota j)
  have hι : ∀ σ, ι σ = g⁻¹ * Loc.iota j σ * g := fun σ => by simp [ι]
  have hc : Continuous ι := by
    have : (ι : GQ l → G ℚ Ω) = fun σ => g⁻¹ * Loc.iota j σ * g := funext hι
    rw [this]
    exact (continuous_const.mul i1.continuous).mul continuous_const
  refine ⟨ι, hc, fun σ => ?_, fun s hs => ?_, fun σ hσ => ?_, fun σ => ?_, ?_⟩
  · rw [hι]
    exact g2 _ (by rw [← i2]; exact ⟨σ, rfl⟩)
  · have h1 : g * s * g⁻¹ ∈ Dec (F := ℚ) (Loc.placeJ j) := g3 s hs
    rw [← i2] at h1
    obtain ⟨σ, hσ⟩ := h1
    exact ⟨σ, by rw [hι, hσ]; group⟩
  · rw [hι]
    exact g1 _ (by rw [← i4]; exact ⟨σ, hσ, rfl⟩)
  · rw [hι, map_mul, map_mul, map_inv, mul_comm _ (cycZ ℚ Ω l (Loc.iota j σ)), inv_mul_cancel_right]
    exact DFunLike.congr_fun (i5 l) σ
  · have h1 := Loc.z1fCoef (MonoidHom.id (GQ l)) ((Loc.colRep W).comp (Loc.iota j)) ((Loc.colRep W).comp ι)
      ((Loc.colRep W g⁻¹).restrictScalars ℚ_[l]) (LinearMap.continuous_on_pi (Loc.colRep W g⁻¹))
      (fun σ y => by
        show Loc.colRep W g⁻¹ (Loc.colRep W (Loc.iota j σ) y) = Loc.colRep W (ι σ) (Loc.colRep W g⁻¹ y)
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hι, mul_inv_cancel_right]) _ h0
    have hcob : ∀ σ, Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹ = z (ι σ * g⁻¹) - z (ι σ) - z g⁻¹ := fun σ => by
      rw [hz.2]; abel
    have h2 : (fun σ => Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹) ∈
        Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
      refine ⟨⟨?_, fun a b => ?_⟩, z g⁻¹ ⊗ₜ 1, fun σ => ?_⟩
      · rw [funext hcob]
        exact ((hz.1.comp (hc.mul continuous_const)).sub (hz.1.comp hc)).sub continuous_const
      · show Loc.colRep W (ι (a * b)) (z g⁻¹) - z g⁻¹ = Loc.colRep W (ι a) (z g⁻¹) - z g⁻¹ +
          Loc.colRep W (ι a) (Loc.colRep W (ι b) (z g⁻¹) - z g⁻¹)
        rw [map_mul, map_mul, Module.End.mul_apply, map_sub]; abel
      · simp [Loc.actC, TensorProduct.sub_tmul]
    have h3 := Submodule.sub_mem _ h1 h2
    convert h3 using 1
    funext σ
    show z (ι σ) = Loc.colRep W g⁻¹ (z (Loc.iota j σ)) - (Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹)
    have e1 := hz.2 g⁻¹ (Loc.iota j σ)
    rw [hcob, hι, mul_inv_cancel_right, e1]
    abel

end GlobalTheory.Ord2
