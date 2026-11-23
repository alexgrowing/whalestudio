import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLatStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionMonoBase

open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.UPoinc

theorem mumBase_of_cdvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] : GlobalTheory.Mum.Base V :=
  ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

theorem uTrait_ramExt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : GlobalTheory.UPoinc.UTrait Xo c) (n : ℕ), 0 < n →
    ∃ (T₂ : GlobalTheory.UPoinc.UTrait Xo c) (g : T.V →+* T₂.V) (gK : FractionRing T.V →+* FractionRing T₂.V)
      (e : T.P.D.toPre.X ≃ₗ[𝓞 E] T₂.P.D.toPre.X) (q : ℕ), Function.Injective g ∧ IsLocalHom g ∧
      (∀ a, gK (algebraMap T.V _ a) = algebraMap T₂.V _ (g a)) ∧ T₂.y = spMap gK ≫ T.y ∧ 0 < q ∧
      ∀ a b, T₂.be (e a) (e b) = ((n * q : ℕ) : ℤ) * T.be a b := by
  intro E _ _ _ H Dw l Xo c T n hn
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : IsAdicComplete (maximalIdeal T.V) T.V := T.cdvr.2.1
  haveI : CharZero T.V := T.cdvr.2.2
  let T0 : Formalism.L2.Pj.CDVR := { V := T.V }
  obtain ⟨T₁, g₁, κ, e₁, ϖ₁, hg₁, hl₁, hϖ₁, hκ, hne₁, hass₁⟩ :=
    GlobalTheory.ArcExt.exists_ramified_ext T0 (Ω := AlgebraicClosure T0.Fr) ⊥ n hn T.ϖ T.irr
  let gK₁ : FractionRing T.V →+* FractionRing T₁.V :=
    κ.comp (algebraMap T0.Fr (⊥ : IntermediateField T0.Fr (AlgebraicClosure T0.Fr)))
  have hgK₁ : ∀ a, gK₁ (algebraMap T.V _ a) = algebraMap T₁.V _ (g₁ a) := hκ
  haveI : IsAdicComplete (maximalIdeal T₁.V) T₁.V := T₁.cpl
  have hB₁ : GlobalTheory.Mum.Base T₁.V := mumBase_of_cdvr T₁.V
  obtain ⟨T₂, f, fK, hf, hfl, -, hfK, hy⟩ :=
    GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c T₁.V hB₁ inferInstance (spMap gK₁ ≫ T.y)
  haveI : IsDiscreteValuationRing T₂.V := T₂.cdvr.1
  haveI : IsAdicComplete (maximalIdeal T₂.V) T₂.V := T₂.cdvr.2.1
  haveI : CharZero T₂.V := T₂.cdvr.2.2

  have hfϖ0 : f ϖ₁ ≠ 0 := fun h => hϖ₁.ne_zero (hf (by rw [h, map_zero]))
  obtain ⟨e₂, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfϖ0 T₂.irr
  have he₂ : 0 < e₂ := by
    rcases Nat.eq_zero_or_pos e₂ with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hu
      exact hϖ₁.not_isUnit ((isUnit_map_iff f ϖ₁).1 (hu ▸ u.isUnit))
    · exact h
  have he₁ : 0 < e₁ := by
    rcases Nat.eq_zero_or_pos e₁ with h | h
    · exfalso
      rw [h, pow_zero] at hass₁
      exact T.irr.not_isUnit ((isUnit_map_iff g₁ T.ϖ).1 (associated_one_iff_isUnit.1 hass₁))
    · exact h
  have hassf : Associated (f ϖ₁) (T₂.ϖ ^ e₂) := ⟨u⁻¹, by rw [hu, mul_comm (u : T₂.V), mul_assoc, Units.mul_inv, mul_one]⟩
  have hass : Associated ((f.comp g₁) T.ϖ) (T₂.ϖ ^ (e₁ * e₂)) := by
    have h1 : Associated (f (g₁ T.ϖ)) (f ϖ₁ ^ e₁) := by
      rw [← map_pow]; exact hass₁.map f
    rw [mul_comm, pow_mul]
    exact h1.trans (hassf.pow_pow)
  have hyc : spMap (fK.comp gK₁) ≫ T.y = spMap (RingHom.id (FractionRing T₂.V)) ≫ T₂.y := by
    have hid : spMap (RingHom.id (FractionRing T₂.V)) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [hy, hid, Category.id_comp, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl
  have hcomp : ∀ a, (fK.comp gK₁) (algebraMap T.V _ a) = algebraMap T₂.V _ ((f.comp g₁) a) := fun a => by
    simp only [RingHom.comp_apply]
    rw [hgK₁, hfK]
  obtain ⟨e, he⟩ := GlobalTheory.T.traitsOfModuliPoint_have_isomorphic_proportional_lattices E H Dw l Xo c T T₂ T₂.V (f.comp g₁) (RingHom.id T₂.V) (fK.comp gK₁)
    (RingHom.id _) (mumBase_of_cdvr T₂.V) inferInstance (hf.comp hg₁) Function.injective_id inferInstance
    inferInstance hcomp (fun _ => rfl) hyc T₂.ϖ (e₁ * e₂) 1 T₂.irr hass (by rw [pow_one]; rfl)
  obtain ⟨k, hk⟩ := hne₁
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk; omega
    · exact h
  refine ⟨T₂, f.comp g₁, fK.comp gK₁, e, k * e₂, hf.comp hg₁, inferInstance, hcomp, ?_, Nat.mul_pos hk0 he₂,
    fun a b => ?_⟩
  · rw [hy, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl
  · have h := he a b
    rw [Nat.cast_one, one_mul] at h
    rw [← h, hk, mul_assoc]

end GlobalTheory.UPoinc
