import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureFractionFiniteNormalCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.RingSide

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

def jMap (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂) :
    integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* M₂.Z.presheaf.stalk z₂ :=
  (M₂.stalkEquiv z₂).symm.toRingHom.comp ((RingHom.id Ω₂).restrict _ (M₂.O z₂) h)

theorem stalkHom_jMap (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) : M₂.stalkHom z₂ (jMap z₂ h b) = b := by
  rw [← RatModel.coe_stalkEquiv]
  simp [jMap]

theorem jMap_mem_max_iff (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (c : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) :
    jMap z₂ h c ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂) ↔ ¬ ((c : Ω₂) ≠ 0 ∧ (c : Ω₂)⁻¹ ∈ M₂.O z₂) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← MulEquiv.isUnit_map (M₂.stalkEquiv z₂).toMulEquiv, RatModel.isUnit_O_iff]
  change ¬ ((M₂.stalkEquiv z₂ (jMap z₂ h c) : Ω₂) ≠ 0 ∧ (M₂.stalkEquiv z₂ (jMap z₂ h c) : Ω₂)⁻¹ ∈ M₂.O z₂) ↔ _
  rw [RatModel.coe_stalkEquiv, stalkHom_jMap]

theorem algHom_mem_integralClosure
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x))
    (τ : Ω₂ →ₐ[Ω₁] Ω₂) {b : Ω₂} (hb : b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) :
    τ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ := by
  let τ' : Ω₂ →ₐ[M₁.Z.presheaf.stalk z₁] Ω₂ :=
    { τ.toRingHom with
      commutes' := fun x => by
        change τ (algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x) = algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x
        rw [halg]
        exact τ.commutes _ }
  exact IsIntegral.map τ' hb

theorem algHom_mem_O
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) {z₂ : M₂.Z}
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    (τ : Ω₂ →ₐ[Ω₁] Ω₂)
    (hu : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ → (τ s)⁻¹ ∈ M₂.O z₂)
    {x : Ω₂} (hx : x ∈ M₂.O z₂) : τ x ∈ M₂.O z₂ := by
  obtain ⟨b, hb, s, hs, hs0, hsO, rfl⟩ := hloc x hx
  rw [map_div₀, div_eq_mul_inv]
  exact mul_mem (hB _ (algHom_mem_integralClosure halg τ hb)) (hu s hs hs0 hsO)

end GlobalTheory.Poinc.RingSide

namespace GlobalTheory.Poinc.RingSide

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

theorem exists_stalk_ringEquiv
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) (z₂ : M₂.Z)
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (H : ∀ b b' : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, (b' : Ω₂) = σ b →
      (jMap z₂ hB b ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂) ↔ jMap z₂ hB b' ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂))) :
    ∃ σ₂ : M₂.Z.presheaf.stalk z₂ ≃+* M₂.Z.presheaf.stalk z₂, ∀ x, M₂.stalkHom z₂ (σ₂ x) = σ (M₂.stalkHom z₂ x) := by
  have hu : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ →
      (σ.toAlgHom s)⁻¹ ∈ M₂.O z₂ := by
    intro s hs hs0 hsO
    have hs' : σ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ :=
      algHom_mem_integralClosure halg σ.toAlgHom hs
    have key := H ⟨s, hs⟩ ⟨σ s, hs'⟩ rfl
    rw [jMap_mem_max_iff, jMap_mem_max_iff] at key
    exact ((not_iff_not.mp key).mp ⟨hs0, hsO⟩).2
  have hu' : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ →
      (σ.symm.toAlgHom s)⁻¹ ∈ M₂.O z₂ := by
    intro s hs hs0 hsO
    have ht : σ.symm s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ :=
      algHom_mem_integralClosure halg σ.symm.toAlgHom hs
    have key := H ⟨σ.symm s, ht⟩ ⟨s, hs⟩ (σ.apply_symm_apply s).symm
    rw [jMap_mem_max_iff, jMap_mem_max_iff] at key
    exact ((not_iff_not.mp key).mpr ⟨hs0, hsO⟩).2
  have hσ : ∀ x ∈ M₂.O z₂, σ x ∈ M₂.O z₂ := fun x hx =>
    algHom_mem_O halg hB hloc σ.toAlgHom hu hx
  have hσ' : ∀ x ∈ M₂.O z₂, σ.symm x ∈ M₂.O z₂ := fun x hx =>
    algHom_mem_O halg hB hloc σ.symm.toAlgHom hu' hx
  let e : M₂.O z₂ ≃+* M₂.O z₂ :=
    { toFun := fun x => ⟨σ x, hσ x x.2⟩
      invFun := fun x => ⟨σ.symm x, hσ' x x.2⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : Ω₂))
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : Ω₂))
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : Ω₂) y)
      map_add' := fun x y => Subtype.ext (map_add σ (x : Ω₂) y) }
  refine ⟨(M₂.stalkEquiv z₂).trans (e.trans (M₂.stalkEquiv z₂).symm), fun x => ?_⟩
  rw [← RatModel.coe_stalkEquiv, ← RatModel.coe_stalkEquiv]
  simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rfl

theorem injective_of_ext
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) {z₂ : M₂.Z}
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    {V V' : Type} [CommRing V] [CommRing V'] (ev : M₁.Z.presheaf.stalk z₁ →+* V) (io : V →+* V')
    (ev₂ : M₂.Z.presheaf.stalk z₂ →+* V') (hev : Function.Injective ev) (hio : Function.Injective io)
    (hE : ∀ x x₂, M₂.stalkHom z₂ x₂ = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x) → ev₂ x₂ = io (ev x)) :
    Function.Injective ev₂ := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  by_contra hy0
  have hY : M₂.stalkHom z₂ y ≠ 0 := by
    intro h
    apply hy0
    apply M₂.stalkHom_injective z₂
    rw [h, map_zero]
  have hYO : M₂.stalkHom z₂ y ∈ M₂.O z₂ := by
    rw [← RatModel.coe_stalkEquiv]
    exact (M₂.stalkEquiv z₂ y).2
  obtain ⟨b, hb, s, hs, hs0, -, hYe⟩ := hloc _ hYO
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_div] at hYe
    exact hY hYe
  have hjb : jMap z₂ hB ⟨b, hb⟩ = y * jMap z₂ hB ⟨s, hs⟩ := by
    apply M₂.stalkHom_injective z₂
    rw [map_mul, stalkHom_jMap, stalkHom_jMap, hYe]
    exact (div_mul_cancel₀ b hs0).symm
  have hev0 : ev₂ (jMap z₂ hB ⟨b, hb⟩) = 0 := by
    rw [hjb, map_mul, hy, zero_mul]
  have hbB : (⟨b, hb⟩ : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) ≠ 0 := fun h =>
    hb0 (congrArg Subtype.val h)
  have hne := Ideal.comap_ne_bot_of_integral_mem hbB (Ideal.mem_span_singleton_self _)
    (integralClosure.isIntegral _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, hc⟩ := ha
  have h1 : ev₂ (jMap z₂ hB (algebraMap _ _ a)) = io (ev a) := by
    apply hE
    rw [stalkHom_jMap]
    exact halg a
  have h2 : ev₂ (jMap z₂ hB (algebraMap _ _ a)) = 0 := by
    rw [← hc, map_mul, map_mul, hev0, mul_zero]
  rw [h2] at h1
  have h3 : ev a = ev 0 := hio (by rw [map_zero, map_zero, ← h1])
  exact ha0 (hev h3)

end GlobalTheory.Poinc.RingSide

open GlobalTheory.Poinc.RingSide in

theorem GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  intro g n F W Z i X₁ act 𝔗 z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ :=
    ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  have halg : ∀ x, algebraMap (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ x =
      algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom z₁ x) := fun _ => rfl
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme 𝔗.X₂.M.Z := by
    exact @GlobalTheory.IsNormalScheme.pred _ 𝔗.X₂.normal
  obtain ⟨𝔷, h𝔷⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁)
  obtain ⟨z₂, hz₂, hmem⟩ := GlobalTheory.Poinc.FinPts.maximal_point hN 𝔗.p_fin 𝔗.p_pt halg 𝔷 h𝔷
  have hB : ∀ b ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, b ∈ 𝔗.X₂.M.O z₂ :=
    fun b hb => GlobalTheory.Poinc.FinPts.mem_O_of_isIntegral hN 𝔗.p_pt halg hb hz₂
  have hloc := GlobalTheory.Poinc.exists_div_integralClosure_of_mem_O _ _ _ _ X₁.M 𝔗.X₂.M 𝔗.p hN
    𝔗.p_fin 𝔗.p_pt z₁ z₂ hz₂
  refine ⟨z₂, jMap z₂ hB, hz₂, fun b => stalkHom_jMap z₂ hB b, ?_, ?_, ?_, ?_⟩
  · have hc : (maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap (jMap z₂ hB) = 𝔷 := by
      ext c
      rw [Ideal.mem_comap, jMap_mem_max_iff, hmem c]
      tauto
    rw [hc]
    exact h𝔷
  · intro x hx
    exact GlobalTheory.Poinc.FinPts.isIntegral_of_mem_O 𝔗.p_fin 𝔗.p_pt halg hx
  · intro σ H
    exact exists_stalk_ringEquiv halg z₂ hB hloc σ H
  · intro V _ ev V' _ io ev₂ hev hio hE
    exact injective_of_ext halg hB hloc ev io ev₂ hev hio hE.2
