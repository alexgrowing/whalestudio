import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureGaloisStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureFractionFiniteNormalCover
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

open GlobalTheory.Poinc.RingSide in

theorem GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  intro I X₁ act 𝔗 z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  have halg : ∀ x, algebraMap (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ x =
      algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom z₁ x) := fun _ => rfl
  have hnorm := (GlobalTheory.isNormalScheme_iff_pred _).1 𝔗.X₂.normal
  obtain ⟨h1, h2, -, -⟩ := integralClosure_stalk_fibre X₁.o₁ X₁.Ω₁ 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ X₁.M 𝔗.X₂.M 𝔗.p hnorm
    𝔗.p_fin 𝔗.p_pt z₁
  obtain ⟨𝔷, h𝔷⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁)
  obtain ⟨z₂, hz₂, h𝔷z⟩ := h2 𝔷 h𝔷
  have hB : ∀ b ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, b ∈ 𝔗.X₂.M.O z₂ :=
    fun b hb => (h1 b).1 hb z₂ hz₂
  have hloc := GlobalTheory.Poinc.exists_div_integralClosure_of_mem_O X₁.o₁ X₁.Ω₁ 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ X₁.M 𝔗.X₂.M 𝔗.p hnorm
    𝔗.p_fin 𝔗.p_pt z₁ z₂ hz₂
  have hcomap : (maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap (jMap z₂ hB) = 𝔷 := by
    ext b
    rw [Ideal.mem_comap, jMap_mem_max_iff, h𝔷z]
    tauto
  refine ⟨z₂, jMap z₂ hB, hz₂, stalkHom_jMap z₂ hB, hcomap ▸ h𝔷, fun x hx => (h1 x).2 hx,
    fun σ H => exists_stalk_ringEquiv halg z₂ hB hloc σ H,
    fun V _ ev V' _ io ev₂ hev hio hE => injective_of_ext halg hB hloc ev io ev₂ hev hio hE.2⟩
