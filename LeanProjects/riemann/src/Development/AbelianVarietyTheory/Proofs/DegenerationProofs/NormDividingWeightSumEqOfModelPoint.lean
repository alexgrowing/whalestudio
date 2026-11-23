import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory

theorem norm_val_FF_eq_of_div :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) := by
  intro o Ω _ _ _ _ S M U₀ hO h0 h1 _ z p _ y y₀ τ hC hA
  have hT : S.TT M z = S.perp τ.yy.ker := by
    rw [ThetaSys.TT, (h0 z p y y₀ τ hC hA).2]
  obtain ⟨hmem, -, hpp, -⟩ := thetaSys_FF_mem_finite_perp_proj o Ω S
  rw [hT]
  intro c k α hdiv hα hc
  have hcw : c = τ.wt α := AddMonoidHom.ext fun t => hc t.1 t.2 t.2
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [hA]
    exact hC.norm_val_le_one ((M.O z).algebraMap_mem a)
  have hk : M.val (gPt p ≫ y) (S.FF _ c k) = y₀ ⟨_, hmem _ c k⟩ := (hA ⟨_, hmem _ c k⟩).symm
  refine le_antisymm ?_ ?_
  · rw [hk]
    exact (h1 p y₀ τ hint _ c k (hmem _ c k) τ.isoFree).1 le_rfl
      (τ.isoFree.1.trans (hpp _).le) α hα hc
  · subst hcw
    obtain ⟨k₁, hk₁, he⟩ := τ.eq α hα
    rw [← he, hA]
    let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    have hw : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w := fun w' => by
      have : (gPt p ≫ y) w' ∈ Set.range (gPt p ≫ y) := ⟨w', rfl⟩
      rw [RatModel.range_eq_singleton _ w] at this
      rw [this]
    have hU : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hC.2 ⟨w, rfl⟩
    have hq := hdiv.2 k₁
    have hmul := RatModel.val_mul hw
      (RatModel.O_le_of_specializes (RatModel.gPt_specializes hC.1 w) hq)
      (RatModel.ringOn_le_O hU (hO.le (hmem _ (τ.wt α) k)))
    rw [div_mul_cancel₀ _ hdiv.1] at hmul
    change ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k₁)‖ ≤ _
    rw [hmul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hC.norm_val_le_one hq)

end GlobalTheory
