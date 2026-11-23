import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.mem_supI_iff_and_HH_eq_ker :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) := by
  intro o Ω _ _ _ _ S M U₀ hO z p _ y y₀ τ hC hA
  have hw : Set.range (gPt p ≫ y) = {(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))} :=
    RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))
  have hξ : (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ (U₀ : Set M.Z) := hC.2 ⟨_, rfl⟩
  have hsp := RatModel.specializes_of_range_eq hw
  have hthO : ∀ j, S.th j ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) :=
    fun j => RatModel.ringOn_le_O hξ (hO.le (S.th_mem j))
  have hinvO : ∀ j, S.th j ≠ 0 →
      (S.th j)⁻¹ ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) :=
    fun j hj => RatModel.ringOn_le_O hξ (hO.th_unit j hj)
  have hmul : ∀ i j, S.th i ≠ 0 → M.val (gPt p ≫ y) (S.th j) =
      M.val (gPt p ≫ y) (S.th j / S.th i) * M.val (gPt p ≫ y) (S.th i) := by
    intro i j hi
    have hq : S.th j / S.th i ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
      rw [div_eq_mul_inv]; exact mul_mem (hthO j) (hinvO i hi)
    rw [← RatModel.val_mul hsp hq (hthO i), div_mul_cancel₀ _ hi]
  have hval : ∀ x, ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = ‖M.val (gPt p ≫ y) (S.th x)‖ := fun x => by rw [hA]
  have hmax : IsGreatest (Set.range fun x => ‖M.val (gPt p ≫ y) (S.th x)‖) τ.δ := by
    simpa only [hval] using τ.δ_max
  have fwd : ∀ x, M.Div S.th x z → ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x hx
    apply le_antisymm (hmax.2 ⟨x, rfl⟩)
    obtain ⟨j, hj⟩ := hmax.1
    rw [← hj]
    dsimp only
    rw [hmul x j hx.1, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.Cen.norm_val_le_one hC (hx.2 j))
  have key : ∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x
    refine ⟨fun h => fwd x h, fun hx => ?_⟩
    obtain ⟨i, hi⟩ := hO.div z
    have h1 : ‖M.val (gPt p ≫ y) (S.th x / S.th i)‖ = 1 := by
      rw [hmul i x hi.1, norm_mul, fwd i hi] at hx
      have h2 : ‖M.val (gPt p ≫ y) (S.th x / S.th i)‖ * τ.δ = 1 * τ.δ := by rw [_root_.one_mul]; exact hx
      exact (mul_left_inj' τ.δ_pos.ne').mp h2
    show M.Div S.th x z
    exact (RatModel.Div.div_iff_isUnit hi x).mpr ((RatModel.norm_val_eq_one_iff hC.1 (hi.2 x)).mp h1)
  refine ⟨key, ?_⟩
  rw [← τ.supp]
  show AddSubgroup.closure (S.supI M z) = _
  congr 1
  ext x
  rw [key x, Set.mem_ofPred_eq, hval]

end GlobalTheory.ZH
