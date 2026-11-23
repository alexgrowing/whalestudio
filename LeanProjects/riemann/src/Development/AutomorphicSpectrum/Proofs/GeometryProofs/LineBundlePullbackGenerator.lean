import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem exists_sec_cleared : ∀ {R Rm : Type} [CommRing R] [CommRing Rm] [Algebra R Rm] (Mn : Submonoid R) [IsLocalization Mn Rm] {X X' Y : Scheme.{0}} {π : X' ⟶ Spec (CommRingCat.of R)} {π' : Y ⟶ Spec (CommRingCat.of Rm)} {κ : Y ⟶ X'}, IsPullback κ π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) → ∀ [CompactSpace X'] [QuasiSeparatedSpace X'] {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}, PGen w → L.IsLB → L'.IsLB → ∀ (th : Out.H0 L 1) (ψ : Y ⟶ X) (n : ℕ) (u : FG L Y), (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), u.sum U h = h ψ * (h (κ ≫ F) ^ n)⁻¹) → ∃ (s : Out.H0 L' n), ∃ t ∈ Mn, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' → (gw w (r ≫ κ) z (J ((r ≫ κ) ≫ F)) (J' (r ≫ κ)) ^ n).val * sval s (r ≫ κ) z J' = GlobalTheory.TwistLoc.gc (r ≫ κ ≫ π) z t * (sval th (r ≫ ψ) z J * ((u.v r z J)⁻¹).val) := by
  intro R Rm _ _ _ Mn _ X X' Y π π' κ H _ _ L L' F w hw hL hL' th ψ n u hu
  have fe : FormEq (Sum.elim (fun k : Fin 1 => ψ ≫ (fun _ : Fin 1 => 𝟙 X) k) u.inv.φ)
      (Sum.elim (fun _ : Fin 1 => ((1 : ℕ) : ℤ)) u.inv.ε)
      (fun _ : Fin 1 => κ ≫ 𝟙 X' ≫ F) (fun _ : Fin 1 => (n : ℤ)) := fun U _ h => by
    have e := FG.sum_inv U u h
    rw [hu U h] at e
    have e' : ∏ k, h (u.inv.φ k) ^ u.inv.ε k = (h ψ * (h (κ ≫ F) ^ n)⁻¹)⁻¹ := e
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, e', Fintype.prod_unique, Category.comp_id, Category.id_comp, Nat.cast_one,
      zpow_one, zpow_natCast, mul_inv, inv_inv, mul_inv_cancel_left]
  obtain ⟨s', hs'⟩ := exists_sec hL fe (pullMulSec th ψ u.inv.t u.inv.ht)
  obtain ⟨t, ht, σ, hσ⟩ := GlobalTheory.TwistLoc.exists_clear_denominator Mn H hL (fun _ : Fin 1 => 𝟙 X' ≫ F)
    (fun _ => (n : ℤ)) s'
  obtain ⟨a, ha⟩ := GlobalTheory.SecPull.exists_down_sec hw hL hL' (fun _ : Fin 1 => 𝟙 X') (fun _ : Fin 1 => 𝟙 X' ≫ F)
    (fun _ => (n : ℤ)) (𝟙 X') (fun _ => by simp) σ
  refine ⟨a, t, ht, fun Z r z J J' hJ hJ' => ?_⟩
  let p : Fin 1 → L.ι := fun _ => J ((r ≫ κ) ≫ F)
  let q : Fin 1 → L'.ι := fun _ => J' (r ≫ κ)
  have m₁ : (r ≫ κ) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X' ≫ F) p :=
    Set.mem_iInter.2 fun _ => hJ ((r ≫ κ) ≫ F)
  have m₂ : (r ≫ κ) z ∈ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') q := Set.mem_iInter.2 fun _ => hJ' (r ≫ κ)
  have m₃ : r z ∈ LB.wchart L (fun _ : Fin 1 => κ ≫ 𝟙 X' ≫ F) p :=
    Set.mem_iInter.2 fun _ => hJ ((r ≫ κ) ≫ F)
  have e₁ := ha Z (r ≫ κ) z p q m₁ m₂
  rw [Category.comp_id] at e₁
  have e₂ := hσ Z r z p m₃
  have e₃ : pw w (fun _ : Fin 1 => 𝟙 X') (fun _ => (n : ℤ)) (r ≫ κ) z p q = gw w (r ≫ κ) z (J ((r ≫ κ) ≫ F)) (J' (r ≫ κ)) ^ n := by
    simp only [pw, Fintype.prod_unique, Category.comp_id, zpow_natCast, p, q]
  have e₄ : sval s' r z J = gs r z (LB.wchart L (fun _ : Fin 1 => κ ≫ 𝟙 X' ≫ F) p) (s'.f p) := sval_of s' r z J p fun _ => by
    simp only [p, Category.assoc, Category.id_comp]
  rw [sval_of a (r ≫ κ) z J' q (fun _ => by simp only [q, Category.comp_id]), ← e₃, e₁, ← _root_.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, _root_.one_mul, e₂, ← e₄, hs' Z r z J hJ,
    sval_pullMulSec _ _ _ _ r z hJ, show val u.inv.t r z J = (u.v r z J)⁻¹ from FG.v_inv u r]

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
