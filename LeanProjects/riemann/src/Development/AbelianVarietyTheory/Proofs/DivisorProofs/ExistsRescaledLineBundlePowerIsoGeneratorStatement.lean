import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLineBundlePowerIsoGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescaled_lineBundlePower_iso_generator : ∀ {T X Z₀ Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (eL : Z₀ ⟶ Z₁) (eM : Z₀ ⟶ Z₂) (t : T ⟶ Z₀) (z : T ⟶ X) (π : X ⟶ T) (k : ℕ) (eA : LB.Gen (L.pull eL)) (eB : LB.Gen (M.pull eM)) (α₀ : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ)))), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → α₀.IsGen → z ≫ π = 𝟙 T → z ≫ f = t ≫ eL → z ≫ g = t ≫ eM → ∃ α : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen ∧ ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (z.appLE ((LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_left)).hom (α.s p).val * ((t.appLE (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k = ((t.appLE (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  first | (exact @GlobalTheory.RigNorm.exists_rescaled_gen) | (exact GlobalTheory.RigNorm.exists_rescaled_gen) | (intros; apply GlobalTheory.RigNorm.exists_rescaled_gen  <;> assumption)
