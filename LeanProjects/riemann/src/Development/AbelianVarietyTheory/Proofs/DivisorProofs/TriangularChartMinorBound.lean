import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorsTriangularChangeInvariantStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical
set_option autoImplicit false

theorem GlobalTheory.ConstLat.CramerFrame.unitAt_genAt_mul_frameC : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (W : Y.X.Opens) (p : ℕ), p.Prime → genericPoint Y.X ∈ W → ∀ {g : ℕ} {C : CxSt F} (A : Fin g → Adl C Y) (U' : V.X.Opens) (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (σ : ∀ k : ℕ, Fin k → Fin (g + g)), (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) → ChartReg V U' H T → (∀ (k : ℕ) (hk : k ≤ g), minorAt H k hk (σ k) ≠ 0) → (∀ z : V.G, V.j z ∈ U' → ∀ (k : ℕ) (hk : k ≤ g), UnitAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk (σ k))) → (AtTest V W p fun _ e y z yt => ⊤ ≤ yt ⁻¹ᵁ U' → ∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)), e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ) ≤ e.w (minorAt (valMat V H (T (below y.1)) z) k hk (σ k))) → (∀ i y, UnitAt y (genAt (A i).D y * d y i)) → ∀ (i : Fin g) (z : V.G), V.j z ∈ U' → UnitAt z (V.φ (genAt (A i).D (V.π z)) * (frameC H σ i : V.G.functionField)) := by
  intro F _ _ Y V W p _ _ g C A U' H d T σ hT _ _ hU _ hgen i z hz
  have hdiag : ∀ k, ((T (V.π z)).map V.φ) k k = V.φ (d (V.π z) k : Y.Fn) := fun k => by
    rw [Matrix.map_apply, (hT _).2 k]
  have htri : ((T (V.π z)).map V.φ).BlockTriangular id := fun a b hab => by
    rw [Matrix.map_apply, (hT _).1 hab, map_zero]
  have hne : ∀ k, ((T (V.π z)).map V.φ) k k ≠ 0 := fun k => by
    rw [hdiag k]
    exact (map_ne_zero V.φ).2 (d (V.π z) k).ne_zero
  have hC := (GlobalTheory.T.minors_triangular_change_invariant H _ htri hne σ).2.2 (fun k hk => (hU z hz k hk).ne_zero) i
  rw [hC, hdiag, div_eq_mul_inv, ← mul_assoc, ← mul_assoc, ← map_mul]
  exact ((V.unitAt_φ (hgen i (V.π z))).mul (hU z hz _ _)).mul (hU z hz _ _).inv
