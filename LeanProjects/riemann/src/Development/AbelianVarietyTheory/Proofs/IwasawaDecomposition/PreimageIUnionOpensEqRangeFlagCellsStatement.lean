import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCells
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_iUnion_opens_eq_range_flagCells : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (F Z : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)) (j : F ⟶ Z) (ν : Z ⟶ P), IsImmersion f → (∀ b w, IsOpenImmersion (i b w)) → (∀ b w, i b w ≫ f = h b w) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → IsOpenImmersion j → j ≫ ν = f → Dense (Set.range j) → TopologicalSpace.NoetherianSpace F → IsSeparated (ν ≫ p0) → (ν ≫ p0) ⁻¹' ⋃ b, ((V b).1 : Set X) = Set.range j := by
  first | exact @GlobalTheory.FlagEmb.preimage_iUnion_eq_range_cells | exact GlobalTheory.FlagEmb.preimage_iUnion_eq_range_cells | (intros; apply GlobalTheory.FlagEmb.preimage_iUnion_eq_range_cells <;> assumption)
