import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellPointEqOfTriangularFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCell_point_eq_of_triangular_frames : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (k : Type) [Field k] b b' w w' (ψ : CR m (V b) →+* k) (ψ' : CR m (V b') →+* k) (d : Let m → k), spMap ψ ≫ cbase m (V b) = spMap ψ' ≫ cbase m (V b') → (∀ z, d z ≠ 0) → Tri (fun z => ψ ∘ uvec (c b) w z) (fun z => ψ' ∘ uvec (c b') w' z) d → spMap ψ ≫ h b w = spMap ψ' ≫ h b' w' := by
  first | exact @GlobalTheory.FlagEmb.cell_pt_eq_of_tri | exact GlobalTheory.FlagEmb.cell_pt_eq_of_tri | (intros; apply GlobalTheory.FlagEmb.cell_pt_eq_of_tri <;> assumption)
