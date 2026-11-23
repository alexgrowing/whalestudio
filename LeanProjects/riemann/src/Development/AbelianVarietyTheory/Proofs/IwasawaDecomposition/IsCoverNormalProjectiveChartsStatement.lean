import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoverNormalProjectiveCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCover_normal_projective_charts : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field K] [Algebra O K] [IsFractionRing O K] (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (algebraMap O K) s V α c D → ∃ (n : ℕ) (I : (PSpace O n).IdealSheafData) (π : I.subscheme ⟶ X) (g : ∀ en : En m, I.subscheme ⟶ PSpace O (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ I.subscheme)), π ≫ s = I.subschemeι ≫ PSpace.str O n ∧ IsFlagModel (algebraMap O K) s V α c π g κ := by
  first | exact @GlobalTheory.FlagModel.exists_flagModel | exact GlobalTheory.FlagModel.exists_flagModel | (intros; apply GlobalTheory.FlagModel.exists_flagModel <;> assumption)
