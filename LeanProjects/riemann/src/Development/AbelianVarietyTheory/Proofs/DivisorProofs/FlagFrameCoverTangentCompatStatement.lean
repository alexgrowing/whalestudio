import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFrameCoverTangentCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCountStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frame_cover_tangent_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)), IsTanBasis t (hU.fromSpec ≫ ρ') e → ∀ (J : Type) (h : J → Fin g → Γ(V.X, U)) (k : ℕ) (hk : k ≤ m), ∃ s : (Fin k → J) → V.G.functionField, ∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h j i)) a hk σ) := by
  first | exact @GlobalTheory.HtGen.CoverChart.pairDet_div_eq | exact GlobalTheory.HtGen.CoverChart.pairDet_div_eq | (intros; apply GlobalTheory.HtGen.CoverChart.pairDet_div_eq <;> assumption)
