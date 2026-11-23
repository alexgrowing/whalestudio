import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombAtGBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCombAtG_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (U : Fin g → R) (σ : 𝓞 E →+* R) (u : Sp (DualNumber R) ⟶ t.G.left),
    (IsCombAtG t x e U u → IsCombAtG t (spMap φ ≫ x) (bcV t φ e) (fun b => φ (U b)) (spMap (dualMap φ) ≫ u)) ∧
    (IsEigG t σ u → IsEigG t (φ.comp σ) (spMap (dualMap φ) ≫ u)) := by
  first | exact @GlobalTheory.FlatModel.BaseChangeComb.bc_comb_eig | exact GlobalTheory.FlatModel.BaseChangeComb.bc_comb_eig | (intros; apply GlobalTheory.FlatModel.BaseChangeComb.bc_comb_eig <;> assumption)
