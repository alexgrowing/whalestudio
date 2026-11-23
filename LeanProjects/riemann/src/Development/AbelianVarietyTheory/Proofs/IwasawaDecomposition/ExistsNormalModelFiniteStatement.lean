import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalFiniteModelOfFiniteOverOpen
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_model_finite : ∀ (A R K : Type) [CommRing A] [CommRing R] [Field K] (κ : A →+* R) (ω : R →+* K) (S Z U : Scheme.{0}) (s : S ⟶ Sp A) (j : Z ⟶ S) [IsOpenImmersion j] (sZ : Z ⟶ Sp A) (cU : U ⟶ Sp K) (y : U ⟶ Z) (h : y ≫ sZ = cU ≫ spMap (ω.comp κ)), IsDedFrac ω → κ.Finite → IsProjOver s → j ≫ s = sZ → Geo.Tor.IsNormalScheme U → IsFinite (pullback.lift y cU h) → ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (sY : Y ⟶ Sp R) (jQ : U ⟶ pullback sY (spMap ω)), IsFinite π ∧ π ≫ s = sY ≫ spMap κ ∧ Geo.Tor.IsNormalScheme Y ∧ IsProjOver sY ∧ Flat sY ∧ jQ ≫ pullback.snd _ _ = cU ∧ jQ ≫ pullback.fst _ _ ≫ π = y ≫ j ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ x, x ∈ Set.range jQ ↔ π (pullback.fst sY (spMap ω) x) ∈ Set.range j := by
  first | exact @GlobalTheory.exists_normal_finite_model_of_finite_over_open_baseChange | exact GlobalTheory.exists_normal_finite_model_of_finite_over_open_baseChange | (intros; apply GlobalTheory.exists_normal_finite_model_of_finite_over_open_baseChange <;> assumption)
