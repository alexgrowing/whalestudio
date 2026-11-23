import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFamilyIndependentTangents
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts GlobalTheory.LieMet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_family_independent_tangents : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (K : Type) [Field K] [NumberField K] (fK : O.κ.c.F →+* K) (yK : Sp K ⟶ gen O.s.T.Z), yK ≫ genStr O.s.T.Z = spMap fK → ∀ {n : ℕ} (b : Fin n → TanM (yK ≫ genι O.s.T.Z) O.s.T.Z.t.G), (∀ σ : K →+* ℂ, LinearIndependent ℂ (fun i => bcTan σ (Category.assoc (spMap σ) yK (genι O.s.T.Z)).symm (b i))) → ∃ h : HermFam K (Fin n → K), ∀ (σ : K →+* ℂ) (z : GlobalTheory.CxPts (genStr O.s.T.Z) (σ.comp fK)) (hz : z.1 = spMap σ ≫ yK) (u v : Fin n → K), h.form σ u v = x.met (σ.comp fK) z (bcTan σ (by rw [hz, Category.assoc]) (∑ i, v i • b i)) (bcTan σ (by rw [hz, Category.assoc]) (∑ i, u i • b i)) := by
  first | exact @GlobalTheory.LieMetFam.exists_hermFam_met | exact GlobalTheory.LieMetFam.exists_hermFam_met | (intros; apply GlobalTheory.LieMetFam.exists_hermFam_met <;> assumption)
