import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTangentEmbedding
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
theorem _root_.GlobalTheory.T.base_change_tangent_embedding : ∀ (D : D7) (O : Setup D) (y : Pt O.s) (K₀ : Type) [Field K₀] [NumberField K₀] (io₀ : K₀ →+* Qb), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (io : K →+* Qb) (j : K₀ →+* K) (fK : O.κ.c.F →+* K) (yK : Sp K ⟶ gen O.s.T.Z) (hio : spMap io ≫ yK = y.y) (b : Pad.Letter O.S.Dw → TanM (yK ≫ genι O.s.T.Z) O.s.T.Z.t.G), io.comp j = io₀ ∧ yK ≫ genStr O.s.T.Z = spMap fK ∧ ∀ l, (tv (bcTan io (by rw [← Category.assoc, hio]) (b l))).left = y.u l.1 l.2 := by
  first | exact @GlobalTheory.PtDescent.exists_descent | exact GlobalTheory.PtDescent.exists_descent | (intros; apply GlobalTheory.PtDescent.exists_descent <;> assumption)
