import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPshFormPsh
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory
open ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasi_psh_form_psh : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y), Y.dim = e → ∀ (a : Fin (M.n + 1)) (Θ : LocPot (M.X a)) (θ : ChartForm Y.str (I.ε a) Y.dim) (v : M.X a → EReal), IsPotential (M.A a) Θ → (∀ x, GlobalTheory.ShFam.IsPotential (AnRead.all Y.str (I.ε a) Y.dim) θ (I.pt a '' Θ.U x) (fun y => 2 * Θ.φ x ((I.pt a).symm y))) → GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsQuasiPsh (M.A a) Θ v → GlobalTheory.Published.IsFormPsh (AnRead.all Y.str (I.ε a) Y.dim) θ (v ∘ (I.pt a).symm) := by
  first | exact @GlobalTheory.QuasiPshTransfer.isFormPsh_of_isQuasiPsh | exact GlobalTheory.QuasiPshTransfer.isFormPsh_of_isQuasiPsh | (intros; apply GlobalTheory.QuasiPshTransfer.isFormPsh_of_isQuasiPsh <;> assumption)
