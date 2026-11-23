import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMul
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPointOf_rational_unitary_adelic_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (γ : UF E n) (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), IsPtOf hc g p → IsPtOf hc (ratAd F γ * g) (((γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  first | exact @GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd | (intros; apply GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd <;> assumption)
