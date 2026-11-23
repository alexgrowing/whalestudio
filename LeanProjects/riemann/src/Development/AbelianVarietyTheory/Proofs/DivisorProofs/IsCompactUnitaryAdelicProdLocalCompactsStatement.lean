import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompacts
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitaryAdelic_prod_local_compacts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (D : ∀ v : AwayP p, Set (Gv G v)), (∀ v, IsCompact (D v)) → (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D v ⊆ IntV G v) → IsCompact {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
  first | (exact @GlobalTheory.OrbFinAf.isCompact_prod_local) | (exact GlobalTheory.OrbFinAf.isCompact_prod_local) | (intros; apply GlobalTheory.OrbFinAf.isCompact_prod_local  <;> assumption)
