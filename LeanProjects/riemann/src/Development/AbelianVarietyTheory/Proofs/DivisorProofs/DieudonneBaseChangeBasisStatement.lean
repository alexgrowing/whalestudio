import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneBaseChangeBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonne_baseChange_basis : ∀ (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) (B : Base p P) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (hG : P k G) (hG' : P k' (G.baseChange k')) (ι : Type) [Fintype ι] (b : Module.Basis ι (WittVector p k) (B.M G hG)), ∃ b' : Module.Basis ι (WittVector p k') (B.M (G.baseChange k') hG'), ∀ i, b' i = B.smap hG' hG (G.toBase k') (b i) := by
  first | exact @GlobalTheory.Dieu.Base.smap_toBase_basis | exact GlobalTheory.Dieu.Base.smap_toBase_basis | (intros; apply GlobalTheory.Dieu.Base.smap_toBase_basis <;> assumption)
