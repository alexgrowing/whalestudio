import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelEntryRationalEquivarianceTransports
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntry_rationalEquivariance_transports : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β} (q : (I.stp u a i).D b) (q' : (I.stp u a (i + 1)).D b') (g : (I.stp u a i).G b) (g' : (I.stp u a (i + 1)).G b') (x : Fr B.fields.emb B.embLL (B.R.N i) → ℂ), (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) → ent I l u a i ((I.stp u a i).act b g q) ((I.stp u a (i + 1)).act b' g' q') ((I.stp u a i).tr B.fields.emb B.embLL b g x) = (I.stp u a (i + 1)).tr B.fields.emb B.embLL b' g' (ent I l u a i q q' x) := by
  first | exact @GlobalTheory.KerDia.Eqv.ent_smul | exact GlobalTheory.KerDia.Eqv.ent_smul | (intros; apply GlobalTheory.KerDia.Eqv.ent_smul <;> assumption)
