import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequences
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.PhiPG0
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leibniz_order_of_exact_sequences : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k → PsiGP k → PhiGP k → PsiPG k → PhiPG k → PhiPG0 k → LeibnizOrd k := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts | exact GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts <;> assumption)
