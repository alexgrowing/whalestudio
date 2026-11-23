import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalUnitaryPairToPairComponentMemLocalLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalUnitary_pairToPair_component_mem_localLevel : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → (pc P v c').act (glE γ) = pc P v c → mov K (A.eV v).1 c γ c' ∈ K.lev.Uloc (A.eV v).1 := by
  first | exact @GlobalTheory.LevelHecke.PairToLevel.main | exact GlobalTheory.LevelHecke.PairToLevel.main | (intros; apply GlobalTheory.LevelHecke.PairToLevel.main <;> assumption)
