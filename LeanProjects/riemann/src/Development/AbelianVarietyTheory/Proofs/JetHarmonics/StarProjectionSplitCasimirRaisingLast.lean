import Mathlib
import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorStdRelAdjointSplitCasimir
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRowInvertsCasimir
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirStdEigenvalue
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem starProjection_splitCasimirStd_last : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + 0)).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  intro V _ _ _ n E Et Om β L l hH hadj hEt hOm M v hv
  have hq : ∀ w v, qdet E w v = (∏ j, (w + shf β L j)) • v := hH.cap
  obtain ⟨K, hK, hK'⟩ := comatrix_last_row_inverts_casimir V n E Om (shf β L) hH.gl hq hOm
  obtain ⟨-, -, hsym, -⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hH.gl hadj hEt hOm
  have hev := splitCasimirStd_eigenvalue V n E Et Om (shf β L) hH.gl hadj hq hEt hOm
  have hinj : Function.Injective (shf β L) := by
    intro a b h
    apply hH.anti.injective
    have h' : (L a : ℂ) = (L b : ℂ) := add_left_cancel h
    exact_mod_cast h'
  have hcont : Continuous fun u : ℂ => cpol (shf β M) (u - 1) := by
    unfold cpol
    fun_prop
  have h := ev_starProjection_eigenspace_eq_residue (PiLp 2 (fun _ : Fin (n + 1) => V)) V (n + 1)
    (shf β L) 0 Om (PiLp.projₗ 2 (fun _ : Fin (n + 1) => V) (Fin.last n)) K
    (fun u : ℂ => cpol (shf β M) (u - 1)) (PiLp.single 2 (Fin.last n) v) v l hinj hsym hev hK hcont
    (fun u => (hK' u v).trans (mem_CapSp.1 hv (u - 1)))
  refine Eq.trans h ?_
  congr 1
  simp only [cpol, shf, WigSh.wP]
  push_cast
  congr 1
  · exact Finset.prod_congr rfl fun j _ => by ring
  · exact Finset.prod_congr rfl fun j _ => by ring

end GlobalTheory
