import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTauComponentFrameOfLattice
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tau_component_frame_of_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (τ : S.K →ₐ[S.Qp] S.LL), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (r : ℕ) (Pm : Matrix (Fin r) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (J : Finset ℤ), (∀ u, u ∈ J → IsJumpV S.PD T.ρ τ u) ∧ {u | IsJumpV S.PD T.ρ τ u}.Finite ∧ Frame (D.loc l).χQ K (mN l s (M0 + h0)) U g ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K (mN l s (M0 + h0))) U (J : Set ℤ) ∧ (∀ σ ∈ Gj K (mN l s (M0 + h0)), Pm * M σ = U σ * Pm.map ((D.locA l).actC σ)) ∧ ball l r ⊆ Pm.mulVec '' ball l d ∧ (∀ x ∈ ball l d, (l : PadicComplex l) • Pm.mulVec x ∈ ball l r) ∧ ∀ y : Fin d → ℚ_[l], Pm.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ Pm.mulVec '' ball l d → ∀ a, ‖y a‖ ≤ 1 := by
  first | exact @GlobalTheory.TauFrame.exists_tau_frame | exact GlobalTheory.TauFrame.exists_tau_frame | (intros; apply GlobalTheory.TauFrame.exists_tau_frame <;> assumption)
