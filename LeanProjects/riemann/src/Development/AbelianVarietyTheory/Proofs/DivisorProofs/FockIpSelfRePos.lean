import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenKLeFockStab

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem fockIp_self_re_pos {ι : Type} {p : MvPolynomial ι ℂ} (hp : p ≠ 0) :
    0 < (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp p p).re := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp
  rw [Complex.re_sum]
  refine Finset.sum_pos (fun k hk => ?_) (MvPolynomial.support_nonempty.2 hp)
  rw [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  refine mul_pos (Complex.normSq_pos.2 (MvPolynomial.mem_support_iff.1 hk)) ?_
  exact Nat.cast_pos.2 (Finset.prod_pos fun _ _ => Nat.factorial_pos _)

theorem fockSum_ne_zero : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ), a ≤ d → fockSum D a d n ≠ 0 := by
  intro D a d n had h0
  have hpos : 0 < (fockSum D a d n).re := by
    unfold fockSum
    rw [Complex.re_sum]
    haveI : Nonempty (GlobalTheory.NormSum.Tup D a d n) := ⟨fun _ _ => ⟨Fin.castLE had, fun _ _ h => h⟩⟩
    exact Finset.sum_pos (fun T _ => fockIp_self_re_pos (GlobalTheory.NormAdelic.minorPol_ne_zero T)) (by
      classical exact ⟨fun _ _ => ⟨Fin.castLE had, fun _ _ h => h⟩, by simp⟩)
  rw [h0] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.NormRatio
