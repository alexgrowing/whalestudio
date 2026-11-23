import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem lamAt_last {R : Ranks} (h : HCParam R) (i : Fin R.m) (n : ℕ) (hn : n + 1 = R.k + i) :
    Formalism.L2.NTheta.lamAt h n = -h.b i := by
  have hk := R.m_add_three_le_k
  have hi := i.2
  have e : n - (R.k - 1) = i := by omega
  unfold Formalism.L2.NTheta.lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 2
  exact Fin.ext e

theorem lastPos_of_kapIs :
    ∀ (D : D7) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ i, (κ i).LastPos := by
  intro D κ h i τ k hk
  rw [(h i τ).1 k,
    show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hp : (k : ℕ) + 1 = D.R.k + i := by
    rw [hk]
    simp only [Ranks.sigW]
    omega
  have hg := (D.hc τ).gap_be i
  have hq : (((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) = ((k : ℕ) : ℚ) + 1 := by
    exact_mod_cast hk.symm
  simp only [aPl, if_pos k.2]
  rw [lamAt_last (D.hc τ) i k hp, hq]
  have h1 : (1 : ℤ) ≤ ⌊-(D.hc τ).b i + (D.hc τ).e i - (((k : ℕ) : ℚ) + 1 - (((k : ℕ) : ℚ) + 1)) -
      ((D.R.t : ℚ) + 1) / 2⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  omega

end GlobalTheory.HolDict
