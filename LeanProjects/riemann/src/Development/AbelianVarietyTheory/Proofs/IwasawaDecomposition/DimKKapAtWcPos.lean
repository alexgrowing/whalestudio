import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeylDimPos

theorem weylDimU_pos {p : ℕ} (lam : Fin p → ℤ) (h : ∀ i j : Fin p, i ≤ j → lam j ≤ lam i) : 0 < weylDimU lam := by
  unfold weylDimU
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  have hij : i < j := (Finset.mem_filter.1 hj).2
  have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
  have h2 : (0 : ℚ) ≤ ((lam i - lam j : ℤ) : ℚ) := by exact_mod_cast sub_nonneg.2 (h i j hij.le)
  exact div_pos (by linarith) (by linarith)

theorem dimK_kapW_pos {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) :
    0 < dimK p q (Formalism.L2.NTheta.kapW h p q) := by
  obtain ⟨h1, h2, -⟩ := Formalism.L2.NTheta.holOK_kapW h p q hpq
  exact mul_pos (weylDimU_pos _ fun i j hij => h1 i j hij) (weylDimU_pos _ fun i j hij => h2 i j hij)

theorem dimK_kapAt_pos {D : D7} (W : HSp D) (hW : W.SigOK) (hr : W.rank = D.R.r) (σ : D.what₂.LL →+* ℂ)
    (ρ : D.what₂.Tau) : 0 < dimK _ _ (kapAt W σ ρ) :=
  dimK_kapW_pos _ _ _ (by rw [← hr]; obtain ⟨e, -⟩ := hW (tauE D ρ); simpa using (Fintype.card_congr e).symm)

theorem dimK_kapAt_Wc_pos (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    0 < dimK _ _ (kapAt (Wc D i) σ ρ) :=
  dimK_kapAt_pos _ (D.sp.W_sig _) (D.sp.W_rank _ (by omega) (by have := i.2; omega)) σ ρ

end GlobalTheory.Mem.WeylDimPos
