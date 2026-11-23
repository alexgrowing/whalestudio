import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FderivDeterminantPowerColumnNeg
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyG
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyEq

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CKC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK

theorem iterated_derivative_column_case (t : ℂ) (M : ℕ) (e : Equiv.Perm (Fin (M + 1))) (c : Fin (M + 1)) :
    iteratedFDeriv ℂ (M + 1) (fun y => fderiv ℂ (Hc (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ) 1) =
      -iteratedFDeriv ℂ (M + 1) (Hc (M + 1) t) 0 (fun k => Matrix.single k (e k) 1) := by
  set σ := Equiv.Perm.decomposeFin.symm (c.succ, e) with hσ
  set k0 : Fin (M + 1) := e.symm c with hk0
  have hek0 : e k0 = c := by rw [hk0, Equiv.apply_symm_apply]
  have hσk0 : σ k0.succ = 0 := by
    rw [hσ, Equiv.Perm.decomposeFin_symm_apply_succ, hek0, Equiv.swap_apply_right]
  have hσo : ∀ j : Fin M, σ (k0.succAbove j).succ = (e (k0.succAbove j)).succ := by
    intro j
    rw [hσ, Equiv.Perm.decomposeFin_symm_apply_succ]
    apply Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
    intro h
    have h' := Fin.succ_injective _ h
    rw [← hek0] at h'
    exact Fin.succAbove_ne k0 j (e.injective h')
  have hslit0 : (1 + piF (0 : Matrix (Fin (M + 1)) (Fin (M + 1 + 1)) ℂ)).det ∈ Complex.slitPlane := by
    simp [piF_zero]
  have hA := icompL (fun y => fderiv ℂ (Hc (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) phiF
    phiF_add phiF_smul 0 0 phiF_zero
    (analyticAt_fderiv_apply _ _ _ (analyticAt_determinant_power_zero _ t)) (M + 1)
    (fun k => Matrix.single k (σ k.succ) 1)
    (fun k => Matrix.single k.succ (σ k.succ) 1) (fun k => phiF_single _ _)
  rw [← hA]
  have hB : (fun y => fderiv ℂ (Hc (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) ∘ phiF
      =ᶠ[𝓝 0] fsumc t c := by
    filter_upwards [ev_piFc (M + 1)] with X hX
    exact fderiv_determinant_power_column t X hX c
  rw [(hB.iteratedFDeriv ℂ (M + 1)).eq_of_nhds]
  rw [ipeel (fsumc t c) 0 (analyticAt_fsumc t c 0 hslit0) M _ k0]
  have hD : (fun y => fderiv ℂ (fsumc t c) y (Matrix.single k0 (σ k0.succ) 1)) =ᶠ[𝓝 0]
      fun y => (-1 : ℂ) *
        ((fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ piF) y := by
    filter_upwards [ev_piFc (M + 1)] with X hX
    have h := fderiv_fsumc t c k0 X hX
    simp only [Function.comp_apply]
    rw [hσk0]
    erw [h]
    ring
  refine (congrFun (congrArg DFunLike.coe (hD.iteratedFDeriv ℂ M).eq_of_nhds) _).trans ?_
  have hG0 : AnalyticAt ℂ (fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) 0 :=
    analyticAt_fderiv_apply _ _ _ (analyticAt_determinant_power_zero _ t)
  have hGc : AnalyticAt ℂ
      ((fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ piF) 0 := by
    have hcomp : ((fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ piF) =
        (fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ (piL (M + 1)) := by
      funext X
      simp only [Function.comp_apply, piL_apply]
    rw [hcomp]
    refine AnalyticAt.comp ?_ ((piL (M + 1)).analyticAt 0)
    rw [piL_apply, piF_zero]
    exact hG0
  refine (iconst_mul _ 0 (-1) hGc M _).trans ?_
  rw [icompL (fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) piF
    piF_add piF_smul 0 0 piF_zero hG0 M _
    (fun k => Matrix.single (k0.succAbove k) (e (k0.succAbove k)) 1)
    (fun k => by simp only [hσo, piF_single_succ])]
  rw [neg_one_mul, ipeel (Hc (M + 1) t) 0 (analyticAt_determinant_power_zero _ t) M _ k0, hek0]
  rfl

theorem term_pc (t : ℂ) (N : ℕ) (p : Fin (N + 1)) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ (N + 1) (Hc (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (p, e) k) 1) =
      iteratedFDeriv ℂ N (fun y => fderiv ℂ (Hc (N + 1) t) y (Matrix.single 0 p 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (p, e) k.succ) 1) := by
  rw [ipeel0 (Hc (N + 1) t) 0 (analyticAt_determinant_power_zero (N + 1) t) N]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero]
  rfl

theorem rec_stepc (t : ℂ) (N : ℕ) : detD (Hc (N + 1) t) = (t + N) * detD (Hc N t) := by
  have h0 : ∀ e : Equiv.Perm (Fin N),
      iteratedFDeriv ℂ (N + 1) (Hc (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (0, e) k) 1) =
      t * iteratedFDeriv ℂ N (Hc N t) 0 (fun k => Matrix.single k (e k) 1) := by
    intro e
    rw [term_pc]
    simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    exact iterated_derivative_corner_case t e
  have h1 : ∀ (c : Fin N) (e : Equiv.Perm (Fin N)),
      iteratedFDeriv ℂ (N + 1) (Hc (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (c.succ, e) k) 1) =
      -iteratedFDeriv ℂ N (Hc N t) 0 (fun k => Matrix.single k (e k) 1) := by
    intro c e
    cases N with
    | zero => exact c.elim0
    | succ M =>
      rw [term_pc]
      exact iterated_derivative_column_case t M e c
  rw [detD_fin (N + 1) _ (analyticAt_determinant_power_zero (N + 1) t), detD_fin N _ (analyticAt_determinant_power_zero N t),
    ← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [Equiv.Perm.decomposeFin.symm_sign, h0, h1, Fin.succ_ne_zero, if_true, if_false,
    Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg, Int.cast_one,
    one_mul, neg_one_mul, mul_neg, neg_neg, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [add_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

theorem capelli_determinant_rising_factorial (t : ℂ) : ∀ N : ℕ, detD (Hc N t) = ∏ i ∈ Finset.range N, (t + i)
  | 0 => by
    rw [detD_fin 0 _ (analyticAt_determinant_power_zero 0 t)]
    simp [Hc, iteratedFDeriv_zero_apply]
  | N + 1 => by
    rw [rec_stepc, capelli_determinant_rising_factorial t N, Finset.prod_range_succ]
    ring

end PositivityTheory.Rg.Sw.HSt.CKC

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem kappaC : KappaC := fun N t => CKC.capelli_determinant_rising_factorial t N

theorem analyticAt_det_one_add_cpow {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℂ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) 0 := by
  have h1 : AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det) 0 :=
    (LVs.analyticAt_det (1 + 0)).comp (analyticAt_const.add analyticAt_id)
  exact h1.cpow analyticAt_const (by simpa using Complex.one_mem_slitPlane)

end PositivityTheory.Rg.Sw.HSt
