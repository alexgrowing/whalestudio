import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyK
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CruxSt

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CKC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK

variable {N : ℕ}

def Hc (N : ℕ) (t : ℂ) (T : Matrix (Fin N) (Fin N) ℂ) : ℂ := (1 + T).det ^ t

theorem analyticAt_Hc (N : ℕ) (t : ℂ) (T0 : Matrix (Fin N) (Fin N) ℂ) (h : (1 + T0).det ∈ Complex.slitPlane) :
    AnalyticAt ℂ (Hc N t) T0 := by
  unfold Hc
  have h1 : AnalyticAt ℂ (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det) T0 :=
    (CK.analyticAt_det (1 + T0)).comp (analyticAt_const.add analyticAt_id)
  exact h1.cpow analyticAt_const h

theorem one_det_slit : (1 + (0 : Matrix (Fin N) (Fin N) ℂ)).det ∈ Complex.slitPlane := by
  simpa using Complex.one_mem_slitPlane

theorem analyticAt_determinant_power_zero (N : ℕ) (t : ℂ) : AnalyticAt ℂ (Hc N t) 0 := analyticAt_Hc N t 0 one_det_slit

theorem det_phiF_slit (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane) :
    (1 + phiF X).det ∈ Complex.slitPlane := by rw [det_phiF]; exact hX

theorem fderiv_determinant_power_corner (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane) :
    fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 0 1) = t * Hc N t (piF X) := by
  have hD := det_phiF_slit X hX
  have h1 := fderiv_line (Hc (N + 1) t) (phiF X) (Matrix.single 0 0 1) (analyticAt_Hc _ t _ hD).differentiableAt
  have hD0 : (1 + piF X).det ≠ 0 := Complex.slitPlane_ne_zero hX
  have hfun : (fun s : ℂ => Hc (N + 1) t (phiF X + s • Matrix.single 0 0 1))
      = fun s : ℂ => ((1 + s) * (1 + piF X).det) ^ t := by
    funext s
    simp only [Hc]
    rw [← add_assoc, det_corner_perturbation]
  rw [hfun] at h1
  have hf : HasDerivAt (fun s : ℂ => (1 + s) * (1 + piF X).det) (1 * (1 + piF X).det) 0 :=
    ((hasDerivAt_id' (0 : ℂ)).const_add 1).mul_const _
  have h2 := hf.cpow_const (c := t) (by simpa using hX)
  refine (h1.unique h2).trans ?_
  simp only [Hc, add_zero, one_mul]
  rw [Complex.cpow_sub _ _ hD0, Complex.cpow_one]
  field_simp

theorem fderiv_determinant_power_column_neg (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane)
    (c : Fin N) :
    fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = -fderiv ℂ (Hc N t) (piF X) (colQ X c) := by
  have hA : AnalyticAt ℂ (Hc (N + 1) t) (phiF X) := analyticAt_Hc _ t _ (det_phiF_slit X hX)
  have h1 := fderiv_line (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) hA.differentiableAt
  have e : (fun s : ℂ => Hc (N + 1) t (phiF X + s • Matrix.single 0 c.succ 1)) =
      fun s : ℂ => Hc N t (piF X + s • (-colQ X c)) := by
    funext s
    simp only [Hc]
    rw [← add_assoc, det_column_perturbation, smul_neg, ← sub_eq_add_neg, add_sub_assoc]
  rw [e] at h1
  have hB : AnalyticAt ℂ (Hc N t) (piF X) := analyticAt_Hc _ t _ hX
  have h2 := fderiv_line (Hc N t) (piF X) (-colQ X c) hB.differentiableAt
  exact (h1.unique h2).trans (map_neg _ _)

theorem ev_piFc (N : ℕ) :
    ∀ᶠ X in 𝓝 (0 : Matrix (Fin N) (Fin (N + 1)) ℂ), (1 + piF X).det ∈ Complex.slitPlane := by
  have hc : ContinuousAt (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => (1 + piF X).det) 0 :=
    ((analyticAt_det _).comp (analyticAt_const.add (analyticAt_piF 0))).continuousAt
  have h0 : (1 + piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ)).det ∈ Complex.slitPlane := by
    rw [piF_zero, add_zero, Matrix.det_one]
    exact Complex.one_mem_slitPlane
  exact hc.eventually_mem (Complex.isOpen_slitPlane.mem_nhds h0)

theorem iterated_derivative_corner_case (t : ℂ) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ N (fun y => fderiv ℂ (Hc (N + 1) t) y (Matrix.single 0 0 1)) 0
        (fun k => Matrix.single k.succ (e k).succ 1) =
      t * iteratedFDeriv ℂ N (Hc N t) 0 (fun k => Matrix.single k (e k) 1) := by
  set G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → ℂ :=
    fun y => fderiv ℂ (Hc (N + 1) t) y (Matrix.single 0 0 1) with hG
  have hGa : AnalyticAt ℂ G 0 := analyticAt_fderiv_apply (Hc (N + 1) t) 0 _ (analyticAt_determinant_power_zero (N + 1) t)
  have e1 := icompL G phiF phiF_add phiF_smul 0 0 phiF_zero hGa N
    (fun k => Matrix.single k (e k).succ 1) (fun k => Matrix.single k.succ (e k).succ 1)
    (fun i => phiF_single _ _)
  rw [← e1]
  have hev : (G ∘ phiF) =ᶠ[𝓝 0] (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => t * Hc N t (piF X)) := by
    filter_upwards [ev_piFc N] with X hX
    exact fderiv_determinant_power_corner t X hX
  rw [(hev.iteratedFDeriv ℂ N).eq_of_nhds]
  have hHa : AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => Hc N t (piF X)) 0 := by
    have h0 : AnalyticAt ℂ (Hc N t) (piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ)) := by
      rw [piF_zero]
      exact analyticAt_determinant_power_zero N t
    exact h0.comp (analyticAt_piF 0)
  rw [iconst_mul _ 0 t hHa N]
  congr 1
  exact icompL (Hc N t) piF piF_add piF_smul 0 0 piF_zero (analyticAt_determinant_power_zero N t) N
    (fun k => Matrix.single k (e k).succ 1) (fun k => Matrix.single k (e k) 1)
    (fun i => piF_single_succ _ _)

def fsumc (t : ℂ) (c : Fin N) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : ℂ :=
  -∑ k, X k 0 * fderiv ℂ (Hc N t) (piF X) (Matrix.single k c 1)

theorem fderiv_determinant_power_column (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane)
    (c : Fin N) : fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = fsumc t c X := by
  rw [fderiv_determinant_power_column_neg t X hX c, colQ_expand, map_sum]
  simp only [map_smul, smul_eq_mul, fsumc]

theorem analyticAt_fsumc (t : ℂ) (c : Fin N) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ)
    (h : (1 + piF X0).det ∈ Complex.slitPlane) : AnalyticAt ℂ (fsumc t c) X0 := by
  have hs := Finset.analyticAt_sum
    (f := fun k (X : Matrix (Fin N) (Fin (N + 1)) ℂ) => X k 0 * fderiv ℂ (Hc N t) (piF X) (Matrix.single k c 1))
    Finset.univ (fun k _ => (analyticAt_entry k 0 X0).mul
      ((analyticAt_fderiv_apply (Hc N t) (piF X0) _ (analyticAt_Hc N t _ h)).comp (analyticAt_piF X0)))
  rw [Finset.sum_fn] at hs
  exact hs.neg

theorem fsum_linec (t : ℂ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    fsumc t c (y + s • Matrix.single k0 0 1) =
      fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
  simp only [fsumc]
  rw [piF_add, piF_smul, piF_single_zero, smul_zero, add_zero]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply, and_true, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, add_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem fderiv_fsumc (t : ℂ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ)
    (hy : (1 + piF y).det ∈ Complex.slitPlane) :
    fderiv ℂ (fsumc t c) y (Matrix.single k0 0 1) = -fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
  have h1 := fderiv_line (fsumc t c) y (Matrix.single k0 0 1) (analyticAt_fsumc t c y hy).differentiableAt
  have hfun : (fun s : ℂ => fsumc t c (y + s • Matrix.single k0 0 1))
      = fun s : ℂ => fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
    funext s
    exact fsum_linec t c k0 y s
  rw [hfun] at h1
  have h2 : HasDerivAt (fun s : ℂ => fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1))
      (0 - 1 * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1)) 0 :=
    (hasDerivAt_const _ _).sub ((hasDerivAt_id' (0 : ℂ)).mul_const _)
  refine (h1.unique h2).trans ?_
  ring

end PositivityTheory.Rg.Sw.HSt.CKC
