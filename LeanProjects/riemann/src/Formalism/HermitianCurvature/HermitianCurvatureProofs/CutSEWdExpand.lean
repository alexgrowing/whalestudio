import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2

open Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem wdx_diff {n m : ℕ} {f : ℂ → ℂ} (hf : ContDiffOn ℝ n f {t | t ≠ 0}) (hm : m < n) {t : ℂ} (ht : t ≠ 0) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ m f) t := by
  have hs : IsOpen {t : ℂ | t ≠ 0} := isOpen_ne
  have hd := hf.differentiableOn_iteratedFDerivWithin (by exact_mod_cast hm) hs.uniqueDiffOn
  have hdt : DifferentiableAt ℝ (iteratedFDerivWithin ℝ m f {t | t ≠ 0}) t :=
    (hd t ht).differentiableAt (hs.mem_nhds ht)
  exact hdt.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hs.mem_nhds ht)
    fun s hs' => (iteratedFDerivWithin_of_isOpen m hs hs').symm)

theorem wdx_hasFDerivAt_iter {m : ℕ} {f : ℂ → ℂ} {t : ℂ}
    (hd : DifferentiableAt ℝ (iteratedFDeriv ℝ m f) t) (w : Fin m → ℂ) :
    HasFDerivAt (fun s => iteratedFDeriv ℝ m f s w)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℂ) ℂ w).comp (fderiv ℝ (iteratedFDeriv ℝ m f) t)) t := by
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℂ) ℂ w).hasFDerivAt.comp t hd.hasFDerivAt

theorem wdx_step_eval {m : ℕ} {f : ℂ → ℂ} {t : ℂ} (h : ℂ) (w : Fin m → ℂ) :
    (fderiv ℝ (iteratedFDeriv ℝ m f) t h) w = iteratedFDeriv ℝ (m + 1) f t (Fin.cons h w) := by
  rw [iteratedFDeriv_succ_apply_left]
  simp

theorem word_expansion : WdExpand := by
  intro n f bs hlen hf
  induction bs with
  | nil =>
    refine ⟨1, fun _ => 1, fun _ => Fin.elim0, fun _ => by simp, fun t _ => ?_⟩
    simp [WD]
  | cons b bs ih =>
    have hlen' : bs.length ≤ n := by simp at hlen; omega
    have hlt : bs.length < n := by simp at hlen; omega
    obtain ⟨K, a, v, -, hv⟩ := ih hlen'
    have hs : IsOpen {t : ℂ | t ≠ 0} := isOpen_ne
    have hder : ∀ t : ℂ, t ≠ 0 → ∀ h : ℂ, fderiv ℝ (WD bs f) t h =
        ∑ i, a i * iteratedFDeriv ℝ (bs.length + 1) f t (Fin.cons h (v i)) := by
      intro t ht h
      have heq : WD bs f =ᶠ[𝓝 t] fun s => ∑ i, a i * iteratedFDeriv ℝ bs.length f s (v i) :=
        Filter.eventuallyEq_of_mem (hs.mem_nhds ht) fun s hs' => hv s hs'
      have hd := wdx_diff hf hlt ht
      have hH : HasFDerivAt (fun s => ∑ i, a i * iteratedFDeriv ℝ bs.length f s (v i))
          (∑ i, a i • ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin bs.length => ℂ) ℂ (v i)).comp
            (fderiv ℝ (iteratedFDeriv ℝ bs.length f) t))) t := by
        first
          | exact HasFDerivAt.fun_sum fun i _ => (wdx_hasFDerivAt_iter hd (v i)).const_mul (a i)
          | (convert HasFDerivAt.sum (u := Finset.univ)
              (fun i _ => (wdx_hasFDerivAt_iter hd (v i)).const_mul (a i)) using 1
             ext s
             simp)
      rw [heq.fderiv_eq, hH.fderiv]
      simp [wdx_step_eval]
    refine ⟨K + K, Fin.append (fun i => (1 / 2 : ℂ) * a i)
        (fun i => (1 / 2 : ℂ) * ((if b then -Complex.I else Complex.I) * a i)),
      Fin.append (fun i => Fin.cons (1 : ℂ) (v i)) (fun i => Fin.cons Complex.I (v i)),
      fun h => by simp at h, fun t ht => ?_⟩
    show wirt b (WD bs f) t = ∑ i : Fin (K + K), _ * iteratedFDeriv ℝ (bs.length + 1) f t _
    unfold wirt
    rw [hder t ht, hder t ht, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, mul_add, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring

end Formalism.FourierDecayAlt.P.CutSE
