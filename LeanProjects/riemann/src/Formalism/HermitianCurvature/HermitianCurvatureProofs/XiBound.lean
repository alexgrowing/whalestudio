import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem xi_bound (hP : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef p.T.base F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (hw : KB.CutWord P p.l0 w) (h h' : C.LPt) (hh : D.IsLocPt h j)
    (hh' : D.IsLocPt h' j)
    (grid : Fin 3 → Fin (2 * j + 1) → ℝ) (hinj : ∀ a, Function.Injective (grid a))
    (hgr : ∀ n : Fin 3 → Fin (2 * j + 1), KB.CutWord P p.l0 (KB.plusW (List.ofFn fun a => grid a (n a)) w) ∧
        KB.CutWord P p.l0 (KB.minusW (List.ofFn fun a => grid a (n a)) w) ∧
        (List.ofFn fun a => grid a (n a)).Pairwise (fun y y' => 2 < |y - y'|))
    (Mo : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))
    (hMo : ∀ ε x, (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → ∀ e, JC.NiceCoef (p.T.bs j) ε (Mo x e))
    (hMoC : ∀ x, (∀ e, KB.CptCoef (p.T.bs j) (x e)) → ∀ e, KB.CptCoef (p.T.bs j) (Mo x e)) (a b : ℝ)
    (hA0 : ‖p.form j hj w (Mo (KB.slv p.T F j hj w h hh.2)) (Mo (KB.slv p.T F j hj w h hh.2))‖ ≤ a)
    (hB0 : ‖p.form j hj w (KB.slv p.T F j hj w h' hh'.2) (KB.slv p.T F j hj w h' hh'.2)‖ ≤ b)
    (hA : ∀ n : Fin 3 → Fin (2 * j + 1), ‖p.form j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w)
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))‖ ≤ a)
    (hB : ∀ n : Fin 3 → Fin (2 * j + 1), ‖p.form j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w)
        (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)
        (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)‖ ≤ b) (s : ℂ) :
    ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo (KB.slv p.T F j hj w h hh.2))) (KB.slv p.T F j hj w h' hh'.2)‖ ≤
      8 * (1 + ∑ n : Fin 3 → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| /
        Real.sqrt (((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod)) *
        Real.sqrt (a * b) * ((1 + ‖s‖) ^ 3)⁻¹ := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hA0
  have hb : 0 ≤ b := (norm_nonneg _).trans hB0
  set x := KB.slv p.T F j hj w h hh.2 with hxdef
  set y := KB.slv p.T F j hj w h' hh'.2 with hydef
  have hxc : ∀ e, KB.CptCoef (p.T.bs j) (x e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h hh hF e
  have hyc : ∀ e, KB.CptCoef (p.T.bs j) (y e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h' hh' hF e
  set R := Real.sqrt (a * b) with hRdef
  have hR : 0 ≤ R := Real.sqrt_nonneg _

  have hCS : ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ ≤ R := by
    obtain ⟨-, hss⟩ := Formalism.FourierDecayAlt.P.size_standard_compact hP Wp Wq P p j hj w [] hw hw List.Pairwise.nil
    obtain ⟨hWc, hiso⟩ := Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support hP Wp Wq P p j hj w hw s (Mo x) (Mo x) (hMoC x hxc)
      (hMoC x hxc)
    have key := hss (KB.waveG (p.T.bs j) s w (Mo x)) y hWc hyc
    simp only [List.map_nil, List.prod_nil, mul_one] at key
    change ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ ^ 2 ≤
      (p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) (KB.waveG (p.T.bs j) s w (Mo x))).re *
        (p.form j hj w y y).re at key
    rw [hiso] at key
    have h1 := Complex.abs_re_le_norm (p.form j hj w (Mo x) (Mo x))
    have h2 := Complex.abs_re_le_norm (p.form j hj w y y)
    have hab : (p.form j hj w (Mo x) (Mo x)).re * (p.form j hj w y y).re ≤ a * b := by
      calc (p.form j hj w (Mo x) (Mo x)).re * (p.form j hj w y y).re
          ≤ |(p.form j hj w (Mo x) (Mo x)).re * (p.form j hj w y y).re| := le_abs_self _
        _ = |(p.form j hj w (Mo x) (Mo x)).re| * |(p.form j hj w y y).re| := abs_mul _ _
        _ ≤ a * b := mul_le_mul (h1.trans hA0) (h2.trans hB0) (abs_nonneg _) ha
    have habs := Real.abs_le_sqrt (key.trans hab)
    rwa [abs_of_nonneg (norm_nonneg _)] at habs

  set K := ∑ n : Fin 3 → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| /
        Real.sqrt (((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod)
    with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun n _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hT : ‖s‖ ^ 3 * ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ ≤ K * R := by
    refine (wave_bound3 hP P p F hF j hj w h h' hh hh' grid hinj hgr Mo hMo hMoC s).trans ?_
    rw [hKdef, Finset.sum_mul]
    refine Finset.sum_le_sum fun n _ => ?_
    obtain ⟨hc1, hc2, hpw⟩ := hgr n
    obtain ⟨hq, -⟩ := Formalism.FourierDecayAlt.P.size_standard_compact hP Wp Wq P p j hj w _ hc1 hc2 hpw
    have hqpos : 0 < ((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod := by
      refine List.prod_pos fun c hc => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
      exact hq y hy
    rw [show ∀ u v x : ℝ, u / v * x = u * (x / v) from fun u v x => by ring]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (∏ a, F7.lagCo (grid a) (n a)))
    rw [← Real.sqrt_div' _ hqpos.le]
    refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ?_ hqpos.le)
    have h1 := Complex.abs_re_le_norm (p.form j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w)
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2)))
    have h2 := Complex.abs_re_le_norm (p.form j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w)
        (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)
        (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2))
    exact (le_abs_self _).trans ((abs_mul _ _).le.trans
      (mul_le_mul (h1.trans (hA n)) (h2.trans (hB n)) (abs_nonneg _) ha))

  have hu : 0 < 1 + ‖s‖ := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hu 3)]
  by_cases hs : ‖s‖ ≤ 1
  · have hu8 : (1 + ‖s‖) ^ 3 ≤ 8 := by
      calc (1 + ‖s‖) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hu.le (by linarith) 3
        _ = 8 := by norm_num
    calc ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ * (1 + ‖s‖) ^ 3 ≤ R * 8 :=
          mul_le_mul hCS hu8 (by positivity) hR
      _ ≤ 8 * (1 + K) * R := by nlinarith
  · push Not at hs
    have hu8 : (1 + ‖s‖) ^ 3 ≤ 8 * ‖s‖ ^ 3 := by
      calc (1 + ‖s‖) ^ 3 ≤ (2 * ‖s‖) ^ 3 := pow_le_pow_left₀ hu.le (by linarith) 3
        _ = 8 * ‖s‖ ^ 3 := by ring
    calc ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ * (1 + ‖s‖) ^ 3
        ≤ ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖ * (8 * ‖s‖ ^ 3) :=
          mul_le_mul_of_nonneg_left hu8 (norm_nonneg _)
      _ = 8 * (‖s‖ ^ 3 * ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo x)) y‖) := by ring
      _ ≤ 8 * (K * R) := by linarith
      _ ≤ 8 * (1 + K) * R := by nlinarith

end Formalism.FourierDecayAlt.P.PBO
