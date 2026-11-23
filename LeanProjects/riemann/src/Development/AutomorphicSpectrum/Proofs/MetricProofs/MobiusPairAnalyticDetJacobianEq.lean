import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem det_eq_mul_minor_of_col_zero {n : ℕ} (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (h : ∀ i : Fin n, J i.succ 0 = 0) : J.det = J 0 0 * (J.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

theorem hasDerivAt_mob_line (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) (h : den G a ≠ 0) :
    HasDerivAt (fun t : ℂ => mob G (a + t)) (mobD G a) 0 := by
  have hl : HasDerivAt (fun t : ℂ => a + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add a
  have hn : HasDerivAt (fun t : ℂ => G 1 0 + G 1 1 * (a + t)) (G 1 1) 0 := by
    simpa using (hl.const_mul (G 1 1)).const_add (G 1 0)
  have hd : HasDerivAt (fun t : ℂ => den G (a + t)) (G 0 1) 0 := by
    simpa [den] using (hl.const_mul (G 0 1)).const_add (G 0 0)
  have h0 : den G (a + 0) ≠ 0 := by simpa using h
  have key := hn.div hd h0
  have e : mobD G a = (G 1 1 * den G (a + 0) - (G 1 0 + G 1 1 * (a + 0)) * G 0 1) / den G (a + 0) ^ 2 := by
    simp only [add_zero]
    unfold mobD
    rw [Matrix.det_fin_two]
    congr 1
    unfold den
    ring
  rw [e]
  exact key

theorem jacC_apply_of_line {D E : ℕ} (F : (Fin D → ℂ) → Fin E → ℂ) (z : Fin D → ℂ)
    (hF : DifferentiableAt ℂ F z) (a : Fin E) (k : Fin D) (c : ℂ)
    (h : HasDerivAt (fun t : ℂ => F (z + t • (Pi.single k 1 : Fin D → ℂ)) a) c 0) :
    ReciprocityTheory.AnForm.A.jacC F z a k = c := by
  have hl : HasDerivAt (fun t : ℂ => z + t • (Pi.single k 1 : Fin D → ℂ)) (Pi.single k 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single k 1 : Fin D → ℂ)).const_add z
  have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • (Pi.single k 1 : Fin D → ℂ)) := by
    simpa using hF.hasFDerivAt
  have h2 := hF'.comp_hasDerivAt (0 : ℂ) hl
  have h3 := (hasDerivAt_pi.1 h2) a
  exact h3.unique h

theorem mobius_pair_line_first_axis {d : ℕ} (y : Fin d → ℂ) (a₀ a₁ t : ℂ) :
    (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) + t • (Pi.single 0 1 : Fin (d + 2) → ℂ) =
      Fin.cons (a₀ + t) (Fin.cons a₁ y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Pi.single_apply, Fin.succ_ne_zero]

theorem mobius_pair_line_second_axis {d : ℕ} (y : Fin d → ℂ) (a₀ a₁ t : ℂ) :
    (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) + t • (Pi.single 1 1 : Fin (d + 2) → ℂ) =
      Fin.cons a₀ (Fin.cons (a₁ + t) y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Pi.single_apply]
  · refine Fin.cases ?_ (fun l => ?_) j
    · simp [Pi.single_apply]
    · have : (l.succ.succ : Fin (d + 2)) ≠ 1 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [Pi.single_apply, this]

theorem mobius_pair_cons {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ) (b₀ b₁ : ℂ) :
    mob2 g (Fin.cons b₀ (Fin.cons b₁ y)) = Fin.cons (mob (g y) b₀) (Fin.cons (mob (g y) b₁) y) := rfl

theorem analyticAt_mobius_pair {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a₀ a₁ : ℂ)
    (h₀ : den (g y) a₀ ≠ 0) (h₁ : den (g y) a₁ ≠ 0) :
    AnalyticAt ℂ (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) := by
  set z₀ : Fin (d + 2) → ℂ := Fin.cons a₀ (Fin.cons a₁ y) with hz₀
  have hcoord : ∀ i : Fin (d + 2), AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => z i) z₀ := fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 2) => ℂ) i).analyticAt z₀
  have hT : AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) z₀ := by
    rw [analyticAt_pi_iff]
    intro i
    exact hcoord i.succ.succ
  have hTz : Fin.tail (Fin.tail z₀) = y := by
    simp [hz₀]
  have hga : ∀ p q, AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => g (Fin.tail (Fin.tail z)) p q) z₀ := by
    intro p q
    have h1 : AnalyticAt ℂ (fun y' => g y' p q) (Fin.tail (Fin.tail z₀)) :=
      ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn _ (Set.mem_univ _)
    exact AnalyticAt.comp (f := fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) h1 hT
  have hm : ∀ i : Fin (d + 2), den (g y) (z₀ i) ≠ 0 →
      AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => mob (g (Fin.tail (Fin.tail z))) (z i)) z₀ := by
    intro i hi
    unfold mob den
    refine AnalyticAt.div ?_ ?_ ?_
    · exact (hga 1 0).add ((hga 1 1).mul (hcoord i))
    · exact (hga 0 0).add ((hga 0 1).mul (hcoord i))
    · rw [hTz]
      exact hi
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hm 0 (by simpa [hz₀] using h₀)
  · refine Fin.cases ?_ (fun l => ?_) j
    · exact hm 1 (by simpa [hz₀] using h₁)
    · exact hcoord l.succ.succ

theorem det_jacobian_mobius_pair {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a₀ a₁ : ℂ)
    (h₀ : den (g y) a₀ ≠ 0) (h₁ : den (g y) a₁ ≠ 0) :
    (ReciprocityTheory.AnForm.A.jacC (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det =
      mobD (g y) a₀ * mobD (g y) a₁ := by
  have hdiff : DifferentiableAt ℂ (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) :=
    (analyticAt_mobius_pair g hg y a₀ a₁ h₀ h₁).differentiableAt
  set J := ReciprocityTheory.AnForm.A.jacC (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) with hJ
  have hJ00 : J 0 0 = mobD (g y) a₀ := by
    refine jacC_apply_of_line _ _ hdiff 0 0 _ ?_
    simp only [mobius_pair_line_first_axis, mobius_pair_cons]
    simpa using hasDerivAt_mob_line (g y) a₀ h₀
  have hJ11 : J 1 1 = mobD (g y) a₁ := by
    refine jacC_apply_of_line _ _ hdiff 1 1 _ ?_
    simp only [mobius_pair_line_second_axis, mobius_pair_cons]
    simpa using hasDerivAt_mob_line (g y) a₁ h₁
  have hJ10 : J 1 0 = 0 := by
    refine jacC_apply_of_line _ _ hdiff 1 0 _ ?_
    simp only [mobius_pair_line_first_axis, mobius_pair_cons]
    simpa using hasDerivAt_const (0 : ℂ) (mob (g y) a₁)
  have hJss : ∀ (i : Fin d) (k : Fin (d + 2)), J i.succ.succ k = (Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ := by
    intro i k
    refine jacC_apply_of_line _ _ hdiff _ _ _ ?_
    have e : (fun t : ℂ => mob2 g ((Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) +
        t • (Pi.single k 1 : Fin (d + 2) → ℂ)) i.succ.succ) =
        fun t : ℂ => y i + t * (Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ := by
      funext t
      simp [mob2, Fin.tail]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const ((Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ)).const_add (y i)
  have hc0 : ∀ i : Fin (d + 1), J i.succ 0 = 0 := by
    intro i
    refine Fin.cases ?_ (fun l => ?_) i
    · exact hJ10
    · rw [hJss]
      simp [Pi.single_apply, Fin.succ_ne_zero]
  have hc1 : ∀ i : Fin d, (J.submatrix Fin.succ Fin.succ) i.succ 0 = 0 := by
    intro i
    simp only [Matrix.submatrix_apply]
    rw [hJss]
    have : (i.succ.succ : Fin (d + 2)) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [Pi.single_apply, this]
  have hlast : ((J.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ) = 1 := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [hJss]
    simp [Pi.single_apply, Matrix.one_apply]
  rw [det_eq_mul_minor_of_col_zero J hc0, det_eq_mul_minor_of_col_zero _ hc1, hlast, Matrix.det_one, mul_one,
    hJ00]
  simp only [Matrix.submatrix_apply]
  congr 1

theorem mobius_pair_analyticAt_and_det_jacobian : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a₀ a₁ : ℂ),
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₀ ≠ 0 → GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₁ ≠ 0 →
    AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) ∧
    (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det =
      GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₀ * GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₁ :=
  fun _ g hg y a₀ a₁ h₀ h₁ => ⟨analyticAt_mobius_pair g hg y a₀ a₁ h₀ h₁, det_jacobian_mobius_pair g hg y a₀ a₁ h₀ h₁⟩

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
