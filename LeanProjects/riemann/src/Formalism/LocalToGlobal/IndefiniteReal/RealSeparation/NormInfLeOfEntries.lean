import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Continuous

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {D : D7}

theorem rect_entry_mul_le {m n p : ℕ} (φ : AE D →+* ℂ) (X : Matrix (Fin m) (Fin n) (AE D))
    (Y : Matrix (Fin n) (Fin p) (AE D)) (i : Fin m) (j : Fin p) {bX bY : ℝ}
    (hX : ∀ i k, ‖φ (X i k)‖ ≤ bX) (hY : ∀ k j, ‖φ (Y k j)‖ ≤ bY) : ‖φ ((X * Y) i j)‖ ≤ n * (bX * bY) := by
  rw [Matrix.mul_apply, map_sum]
  calc ‖∑ e, φ (X i e * Y e j)‖ ≤ ∑ e : Fin n, ‖φ (X i e * Y e j)‖ := norm_sum_le _ _
    _ ≤ ∑ _e : Fin n, bX * bY := Finset.sum_le_sum fun e _ => by
        rw [map_mul, norm_mul]
        exact mul_le_mul (hX i e) (hY e j) (norm_nonneg _) ((norm_nonneg _).trans (hX i e))
    _ = n * (bX * bY) := by simp [Finset.sum_const, nsmul_eq_mul]

theorem entry_le_sum {m n : ℕ} (f : Fin m → Fin n → ℝ) (hf : ∀ i j, 0 ≤ f i j) (i : Fin m) (j : Fin n) :
    f i j ≤ ∑ i', ∑ j', f i' j' :=
  (Finset.single_le_sum (fun j' _ => hf i j') (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i' => ∑ j', f i' j') (fun i' _ => Finset.sum_nonneg fun j' _ => hf i' j')
      (Finset.mem_univ i))

variable {A T : HSp D} {ι : A.V →ₗ[D.host.E] T.V} {s : GA D A →* GA D T}

set_option maxHeartbeats 2000000 in

theorem s_entry_le (θ : InfFam D) (hι : HSpace.IsIsomEmb A T ι) (hemb : IsEmbHom ι s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : GA D A) (τ : D.what₂.Tau) (b : ℝ), 0 ≤ b →
      (∀ k l, ‖θ τ (infPart D (mt A h k l))‖ ≤ b) → ∀ i j, ‖θ τ (infPart D (mt T (s h) i j))‖ ≤ C * (b + 1) := by
  set F := (frameMat T A ι).map (incA D)
  set P := (embP' A T ι).map (incA D)
  set Q := (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) - (frameMat T A ι * embP' A T ι).map (incA D)
  let φ : D.what₂.Tau → AE D →+* ℂ := fun τ => (θ τ).comp (infPart D)
  let bF : D.what₂.Tau → ℝ := fun τ => ∑ i, ∑ k, ‖φ τ (F i k)‖
  let bP : D.what₂.Tau → ℝ := fun τ => ∑ k, ∑ j, ‖φ τ (P k j)‖
  let cQ : D.what₂.Tau → ℝ := fun τ => ∑ i, ∑ j, ‖φ τ (Q i j)‖
  have hbF0 : ∀ τ, 0 ≤ bF τ := fun τ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbP0 : ∀ τ, 0 ≤ bP τ := fun τ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcQ0 : ∀ τ, 0 ≤ cQ τ := fun τ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  let C : ℝ := ∑ τ, ((A.rank : ℝ) * ((A.rank : ℝ) * bF τ) * bP τ + cQ τ)
  have hterm0 : ∀ τ, 0 ≤ (A.rank : ℝ) * ((A.rank : ℝ) * bF τ) * bP τ + cQ τ := fun τ => by
    have := hbF0 τ; have := hbP0 τ; have := hcQ0 τ; positivity
  have hCτ : ∀ τ, (A.rank : ℝ) * ((A.rank : ℝ) * bF τ) * bP τ + cQ τ ≤ C := fun τ =>
    Finset.single_le_sum (fun τ' _ => hterm0 τ') (Finset.mem_univ τ)
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun τ _ => hterm0 τ
  refine ⟨C, hC0, fun h τ b hb hh i j => ?_⟩
  rw [mt_of_embRel hι (hemb h)]
  have hFe : ∀ i k, ‖φ τ (F i k)‖ ≤ bF τ := fun i k =>
    entry_le_sum (fun i k => ‖φ τ (F i k)‖) (fun _ _ => norm_nonneg _) i k
  have hPe : ∀ k j, ‖φ τ (P k j)‖ ≤ bP τ := fun k j =>
    entry_le_sum (fun k j => ‖φ τ (P k j)‖) (fun _ _ => norm_nonneg _) k j
  have hQe : ‖φ τ (Q i j)‖ ≤ cQ τ := entry_le_sum (fun i j => ‖φ τ (Q i j)‖) (fun _ _ => norm_nonneg _) i j
  have hFM : ∀ i l, ‖φ τ ((F * mt A h) i l)‖ ≤ A.rank * (bF τ * b) := fun i l =>
    rect_entry_mul_le (φ τ) F (mt A h) i l hFe hh
  have hFMP : ‖φ τ ((F * mt A h * P) i j)‖ ≤ A.rank * ((A.rank * (bF τ * b)) * bP τ) :=
    rect_entry_mul_le (φ τ) (F * mt A h) P i j hFM hPe
  have hsum : ‖φ τ ((F * mt A h * P + Q) i j)‖ ≤ A.rank * ((A.rank * (bF τ * b)) * bP τ) + cQ τ := by
    rw [Matrix.add_apply, map_add]
    exact (norm_add_le _ _).trans (add_le_add hFMP hQe)
  show ‖φ τ ((F * mt A h * P + Q) i j)‖ ≤ C * (b + 1)
  refine hsum.trans ?_
  have h1 := hCτ τ
  have hA0 : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
  set X : ℝ := (A.rank : ℝ) * ((A.rank : ℝ) * bF τ) * bP τ with hXd
  have hX0 : 0 ≤ X := mul_nonneg (mul_nonneg hA0 (mul_nonneg hA0 (hbF0 τ))) (hbP0 τ)
  have e : (A.rank : ℝ) * ((A.rank : ℝ) * (bF τ * b) * bP τ) + cQ τ = X * b + cQ τ := by rw [hXd]; ring
  rw [e]
  have hX : X ≤ C := le_trans (le_add_of_nonneg_right (hcQ0 τ)) h1
  have hY : cQ τ ≤ C := le_trans (le_add_of_nonneg_left hX0) h1
  nlinarith [mul_le_mul_of_nonneg_right hX hb]

theorem normInf_le_of_entries (θ : InfFam D) (V : HSp D) (x : GA D V) (B : ℝ)
    (hB : ∀ τ i j, ‖θ τ (infPart D (mt V x i j))‖ ≤ B ∧ ‖θ τ (infPart D (mt V x⁻¹ i j))‖ ≤ B) :
    normInf θ V x ≤ Fintype.card D.what₂.Tau * (V.rank * (V.rank * (B + B))) := by
  unfold normInf
  calc ∑ τ, ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) x i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) x⁻¹ i j‖)
      ≤ ∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (B + B) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [infMat_eq, infMat_eq]; exact add_le_add (hB τ i j).1 (hB τ i j).2
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

end Formalism.IndefR.Mi

end
