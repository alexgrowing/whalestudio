import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Letter
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Assemble
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.GeneratingFunctionPolynomial

noncomputable section

namespace CompanionTheory.WaveGrid.SpanBall

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P PI.UpqRep Matrix CompanionTheory.LimBd.Main CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace

def steps (n : ℕ) : Finset (Fin n → ℤ) :=
  insert 0 (Finset.univ.image (fun s : Fin n => (Pi.single s 1 : Fin n → ℤ)) ∪
    Finset.univ.image fun s : Fin n => -(Pi.single s 1 : Fin n → ℤ))

def ball (n : ℕ) : ℕ → Finset (Fin n → ℤ)
  | 0 => {0}
  | e + 1 => Finset.image₂ (· + ·) (ball n e) (steps n)

theorem zero_mem_steps (n : ℕ) : (0 : Fin n → ℤ) ∈ steps n := Finset.mem_insert_self _ _

theorem single_mem_steps {n : ℕ} (s : Fin n) : (Pi.single s 1 : Fin n → ℤ) ∈ steps n :=
  Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ s)))

theorem neg_single_mem_steps {n : ℕ} (s : Fin n) : -(Pi.single s 1 : Fin n → ℤ) ∈ steps n :=
  Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ s)))

theorem card_steps (n : ℕ) : (steps n).card ≤ 2 * n + 1 := by
  refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ((Finset.card_union_le _ _).trans ?_) 1)
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun s : Fin n => (Pi.single s 1 : Fin n → ℤ))
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
    (f := fun s : Fin n => -(Pi.single s 1 : Fin n → ℤ))
  rw [Finset.card_univ, Fintype.card_fin] at h1 h2
  omega

theorem card_ball (n : ℕ) : ∀ e, (ball n e).card ≤ (2 * n + 1) ^ e
  | 0 => by simp [ball]
  | e + 1 => by
    rw [pow_succ]
    exact Finset.card_image₂_le _ _ _ |>.trans (Nat.mul_le_mul (card_ball n e) (card_steps n))

theorem sum_natAbs_le_one_of_mem_unitShifts {n : ℕ} {s : Fin n → ℤ} (h : s ∈ steps n) : ∑ i, (s i).natAbs ≤ 1 := by
  have key : ∀ t : Fin n, ∑ i, ((Pi.single t 1 : Fin n → ℤ) i).natAbs = 1 := fun t => by
    rw [Finset.sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]
    simp
  simp only [steps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · simp
  · exact (key t).le
  · simpa only [Pi.neg_apply, Int.natAbs_neg] using (key t).le

theorem sum_natAbs_le_of_mem_ball {n : ℕ} : ∀ e, ∀ ν ∈ ball n e, ∑ i, (ν i).natAbs ≤ e
  | 0, ν, h => by
    rw [ball, Finset.mem_singleton] at h
    simp [h]
  | e + 1, ν, h => by
    obtain ⟨x, hx, s, hs, rfl⟩ := Finset.mem_image₂.1 h
    have h1 := sum_natAbs_le_of_mem_ball e x hx
    have h2 := sum_natAbs_le_one_of_mem_unitShifts hs
    have h3 : ∑ i, ((x + s) i).natAbs ≤ ∑ i, (x i).natAbs + ∑ i, (s i).natAbs := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _
    omega

theorem abs_ball {n e : ℕ} {ν : Fin n → ℤ} (h : ν ∈ ball n e) (a : Fin n) : |(ν a : ℝ)| ≤ e := by
  have h1 : (ν a).natAbs ≤ e := le_trans
    (Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (sum_natAbs_le_of_mem_ball e ν h)
  have h2 : (((ν a).natAbs : ℕ) : ℝ) ≤ e := by exact_mod_cast h1
  rwa [Nat.cast_natAbs, Int.cast_abs] at h2

theorem add_single {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) :
    μ + Pi.single s 1 = fun a => μ a + ((Pi.single s 1 : Fin n → ℤ) a : ℝ) := by
  funext a
  by_cases h : a = s
  · subst h; simp
  · simp [h]

theorem sub_single {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) :
    μ - Pi.single s 1 = fun a => μ a + ((-(Pi.single s 1 : Fin n → ℤ)) a : ℝ) := by
  funext a
  by_cases h : a = s
  · subst h; simp [sub_eq_add_neg]
  · simp [h]

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

def spanOn (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (S : Finset (Fin (2 * r + k + 1) → ℤ)) : Submodule ℂ (B.Mat k r → ℂ) :=
  Submodule.span ℂ {φ | ∃ ν ∈ S, IsCoef k r ε (fun a => lam a + (ν a : ℝ)) φ}

theorem mem_spanStep_of_eq {μ : Fin (2 * r + k + 1) → ℝ} {φ ψ ψ' : B.Mat k r → ℂ} (hφ : IsCoef k r ε μ φ)
    (hψ' : ψ' ∈ spanOn k r ε μ (steps _)) (h : ∀ g ∈ B.GV k r, ψ g = ψ' g) : ψ ∈ spanOn k r ε μ (steps _) := by
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, hσ, -, hw, -⟩ := hφ
  have h1 : IsCoef k r ε μ (ψ - ψ') :=
    ⟨H, i1, i2, i3, σ, 0, w, hμ, hσ, kfin_zero σ, hw, fun g hg => by simp [h g hg]⟩
  have h0 : ψ - ψ' ∈ spanOn k r ε μ (steps _) := Submodule.subset_span ⟨0, zero_mem_steps _, by simpa using h1⟩
  simpa using Submodule.add_mem _ h0 hψ'

theorem letterStep {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) {μ : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} {q φ : B.Mat k r → ℂ} (hq : IsLetter k r q) (hφ : IsCoef k r ε μ φ) (hg : PI.ZuckTensor.GapAtLeast ε μ h)
    (hlt : t _ ε + 1 < h) : q * φ ∈ spanOn k r ε μ (steps _) := by
  rcases hq with rfl | ⟨x, y, hq⟩
  · rw [one_mul]
    exact Submodule.subset_span ⟨0, zero_mem_steps _, by simpa using hφ⟩
  have hφ' := hφ
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, ⟨P, hP, hτ⟩, hv, hw, hφG⟩ := hφ'
  rw [kfin_iff hP] at hv hw
  rcases hq with hq | hq
  · obtain ⟨X⟩ := hZ _ ε μ H _ hμ hτ h hg hlt
    obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (P *ᵥ x) (P *ᵥ y) hv hw
    refine mem_spanStep_of_eq hφ (ψ' := ∑ i, fun g => ⟪wI i, X.σs (sI i) (P * g * P⁻¹) (vI i)⟫_ℂ)
      (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, single_mem_steps (sI i),
        add_single μ (sI i) ▸ isCoef_of_J hP (X.ds _ (hI i).1).1 (X.ds _ (hI i).1).2 (hI i).2.1 (hI i).2.2⟩) fun g hgG => ?_
    have := hsum _ (forth_mem hP.1 hgG)
    simp only [back_forth hP.1, dot_transport hP] at this
    rw [Pi.mul_apply, hq g hgG, hφG g hgG, mul_comm, this, Finset.sum_apply]
  · obtain ⟨X⟩ := hZd _ ε μ H _ hμ hτ h hg hlt
    obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (P *ᵥ x) (P *ᵥ y) hv hw
    refine mem_spanStep_of_eq hφ (ψ' := ∑ i, fun g => ⟪wI i, X.σs (sI i) (P * g * P⁻¹) (vI i)⟫_ℂ)
      (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, neg_single_mem_steps (sI i),
        sub_single μ (sI i) ▸ isCoef_of_J hP (X.ds _ (hI i).1).1 (X.ds _ (hI i).1).2 (hI i).2.1 (hI i).2.2⟩) fun g hgG => ?_
    have := hsum _ (forth_mem hP.1 hgG)
    have hi : (P * g * P⁻¹)⁻¹ = P * g⁻¹ * P⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1.1), Matrix.mul_assoc]
    simp only [back_forth hP.1, hi, dot_transport hP] at this
    rw [Pi.mul_apply, hq g hgG, hφG g hgG, mul_comm, this, Finset.sum_apply]

theorem spanBall {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) {lam : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} (d : ℕ) {q φ : B.Mat k r → ℂ} (hq : q ∈ Letters k r ^ d) (hφ : IsCoef k r ε lam φ)
    (hg : PI.ZuckTensor.GapAtLeast ε lam h) (hlt : t _ ε + 1 + 2 * (d : ℝ) < h) :
    q * φ ∈ spanOn k r ε lam (ball _ d) := by
  induction d generalizing q with
  | zero =>
    rw [pow_zero, Submodule.mem_one] at hq
    obtain ⟨c, rfl⟩ := hq
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, Finset.mem_singleton_self _, by simpa using hφ⟩)
  | succ d ih =>
    push_cast at hlt
    have step : Letters k r * spanOn k r ε lam (ball _ d) ≤ spanOn k r ε lam (ball _ (d + 1)) := by
      unfold Letters
      rw [spanOn, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨a, ha, b, ⟨ν, hν, hb⟩, rfl⟩
      have hgμ : PI.ZuckTensor.GapAtLeast ε (fun a => lam a + (ν a : ℝ)) (h - 2 * d) :=
        gap_of_box (lam := lam) (μ := fun a => lam a + (ν a : ℝ)) (c := d) (fun s => by simpa using abs_ball hν s) hg (by linarith)
      refine Submodule.span_mono ?_ (letterStep hZ hZd ha hb hgμ (by linarith))
      rintro ψ ⟨s, hs, hψ⟩
      refine ⟨ν + s, Finset.mem_image₂_of_mem hν hs, ?_⟩
      simpa only [Pi.add_apply, Int.cast_add, add_assoc] using hψ
    rw [pow_succ'] at hq
    refine Submodule.mul_induction_on hq (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [mul_assoc]
      exact step (Submodule.mul_mem_mul ha (ih hb (by linarith)))
    · rw [add_mul]
      exact Submodule.add_mem _ ha hb

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sumOn (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (S : Finset (Fin (2 * r + k + 1) → ℤ)) : Submodule ℂ (B.Mat k r → (Wq →L[ℂ] Wp)) where
  carrier := {G | ∃ F : (Fin (2 * r + k + 1) → ℤ) → B.Mat k r → (Wq →L[ℂ] Wp),
    (∀ ν, F ν ∈ Wsp k r Wp Wq ε fun a => lam a + (ν a : ℝ)) ∧ G = ∑ ν ∈ S, F ν}
  add_mem' := by
    rintro _ _ ⟨F, hF, rfl⟩ ⟨F', hF', rfl⟩
    exact ⟨F + F', fun ν => Submodule.add_mem _ (hF ν) (hF' ν), by simp [Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
  smul_mem' := by
    rintro c _ ⟨F, hF, rfl⟩
    exact ⟨c • F, fun ν => Submodule.smul_mem _ c (hF ν), by simp [Finset.smul_sum]⟩

theorem smul_mem_sumOn {lam : Fin (2 * r + k + 1) → ℝ} {S : Finset (Fin (2 * r + k + 1) → ℤ)} {φ : B.Mat k r → ℂ}
    (hφ : φ ∈ spanOn k r ε lam S) (T : Wq →L[ℂ] Wp) : (fun g => φ g • T) ∈ sumOn k r Wp Wq ε lam S := by
  classical
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ν, hν, h⟩ := h
    refine ⟨fun ν' => if ν' = ν then fun g => φ g • T else 0, fun ν' => ?_, by simp [hν]⟩
    dsimp only
    split_ifs with e
    · subst e
      exact Submodule.subset_span ⟨φ, T, h, rfl⟩
    · exact Submodule.zero_mem _
  | zero =>
    convert Submodule.zero_mem _ using 2 with g
    simp
  | add φ ψ _ _ h h' =>
    convert Submodule.add_mem _ h h' using 2 with g
    simp [add_smul]
  | smul c φ _ h =>
    convert Submodule.smul_mem _ c h using 2 with g
    simp [smul_smul]

theorem mul_mem_sumOn {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t)
    {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ} {d : ℕ} {q : B.Mat k r → ℂ} (hq : q ∈ Letters k r ^ d)
    (hg : PI.ZuckTensor.GapAtLeast ε lam h) (hlt : t _ ε + 1 + 2 * (d : ℝ) < h) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ Wsp k r Wp Wq ε lam) : (fun g => q g • F g) ∈ sumOn k r Wp Wq ε lam (ball _ d) := by
  induction hF using Submodule.span_induction with
  | mem F h' =>
    obtain ⟨φ, T, hφ, rfl⟩ := h'
    convert smul_mem_sumOn (spanBall hZ hZd d hq hφ hg hlt) T using 2 with g
    rw [smul_smul, Pi.mul_apply]
  | zero =>
    convert Submodule.zero_mem _ using 2 with g
    simp
  | add F F' _ _ h h' =>
    convert Submodule.add_mem _ h h' using 2 with g
    simp
  | smul c F _ h =>
    convert Submodule.smul_mem _ c h using 2 with g
    simp only [Pi.smul_apply]
    rw [smul_comm]

end CompanionTheory.WaveGrid.SpanBall
