import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.CoefXHasDeriv

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace TDAux

section Frob
variable {n : ℕ}

theorem frob_eq (g : Matrix (Fin n) (Fin n) ℂ) : frob g = Real.sqrt (Formalism.REAL.hs g) := rfl

theorem frob_mul_le (A B : Matrix (Fin n) (Fin n) ℂ) : frob (A * B) ≤ frob A * frob B := by
  let _ : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  have hf : ∀ A : Matrix (Fin n) (Fin n) ℂ, frob A = ‖A‖ := by
    intro A
    rw [Matrix.frobenius_norm_def, frob, Real.sqrt_eq_rpow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Real.rpow_two]
  rw [hf, hf, hf]
  exact Matrix.frobenius_norm_mul A B

theorem entry_le_frob (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ≤ frob g := by
  rw [frob]
  apply Real.le_sqrt_of_sq_le
  have h1 : ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j', ‖g i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  linarith

theorem frob_ge_one {ε : Fin n → Bool} (hn : 1 ≤ n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    1 ≤ frob g := by
  rw [frob_eq]
  have h := Formalism.REAL.dim_le_frobenius hg
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.one_le_sqrt]
  linarith

theorem frob_pos {ε : Fin n → Bool} (hn : 1 ≤ n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    0 < frob g := lt_of_lt_of_le one_pos (frob_ge_one hn hg)

end Frob

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem n_pos : 1 ≤ 2 * r + k + 1 := by omega

theorem JgJ_entry (g : Mat k r) (i j : Fin (2 * r + k + 1)) :
    ‖(Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) i j‖ = ‖g j i‖ := by
  have e : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) i j =
      (if ε i then 1 else -1) * star (g j i) * (if ε j then 1 else -1) := by
    simp [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [e, norm_mul, norm_mul, norm_star]
  have n1 : ∀ b : Bool, ‖(if b = true then (1 : ℂ) else -1)‖ = 1 := by
    intro b; cases b <;> simp
  rw [n1, n1, one_mul, mul_one]

theorem cJd_bound (x₁ : Fin (2 * r + k + 1) → ℂ) (c : Fin (2 * r + k + 1)) {g : Mat k r}
    (hg : Formalism.REAL.inUJ ε g) : ‖cJd x₁ (Pi.single c 1) g‖ ≤ (∑ j, ‖x₁ j‖) * frob g := by
  rw [cJd_eq x₁ _ hg, cL, single_dotProduct, one_mul, Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, JgJ_entry, mul_comm]
  exact mul_le_mul_of_nonneg_left (entry_le_frob g j c) (norm_nonneg _)

theorem frob_translate_le {a : ℝ} (ha : 0 ≤ a) {x₀ g : Mat k r} (hx₀ : Formalism.REAL.inUJ ε x₀)
    (hg : Formalism.REAL.inUJ ε g) : frob (x₀⁻¹ * g) ^ (-a) ≤ frob x₀ ^ a * frob g ^ (-a) := by
  have hy := Formalism.REAL.indefinite_unitary_mul_mem ε (inv_mem hx₀) hg
  have hp := frob_pos n_pos hy
  have hq := frob_pos n_pos hx₀
  have hG := frob_pos n_pos hg
  have hle : frob g ≤ frob x₀ * frob (x₀⁻¹ * g) := by
    have e : g = x₀ * (x₀⁻¹ * g) := by rw [← Matrix.mul_assoc, mul_inv_self' hx₀, Matrix.one_mul]
    conv_lhs => rw [e]
    exact frob_mul_le _ _
  have h1 : frob g / frob x₀ ≤ frob (x₀⁻¹ * g) := by
    rw [div_le_iff₀ hq]; linarith
  have h2 := Real.rpow_le_rpow_of_nonpos (div_pos hG hq) h1 (neg_nonpos.mpr ha)
  rw [Real.div_rpow hG.le hq.le, Real.rpow_neg hq.le, div_inv_eq_mul] at h2
  rwa [mul_comm (frob x₀ ^ a)]

end TDAux

namespace TDAux

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def Qp (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x₀ : Mat k r) (w : H) (a : ℝ) (m : H) : Prop :=
  Formalism.REAL.SmoothOnG ε (coefX σ x₀ w m) ∧
    ∃ C : ℝ, ∀ g, Formalism.REAL.inUJ ε g → ‖coefX σ x₀ w m g‖ ≤ C * frob g ^ (-a)

theorem Qp_zero (σ : Mat k r → (H →L[ℂ] H)) (x₀ : Mat k r) (w : H) (a : ℝ) : Qp ε σ x₀ w a 0 := by
  have e : coefX σ x₀ w 0 = fun _ => 0 := by funext g; simp [coefX]
  refine ⟨?_, 0, fun g _ => ?_⟩
  · rw [e]; exact Formalism.REAL.smooth_on_group_const_fun 0
  · rw [e]; simp

theorem Qp_add_smul {σ : Mat k r → (H →L[ℂ] H)} {x₀ : Mat k r} {w : H} {a : ℝ} {m₁ m₂ : H} (c : ℂ)
    (h₁ : Qp ε σ x₀ w a m₁) (h₂ : Qp ε σ x₀ w a m₂) : Qp ε σ x₀ w a (m₁ + c • m₂) := by
  have e : coefX σ x₀ w (m₁ + c • m₂) = fun g => coefX σ x₀ w m₁ g + c * coefX σ x₀ w m₂ g := by
    funext g; exact coefX_add_smul σ x₀ w m₁ m₂ c g
  obtain ⟨s₁, C₁, b₁⟩ := h₁
  obtain ⟨s₂, C₂, b₂⟩ := h₂
  refine ⟨?_, C₁ + ‖c‖ * C₂, fun g hg => ?_⟩
  · rw [e]; exact Formalism.REAL.smooth_on_group_add s₁ (Formalism.REAL.smooth_on_group_const_mul c s₂)
  · rw [e]
    calc ‖coefX σ x₀ w m₁ g + c * coefX σ x₀ w m₂ g‖ ≤ ‖coefX σ x₀ w m₁ g‖ + ‖c‖ * ‖coefX σ x₀ w m₂ g‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ C₁ * frob g ^ (-a) + ‖c‖ * (C₂ * frob g ^ (-a)) := by
          gcongr
          · exact b₁ g hg
          · exact b₂ g hg
      _ = (C₁ + ‖c‖ * C₂) * frob g ^ (-a) := by ring

theorem Qp_word {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hE : IsDerivedOn ε σ D E) {x₀ : Mat k r}
    (hx₀ : Formalism.REAL.inUJ ε x₀) {ψ : Mat k r → ℂ} {v : D} {w : H}
    (hcoef : ∀ y, Formalism.REAL.inUJ ε y → coefX σ x₀ w (v : H) y = ψ (x₀⁻¹ * y))
    (hψs : Formalism.REAL.SmoothOnG ε ψ) {a : ℝ} (ha : 0 ≤ a)
    (hψd : ∀ wd, ∃ C : ℝ, ∀ y, Formalism.REAL.inUJ ε y → ‖Formalism.REAL.Eword ε wd ψ y‖ ≤ C * frob y ^ (-a))
    (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    Qp ε σ x₀ w a ((Ewd E wd v : D) : H) := by
  have e : ∀ g, Formalism.REAL.inUJ ε g → coefX σ x₀ w ((Ewd E wd v : D) : H) g =
      Formalism.REAL.Eword ε wd (fun y => ψ (x₀⁻¹ * y)) g := by
    intro g hg
    rw [← coefX_Eword hσ hE hx₀ w v wd g hg]
    exact eword_congr hcoef wd g hg
  refine ⟨Formalism.REAL.smooth_on_group_congr (Formalism.REAL.smooth_iterated_lie_derivative (smooth_left hψs (inv_mem hx₀)) wd)
    (fun g hg => (e g hg).symm), ?_⟩
  obtain ⟨C, hC⟩ := hψd wd
  refine ⟨max C 0 * frob x₀ ^ a, fun g hg => ?_⟩
  rw [e g hg, eword_left]
  have hy := Formalism.REAL.indefinite_unitary_mul_mem ε (inv_mem hx₀) hg
  have hp : 0 ≤ frob (x₀⁻¹ * g) ^ (-a) := Real.rpow_nonneg (frob_pos n_pos hy).le _
  calc ‖Formalism.REAL.Eword ε wd ψ (x₀⁻¹ * g)‖ ≤ C * frob (x₀⁻¹ * g) ^ (-a) := hC _ hy
    _ ≤ max C 0 * frob (x₀⁻¹ * g) ^ (-a) := mul_le_mul_of_nonneg_right (le_max_left _ _) hp
    _ ≤ max C 0 * (frob x₀ ^ a * frob g ^ (-a)) :=
        mul_le_mul_of_nonneg_left (frob_translate_le ha hx₀ hg) (le_max_right _ _)
    _ = max C 0 * frob x₀ ^ a * frob g ^ (-a) := by ring

theorem genSub_le_span {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (V : Submodule ℂ M) :
    genSub E V ≤ Submodule.span ℂ {x | ∃ v ∈ V, ∃ wd, x = Ewd E wd v} := by
  refine sInf_le ⟨fun v hv => Submodule.subset_span ⟨v, hv, [], rfl⟩, fun a b x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v, hv, wd, rfl⟩ := hx
      exact Submodule.subset_span ⟨v, hv, (a, b) :: wd, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem Qp_genSub {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D} {V : Submodule ℂ D}
    {x₀ : Mat k r} {w : H} {a : ℝ}
    (hV : ∀ v ∈ V, ∀ wd, Qp ε σ x₀ w a ((Ewd E wd v : D) : H)) :
    ∀ m ∈ genSub E V, Qp ε σ x₀ w a (m : H) := by
  intro m hm
  have hm' := genSub_le_span E V hm
  clear hm
  induction hm' using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v, hv, wd, rfl⟩ := hx
      exact hV v hv wd
  | zero => simpa using Qp_zero (ε := ε) σ x₀ w a
  | add x y _ _ hx hy =>
      have := Qp_add_smul 1 hx hy
      simpa using this
  | smul c x _ hx =>
      have := Qp_add_smul c (Qp_zero (ε := ε) σ x₀ w a) hx
      simpa using this

end TDAux

namespace TDAux

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def Fw {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) :
    List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → (Fin (2 * r + k + 1) → M) → (Fin (2 * r + k + 1) → M)
  | [] => id
  | p :: wd => fun f => LemK.tensVd E p.1 p.2 (Fw E wd f)

theorem tMapD_Eword {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hE : IsDerivedOn ε σ D E) {x₀ : Mat k r}
    (hx₀ : Formalism.REAL.inUJ ε x₀) (x₁ : Fin (2 * r + k + 1) → ℂ) (w : H) (f : Fin (2 * r + k + 1) → D) :
    ∀ (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (g : Mat k r), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε wd (tMapD σ x₁ x₀ w (fun c => (f c : H))) g =
        tMapD σ x₁ x₀ w (fun c => ((Fw E wd f c : D) : H)) g
  | [], _, _ => rfl
  | p :: wd, g, hg => by
      show Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε wd (tMapD σ x₁ x₀ w (fun c => (f c : H)))) g = _
      rw [Formalism.REAL.lie_derivative_congr p.1 p.2 (fun x hx => tMapD_Eword hσ hE hx₀ x₁ w f wd x hx) hg]
      exact tMapD_Eab hσ hE hx₀ hg x₁ w (Fw E wd f) p.1 p.2

theorem genSub_stable {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (V : Submodule ℂ M)
    (a b : Fin (2 * r + k + 1)) {x : M} (hx : x ∈ genSub E V) : E a b x ∈ genSub E V := by
  rw [genSub, Submodule.mem_sInf] at hx ⊢
  intro T hT
  exact hT.2 a b x (hx T hT)

theorem Fw_mem {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (V : Submodule ℂ M)
    {f : Fin (2 * r + k + 1) → M} (hf : ∀ c, f c ∈ genSub E V) :
    ∀ (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) c, Fw E wd f c ∈ genSub E V
  | [], c => hf c
  | p :: wd, c => by
      show LemK.tensVd E p.1 p.2 (Fw E wd f) c ∈ genSub E V
      rw [tensVd_apply]
      refine Submodule.sub_mem _ (genSub_stable E V _ _ (Fw_mem E V hf wd c)) ?_
      split_ifs
      · exact Fw_mem E V hf wd p.1
      · exact Submodule.zero_mem _

theorem tMapD_smooth {σ : Mat k r → (H →L[ℂ] H)} {x₀ : Mat k r} {w : H} {a : ℝ}
    (x₁ : Fin (2 * r + k + 1) → ℂ) {f : Fin (2 * r + k + 1) → H} (hf : ∀ c, Qp ε σ x₀ w a (f c)) :
    Formalism.REAL.SmoothOnG ε (tMapD σ x₁ x₀ w f) := by
  have := Formalism.REAL.smooth_on_group_sum (ε := ε) Finset.univ
    (fun c g => cJd x₁ (Pi.single c 1) g * coefX σ x₀ w (f c) g)
    (fun c _ => Formalism.REAL.smooth_on_group_mul (cJd_smooth x₁ _) (hf c).1)
  exact this

theorem tMapD_bound {σ : Mat k r → (H →L[ℂ] H)} {x₀ : Mat k r} {w : H} {a : ℝ}
    (x₁ : Fin (2 * r + k + 1) → ℂ) {f : Fin (2 * r + k + 1) → H} (hf : ∀ c, Qp ε σ x₀ w a (f c)) :
    ∃ C : ℝ, ∀ g, Formalism.REAL.inUJ ε g → ‖tMapD σ x₁ x₀ w f g‖ ≤ C * frob g ^ (1 - a) := by
  choose C hC using fun c => (hf c).2
  refine ⟨(∑ j, ‖x₁ j‖) * ∑ c, C c, fun g hg => ?_⟩
  have hG := frob_pos n_pos hg
  have e : frob g ^ (1 - a) = frob g * frob g ^ (-a) := by
    rw [sub_eq_add_neg, Real.rpow_add hG, Real.rpow_one]
  rw [e]
  unfold tMapD
  refine (norm_sum_le Finset.univ (fun c => cJd x₁ (Pi.single c 1) g * coefX σ x₀ w (f c) g)).trans ?_
  calc ∑ c, ‖cJd x₁ (Pi.single c 1) g * coefX σ x₀ w (f c) g‖ ≤
        ∑ c, ((∑ j, ‖x₁ j‖) * frob g) * (C c * frob g ^ (-a)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul]
        exact mul_le_mul (cJd_bound x₁ c hg) (hC c g hg) (norm_nonneg _)
          (mul_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _) hG.le)
    _ = (∑ j, ‖x₁ j‖) * (∑ c, C c) * (frob g * frob g ^ (-a)) := by
        have h3 : ∀ c, ((∑ j, ‖x₁ j‖) * frob g) * (C c * frob g ^ (-a)) =
            ((∑ j, ‖x₁ j‖) * (frob g * frob g ^ (-a))) * C c := fun c => by ring
        rw [Finset.sum_congr rfl (fun c _ => h3 c), ← Finset.mul_sum]
        ring

end TDAux
end ReciprocityTheory.ChartRestriction.DS.Lap
