import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.DjCurveA

open Matrix

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.DjC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

section Curve

variable {N j : ℕ}

theorem smul_real_eq (Y : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) : (t : ℂ) • Y = t • Y := by
  ext a b
  simp

theorem exp_add_real (Y : Matrix (Fin N) (Fin N) ℂ) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) = NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y) := by
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)

theorem det_sub_exp (e : Fin j ↪ Fin N) (S : Set (Fin N)) (Y : Matrix (Fin N) (Fin N) ℂ) (hY : Pres S Y)
    (hm : ∀ E F : Matrix (Fin N) (Fin N) ℂ, Pres S E → Pres S F → sub e (E * F) = sub e E * sub e F) (t : ℝ) :
    (sub e (NormedSpace.exp ((t : ℂ) • Y))).det = Complex.exp (t * (sub e Y).trace) := by
  have hsub1 : sub e (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    ext a b
    simp [sub, Matrix.one_apply, e.injective.eq_iff]
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℂ, f = fun s : ℝ => (sub e (NormedSpace.exp ((s : ℂ) • Y))).det := ⟨_, rfl⟩
  have hpres : ∀ s : ℝ, Pres S (NormedSpace.exp ((s : ℂ) • Y)) := fun s => pres_exp (pres_smul hY _)
  have hmul : ∀ s u : ℝ, f (s + u) = f s * f u := by
    intro s u
    rw [hf]
    simp only
    rw [exp_add_real, hm _ _ (hpres s) (hpres u), Matrix.det_mul]
  have hf0 : f 0 = 1 := by
    rw [hf]
    simp [hsub1]
  have hd0 : HasDerivAt f (sub e Y).trace 0 := by
    rw [hf]
    apply hasDerivAt_det_of_one (fun s : ℝ => sub e (NormedSpace.exp ((s : ℂ) • Y))) (sub e Y)
    · simp [hsub1]
    · intro a b
      have hfun : (fun s : ℝ => sub e (NormedSpace.exp ((s : ℂ) • Y)) a b) =
          fun s : ℝ => (NormedSpace.exp (s • Y)) (e a) (e b) := by
        funext s
        rw [smul_real_eq]
        rfl
      rw [hfun]
      exact hasDerivAt_exp_entry Y (e a) (e b)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (sub e Y).trace := ⟨_, rfl⟩
  rw [← hc] at hd0
  have hd : ∀ s, HasDerivAt f (c * f s) s := by
    intro s
    have h1 : f = fun u => f s * f (u - s) := by
      funext u
      rw [← hmul, add_sub_cancel]
    have h2 : HasDerivAt (fun u => f (u - s)) c s := by
      have h3 := hd0
      rw [← sub_self s] at h3
      exact h3.comp_sub_const s s
    have h4 := h2.const_mul (f s)
    have h5 : HasDerivAt f (f s * c) s :=
      h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => congrFun h1 u)
    rw [mul_comm]
    exact h5
  have hl : ∀ u : ℝ, HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := fun u => Complex.ofRealCLM.hasDerivAt
  have hg : ∀ u : ℝ, HasDerivAt (fun u : ℝ => f u * Complex.exp (-(c * u))) 0 u := by
    intro u
    have he : HasDerivAt (fun u : ℝ => Complex.exp (-(c * u))) (Complex.exp (-(c * u)) * (-c)) u := by
      have h := ((hl u).const_mul c).neg.cexp
      simpa using h
    have := (hd u).mul he
    exact this.congr_deriv (by ring)
  have hconst : ∀ u : ℝ, f u * Complex.exp (-(c * u)) = 1 := by
    intro u
    have := is_const_of_deriv_eq_zero (fun x => (hg x).differentiableAt) (fun x => (hg x).deriv) u 0
    rw [this, hf0]
    simp
  have key : f t = Complex.exp (c * t) := by
    have h1 := hconst t
    calc f t = f t * Complex.exp (-(c * t)) * Complex.exp (c * t) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = Complex.exp (c * t) := by rw [h1, one_mul]
  have hft : f t = (sub e (NormedSpace.exp ((t : ℂ) • Y))).det := by rw [hf]
  rw [← hft, key, hc, mul_comm]

theorem trace_sub_le (e : Fin j ↪ Fin N) (Y : Matrix (Fin N) (Fin N) ℂ) : ‖(sub e Y).trace‖ ≤ (j : ℝ) * mx Y := by
  unfold mx
  simp only [Matrix.trace, Matrix.diag]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a, ‖sub e Y a a‖ ≤ ∑ _a : Fin j, ‖Matrix.of.symm Y‖ := Finset.sum_le_sum fun a _ => by
        show ‖Y (e a) (e a)‖ ≤ _
        exact (norm_le_pi_norm (Matrix.of.symm Y (e a)) (e a)).trans (norm_le_pi_norm (Matrix.of.symm Y) (e a))
    _ = (j : ℝ) * ‖Matrix.of.symm Y‖ := by simp

end Curve

section Concrete

variable (k j ρ : ℕ)

def eR : Fin j ↪ Fin (2 * (j + ρ) + k + 1) :=
  ⟨fun a => ⟨a.val, by omega⟩, fun a b h => Fin.ext (Fin.mk.inj_iff.1 h)⟩

def eL : Fin j ↪ Fin (2 * (j + ρ) + k + 1) :=
  ⟨fun a => ⟨2 * (j + ρ) + k - a.val, by omega⟩, fun a b h => Fin.ext (by have h' := Fin.mk.inj_iff.1 h; omega)⟩

theorem eL_val (a : Fin j) : (eL k j ρ a).val = 2 * (j + ρ) + k - a.val := rfl

theorem mem_range_eR (c : Fin (2 * (j + ρ) + k + 1)) : c ∈ Set.range (eR k j ρ) ↔ c.val < j := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨c.val, h⟩, Fin.ext rfl⟩

theorem mem_range_eL (c : Fin (2 * (j + ρ) + k + 1)) :
    c ∈ Set.range (eL k j ρ) ↔ 2 * (j + ρ) + k + 1 ≤ c.val + j := by
  have hc := c.isLt
  constructor
  · rintro ⟨a, rfl⟩
    rw [eL_val]
    have := a.isLt
    omega
  · intro h
    refine ⟨⟨2 * (j + ρ) + k - c.val, by omega⟩, Fin.ext ?_⟩
    rw [eL_val]
    simp only
    omega

theorem hpk_row {k r : ℕ} (i m : Fin (2 * r + k + 1)) (hi : i.val < r) :
    Hpk k r i m = if i.val + m.val = 2 * r + k then 1 else 0 := by
  unfold Hpk
  by_cases h : i.val + m.val = 2 * r + k
  · simp [hi, h]
  · rw [if_neg (fun h' => h h'.2), if_neg (fun h' => h h'.2), if_neg (fun h' => absurd h'.1 (by omega)),
      if_neg h]

variable {k j ρ}

theorem presR {Y : B.Mat k (j + ρ)} (hY : inLieP k j ρ Y) : Pres (Set.range (eR k j ρ)) Y := by
  intro c b hb hc
  rw [mem_range_eR] at hb hc
  exact hY.2 c b hb (not_lt.1 hc)

theorem presL {Y : B.Mat k (j + ρ)} (hY : inLieP k j ρ Y) : Pres (Set.range (eL k j ρ))ᶜ Y := by
  intro c b hb hc
  simp only [Set.mem_compl_iff, not_not, mem_range_eL] at hb hc
  have hcl := c.isLt
  have hi' : 2 * (j + ρ) + k - c.val < 2 * (j + ρ) + k + 1 := by omega
  obtain ⟨i, hidef⟩ : ∃ i : Fin (2 * (j + ρ) + k + 1), i = ⟨2 * (j + ρ) + k - c.val, hi'⟩ := ⟨_, rfl⟩
  have hiv : i.val = 2 * (j + ρ) + k - c.val := by rw [hidef]
  have hi : i.val < j := by omega
  have hL := congrArg (fun M : Matrix (Fin (2 * (j + ρ) + k + 1)) (Fin (2 * (j + ρ) + k + 1)) ℂ => M i b) hY.1
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply] at hL
  have h1 : ∑ m, Yᴴ i m * Hpk k (j + ρ) m b = 0 := by
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : m.val < j
    · rw [hpk_row m b (by omega), if_neg (by omega), mul_zero]
    · rw [Matrix.conjTranspose_apply, hY.2 m i hi (by omega), star_zero, zero_mul]
  have h2 : ∑ m, Hpk k (j + ρ) i m * Y m b = Y c b := by
    rw [Finset.sum_eq_single c]
    · rw [hpk_row i c (by omega), if_pos (by omega), one_mul]
    · intro m _ hm
      rw [hpk_row i m (by omega), if_neg, zero_mul]
      intro h
      apply hm
      ext
      omega
    · simp
  rw [h1, h2, zero_add] at hL
  exact hL

theorem zh_right (g E : B.Mat k (j + ρ)) (hE : Pres (Set.range (eR k j ρ)) E) :
    Zh k j ρ (g * E) = Zh k j ρ g * sub (eR k j ρ) E := by
  ext a b
  have hr : 2 * (j + ρ) + k - a.val < 2 * (j + ρ) + k + 1 := by omega
  let r0 : Fin (2 * (j + ρ) + k + 1) := ⟨2 * (j + ρ) + k - a.val, hr⟩
  have key : (g * E) r0 (eR k j ρ b) = ∑ a', g r0 (eR k j ρ a') * E (eR k j ρ a') (eR k j ρ b) := by
    rw [Matrix.mul_apply, show (∑ a', g r0 (eR k j ρ a') * E (eR k j ρ a') (eR k j ρ b)) =
      ∑ m ∈ Finset.univ.map (eR k j ρ), g r0 m * E m (eR k j ρ b) from
      (Finset.sum_map Finset.univ (eR k j ρ) (fun m => g r0 m * E m (eR k j ρ b))).symm]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_
    have hm' : m ∉ Set.range (eR k j ρ) := by
      rintro ⟨x, rfl⟩
      exact hm (Finset.mem_map_of_mem _ (Finset.mem_univ x))
    rw [hE m (eR k j ρ b) ⟨b, rfl⟩ hm', mul_zero]
  exact key

theorem zh_left (g E : B.Mat k (j + ρ)) (hE : Pres (Set.range (eL k j ρ))ᶜ E) :
    Zh k j ρ (E * g) = sub (eL k j ρ) E * Zh k j ρ g := by
  ext a b
  have hb : b.val < 2 * (j + ρ) + k + 1 := by omega
  let c0 : Fin (2 * (j + ρ) + k + 1) := ⟨b.val, hb⟩
  have key : (E * g) (eL k j ρ a) c0 = ∑ a', E (eL k j ρ a) (eL k j ρ a') * g (eL k j ρ a') c0 := by
    rw [Matrix.mul_apply, show (∑ a', E (eL k j ρ a) (eL k j ρ a') * g (eL k j ρ a') c0) =
      ∑ m ∈ Finset.univ.map (eL k j ρ), E (eL k j ρ a) m * g m c0 from
      (Finset.sum_map Finset.univ (eL k j ρ) (fun m => E (eL k j ρ a) m * g m c0)).symm]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_
    have hm' : m ∈ (Set.range (eL k j ρ))ᶜ := by
      rintro ⟨x, rfl⟩
      exact hm (Finset.mem_map_of_mem _ (Finset.mem_univ x))
    rw [hE (eL k j ρ a) m hm' (fun h => h ⟨a, rfl⟩), zero_mul]
  exact key

theorem djCurve_general (Y : B.Mat k (j + ρ)) (hY : inLieP k j ρ Y) : ∃ c₁ c₂ : ℂ,
    ‖c₁‖ ≤ (j : ℝ) * mx Y ∧ ‖c₂‖ ≤ (j : ℝ) * mx Y ∧
    ∀ (g : B.Mat k (j + ρ)) (t : ℝ),
      DjU k j ρ (g * NormedSpace.exp ((t : ℂ) • Y)) = Complex.exp ((t : ℂ) * c₁) * DjU k j ρ g ∧
      DjU k j ρ (NormedSpace.exp (-((t : ℂ) • Y)) * g) = Complex.exp ((t : ℂ) * c₂) * DjU k j ρ g := by
  have hR := presR hY
  have hLp := presL hY
  have hmR : ∀ E F : B.Mat k (j + ρ), Pres (Set.range (eR k j ρ)) E → Pres (Set.range (eR k j ρ)) F →
      sub (eR k j ρ) (E * F) = sub (eR k j ρ) E * sub (eR k j ρ) F := by
    intro E F hE hF
    ext a b
    show ∑ m, E ((eR k j ρ) a) m * F m ((eR k j ρ) b) = ∑ a', E ((eR k j ρ) a) ((eR k j ρ) a') * F ((eR k j ρ) a') ((eR k j ρ) b)
    rw [← Finset.sum_map Finset.univ (eR k j ρ) (fun m => E ((eR k j ρ) a) m * F m ((eR k j ρ) b))]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_
    have hm' : m ∉ Set.range (eR k j ρ) := by
      rintro ⟨x, rfl⟩
      exact hm (Finset.mem_map_of_mem _ (Finset.mem_univ x))
    rw [hF m ((eR k j ρ) b) ⟨b, rfl⟩ hm', mul_zero]
  have hmL : ∀ E F : B.Mat k (j + ρ), Pres (Set.range (eL k j ρ))ᶜ E → Pres (Set.range (eL k j ρ))ᶜ F →
      sub (eL k j ρ) (E * F) = sub (eL k j ρ) E * sub (eL k j ρ) F := by
    intro E F hE hF
    ext a b
    show ∑ m, E ((eL k j ρ) a) m * F m ((eL k j ρ) b) = ∑ a', E ((eL k j ρ) a) ((eL k j ρ) a') * F ((eL k j ρ) a') ((eL k j ρ) b)
    rw [← Finset.sum_map Finset.univ (eL k j ρ) (fun m => E ((eL k j ρ) a) m * F m ((eL k j ρ) b))]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_
    have hm' : m ∈ (Set.range (eL k j ρ))ᶜ := by
      rintro ⟨x, rfl⟩
      exact hm (Finset.mem_map_of_mem _ (Finset.mem_univ x))
    rw [hE ((eL k j ρ) a) m hm' (fun h => h ⟨a, rfl⟩), zero_mul]
  refine ⟨(sub (eR k j ρ) Y).trace, -(sub (eL k j ρ) Y).trace, trace_sub_le _ Y,
    by rw [norm_neg]; exact trace_sub_le _ Y, fun g t => ⟨?_, ?_⟩⟩
  · unfold DjU
    rw [zh_right g _ (pres_exp (pres_smul hR _)), Matrix.det_mul, det_sub_exp (eR k j ρ) _ Y hR hmR t, mul_comm]
  · unfold DjU
    have hneg : -((t : ℂ) • Y) = (t : ℂ) • (-Y) := (smul_neg _ _).symm
    rw [hneg, zh_left g _ (pres_exp (pres_smul (pres_neg hLp) _)), Matrix.det_mul,
      det_sub_exp (eL k j ρ) _ (-Y) (pres_neg hLp) hmL t]
    have htr : (sub (eL k j ρ) (-Y)).trace = -(sub (eL k j ρ) Y).trace := by
      rw [← Matrix.trace_neg]
      congr 1
    rw [htr]

end Concrete

end PI.UnitaryCorollaryDerivatives.DjC
