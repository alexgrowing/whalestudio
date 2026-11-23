import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic

noncomputable section

namespace GlobalTheory.DiffDecay

section Weak

variable {E : Type} [AddCommGroup E] [Module ℂ E]

def WithSemi (_p : Seminorm ℂ E) : Type := E

instance (p : Seminorm ℂ E) : AddCommGroup (WithSemi p) := inferInstanceAs (AddCommGroup E)
instance (p : Seminorm ℂ E) : Module ℂ (WithSemi p) := inferInstanceAs (Module ℂ E)
instance (p : Seminorm ℂ E) : SeminormedAddCommGroup (WithSemi p) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := WithSemi p) p.toAddGroupSeminorm
instance (p : Seminorm ℂ E) : NormedSpace ℂ (WithSemi p) where
  norm_smul_le a x := (map_smul_eq_mul p a x).le

theorem bounded_of_weak [TopologicalSpace E] [IsTopologicalAddGroup E] {T : Type} (f : T → E)
    (h : ∀ l : E →L[ℂ] ℂ, ∃ C : ℝ, ∀ t, ‖l (f t)‖ ≤ C) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ C : ℝ, ∀ t, p (f t) ≤ C := by
  let j₀ : E →ₗ[ℂ] WithSemi p := LinearMap.id
  have hj : Continuous j₀ := by
    refine continuous_of_continuousAt_zero j₀ ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have := hp.tendsto 0
    rw [map_zero] at this
    exact this
  let j : E →L[ℂ] WithSemi p := ⟨j₀, hj⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun t => NormedSpace.inclusionInDoubleDual ℂ (WithSemi p) (j (f t)))
    (fun φ => h (φ.comp j))
  refine ⟨C, fun t => ?_⟩
  have := hC t
  rw [show NormedSpace.inclusionInDoubleDual ℂ (WithSemi p) (j (f t)) =
    NormedSpace.inclusionInDoubleDualLi ℂ (j (f t)) from rfl, LinearIsometry.norm_map] at this
  exact this

end Weak

section Tame

variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {W : Type} [SeminormedAddCommGroup W]

def Tame (R : W → E →ₗ[ℂ] E) : Prop :=
  ∀ p : Seminorm ℂ E, Continuous p → ∃ (q : Seminorm ℂ E) (M : ℕ), Continuous q ∧
    ∀ w f, p (R w f - f) ≤ ‖w‖ * (1 + ‖w‖) ^ M * q f

theorem continuous_smul_semi (c : ℝ) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ q' : Seminorm ℂ E, Continuous q' ∧ ∀ f, q' f = |c| * q f :=
  ⟨(‖c‖₊ : NNReal) • q, (continuous_const.mul hq : Continuous fun f => |c| * q f), fun _ => rfl⟩

theorem Tame.growth {R : W → E →ₗ[ℂ] E} (h : Tame R) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ (q : Seminorm ℂ E) (M : ℕ), Continuous q ∧ ∀ w f, p (R w f) ≤ (1 + ‖w‖) ^ M * q f := by
  obtain ⟨q, M, hq, hb⟩ := h p hp
  refine ⟨p + q, M + 1, (hp.add hq : Continuous fun f => p f + q f), fun w f => ?_⟩
  have h1 : p (R w f) ≤ p (R w f - f) + p f := by
    simpa using map_add_le_add p (R w f - f) f
  have h2 := hb w f
  have h3 : 1 ≤ (1 + ‖w‖) ^ M := one_le_pow₀ (by linarith [norm_nonneg w])
  have hp0 := apply_nonneg p f
  have hq0 := apply_nonneg q f
  have hw := norm_nonneg w
  rw [Seminorm.add_apply, pow_succ]
  nlinarith [mul_nonneg hw hp0, mul_nonneg (mul_nonneg hw hp0) (sub_nonneg.2 h3), mul_nonneg hp0 (sub_nonneg.2 h3),
    mul_nonneg hq0 (sub_nonneg.2 h3)]

theorem Tame.iter {R : W → E →ₗ[ℂ] E} (h : Tame R) (j : ℕ) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ u, ‖u‖ ≤ 1 → ∀ f, p (((R u - 1) ^ j) f) ≤ ‖u‖ ^ j * q f := by
  induction j with
  | zero => exact ⟨p, hp, fun u _ f => by simp⟩
  | succ j ih =>
    obtain ⟨q, hq, hb⟩ := ih
    obtain ⟨q₁, M, hq₁, hb₁⟩ := h q hq
    obtain ⟨q₂, hq₂, e₂⟩ := continuous_smul_semi (2 ^ M) q₁ hq₁
    refine ⟨q₂, hq₂, fun u hu f => ?_⟩
    rw [pow_succ, Module.End.mul_apply]
    refine (hb u hu _).trans ?_
    rw [pow_succ, mul_assoc, e₂, abs_of_nonneg (by positivity)]
    gcongr
    rw [LinearMap.sub_apply, Module.End.one_apply, ← mul_assoc]
    refine (hb₁ u f).trans ?_
    gcongr
    linarith

theorem Tame.decay {R : W → E →ₗ[ℂ] E} (h : Tame R) (p : Seminorm ℂ E) (hp : Continuous p) (A C : ℝ) (N : ℕ) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ (s : W) (r : ℝ), 0 ≤ r → ‖s‖ ≤ A * r →
      (0 < r → ∃ u, ‖u‖ * r ≤ C ∧ ∀ f, p (R s (R u f + f)) = 0) → ∀ f, p (R s f) ≤ q f * (1 + r) ^ (-(N : ℝ)) := by
  obtain ⟨q₁, M, hq₁, hb₁⟩ := h.growth p hp
  obtain ⟨q₂, hq₂, hb₂⟩ := h.iter (M + N) q₁ hq₁
  set r₀ := max C 1 with hr₀
  obtain ⟨q₃, hq₃, e₃⟩ := continuous_smul_semi ((1 + |A|) ^ M * (1 + r₀) ^ (M + N)) q₁ hq₁
  obtain ⟨q₄, hq₄, e₄⟩ := continuous_smul_semi ((1 + |A|) ^ M * (2 * r₀) ^ (M + N)) q₂ hq₂
  have hr1 : 1 ≤ r₀ := le_max_right _ _
  refine ⟨q₃ + q₄, (hq₃.add hq₄ : Continuous fun f => q₃ f + q₄ f), fun s r hr hs hu f => ?_⟩
  have hs' : 1 + ‖s‖ ≤ (1 + |A|) * (1 + r) := by
    nlinarith [le_abs_self A, abs_nonneg A, mul_le_mul_of_nonneg_right (le_abs_self A) hr]
  have hpow : (1 + ‖s‖) ^ M ≤ (1 + |A|) ^ M * (1 + r) ^ M := by
    rw [← mul_pow]; gcongr
  rw [Real.rpow_neg (by linarith), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity), Seminorm.add_apply]
  have h3 := apply_nonneg q₃ f
  have h4 := apply_nonneg q₄ f
  rcases le_or_gt r r₀ with hrr | hrr
  · refine le_trans ?_ (le_add_of_nonneg_right h4)
    rw [e₃, abs_of_nonneg (by positivity)]
    calc p (R s f) * (1 + r) ^ N ≤ ((1 + |A|) ^ M * (1 + r) ^ M * q₁ f) * (1 + r) ^ N := by
          gcongr; exact (hb₁ s f).trans (by gcongr)
      _ = (1 + |A|) ^ M * (1 + r) ^ (M + N) * q₁ f := by ring
      _ ≤ _ := by gcongr
  · refine le_trans ?_ (le_add_of_nonneg_left h3)
    obtain ⟨u, huC, hu0⟩ := hu (by linarith)
    have hC : C ≤ r₀ := le_max_left _ _
    have hu1 : ‖u‖ ≤ 1 := by
      by_contra hcon
      nlinarith [not_le.1 hcon]
    have hstep : ∀ g, p (R s g) ≤ p (R s ((R u - 1) g)) := fun g => by
      have e1 : (2 : ℂ) • R s g = R s (R u g + g) - R s ((R u - 1) g) := by
        rw [← map_sub, ← map_smul, LinearMap.sub_apply, Module.End.one_apply, two_smul]; congr 1; abel
      have e2 := map_sub_le_add p (R s (R u g + g)) (R s ((R u - 1) g))
      rw [← e1, map_smul_eq_mul, hu0] at e2
      have := apply_nonneg p (R s g)
      simp only [Complex.norm_ofNat] at e2
      linarith
    have hit : ∀ j : ℕ, p (R s f) ≤ p (R s (((R u - 1) ^ j) f)) := fun j => by
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact ih.trans (hstep _)
    have hur : ‖u‖ * (1 + r) ≤ 2 * r₀ := by nlinarith
    rw [e₄, abs_of_nonneg (by positivity)]
    calc p (R s f) * (1 + r) ^ N ≤ ((1 + |A|) ^ M * (1 + r) ^ M * (‖u‖ ^ (M + N) * q₂ f)) * (1 + r) ^ N := by
          gcongr
          refine (hit (M + N)).trans ((hb₁ s _).trans ?_)
          gcongr
          exact hb₂ u hu1 f
      _ = (1 + |A|) ^ M * (‖u‖ * (1 + r)) ^ (M + N) * q₂ f := by rw [mul_pow ‖u‖]; ring
      _ ≤ _ := by gcongr

end Tame

section Heis

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : Type} [SeminormedAddCommGroup W]

def heisOp (L : V →L[ℝ] ℝ) (k : ℝ) (a : V) : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k))).comp (SchwartzMap.compSubConstCLM ℂ (-a))

theorem tame_heisOp
    (hT : ∀ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p →
      ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (a : V) (f : SchwartzMap V ℂ),
        p (SchwartzMap.compSubConstCLM ℂ (-a) f - f) ≤ ‖a‖ * (1 + ‖a‖) ^ M * q f)
    (hP : ∀ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p →
      ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (L : V →L[ℝ] ℝ) (k : ℝ) (f : SchwartzMap V ℂ),
        p (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ M * q f)
    (L : W → V →L[ℝ] ℝ) (k : W → ℝ) (a : W → V) (c : ℝ) (hc : 1 ≤ c) (hL : ∀ w, ‖L w‖ ≤ c * ‖w‖)
    (hk : ∀ w, |k w| ≤ c * ‖w‖ ^ 2) (ha : ∀ w, ‖a w‖ ≤ ‖w‖) :
    Tame fun w => (heisOp (L w) (k w) (a w)).toLinearMap := by
  intro p hp
  obtain ⟨q₁, M₁, hq₁, hb₁⟩ := hP p hp
  obtain ⟨q₂, M₂, hq₂, hb₂⟩ := hT p hp
  have hTt : Tame fun a : V => (SchwartzMap.compSubConstCLM ℂ (-a) : SchwartzMap V ℂ →L[ℂ] _).toLinearMap := hT
  obtain ⟨q₃, M₃, hq₃, hb₃⟩ := hTt.growth q₁ hq₁
  obtain ⟨q₄, hq₄, e₄⟩ := continuous_smul_semi (c ^ (M₁ + 1)) q₃ hq₃
  refine ⟨q₂ + q₄, M₁ + M₂ + M₃ + 1, (hq₂.add hq₄ : Continuous fun f => q₂ f + q₄ f), fun w f => ?_⟩
  set g := SchwartzMap.compSubConstCLM ℂ (-(a w)) f with hg
  have h1 := map_add_le_add p (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L w y + k w)) g - g) (g - f)
  rw [sub_add_sub_cancel] at h1
  refine le_trans h1 ?_
  have hw := norm_nonneg w
  have h1w : 1 ≤ 1 + ‖w‖ := by linarith
  have hc0 : 0 < c := by linarith
  rw [Seminorm.add_apply, mul_add, add_comm]
  refine add_le_add ((hb₂ _ f).trans ?_) ((hb₁ _ _ g).trans ?_)
  · have := ha w
    calc _ ≤ ‖w‖ * (1 + ‖w‖) ^ M₂ * q₂ f := by gcongr
      _ ≤ _ := by gcongr; omega
  · have h2 : q₁ g ≤ (1 + ‖w‖) ^ M₃ * q₃ f := (hb₃ (a w) f).trans (by have := ha w; gcongr)
    have h3 : ‖L w‖ + |k w| ≤ c * (‖w‖ * (1 + ‖w‖)) := by nlinarith [hL w, hk w]
    have h4 : 1 + ‖L w‖ ≤ c * (1 + ‖w‖) := by nlinarith [hL w]
    rw [e₄, abs_of_nonneg (pow_nonneg hc0.le _)]
    have h5 := apply_nonneg q₃ f
    have h6 := apply_nonneg q₁ g
    calc _ ≤ c * (‖w‖ * (1 + ‖w‖)) * (c * (1 + ‖w‖)) ^ M₁ * ((1 + ‖w‖) ^ M₃ * q₃ f) := by gcongr
      _ = ‖w‖ * (1 + ‖w‖) ^ (M₁ + M₃ + 1) * (c ^ (M₁ + 1) * q₃ f) := by rw [mul_pow c]; ring
      _ ≤ _ := by gcongr; omega

end Heis

end GlobalTheory.DiffDecay

end
