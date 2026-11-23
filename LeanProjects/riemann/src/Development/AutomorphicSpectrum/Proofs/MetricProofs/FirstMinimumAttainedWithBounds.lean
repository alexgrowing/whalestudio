import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateFormStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.ShortVec

section Abstract

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {L : Type} [AddCommGroup L]
  (p : L →+ V) (f : L →ₗ[ℤ] L →ₗ[ℤ] ℤ)

theorem abs_form_le (him : ∀ x y, ((f x y : ℤ) : ℝ) = (inner ℂ (p y) (p x)).im) (x y : L) :
    |((f x y : ℤ) : ℝ)| ≤ ‖p x‖ * ‖p y‖ := by
  rw [him, mul_comm]
  exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)

include p in

theorem finite_short [Module.Free ℤ L] [Module.Finite ℤ L]
    (him : ∀ x y, ((f x y : ℤ) : ℝ) = (inner ℂ (p y) (p x)).im) (hu : Function.Surjective f) (T : ℝ) :
    {x : L | ‖p x‖ < T}.Finite := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  have hc : ∀ i, ∃ c, f c = b.coord i := fun i => hu _
  choose c hc using hc
  let C : Module.Free.ChooseBasisIndex ℤ L → ℤ := fun i => ⌈‖p (c i)‖ * |T|⌉
  have hfin : (Set.Icc (fun i => -C i) C : Set (Module.Free.ChooseBasisIndex ℤ L → ℤ)).Finite :=
    Set.finite_Icc _ _
  refine (Set.Finite.preimage (f := fun x i => b.repr x i) ?_ hfin).subset ?_
  · intro x _ y _ h
    exact b.repr.injective (Finsupp.ext (congrFun h))
  · intro x hx
    have hx' : ‖p x‖ < T := hx
    have key : ∀ i, |((b.repr x i : ℤ) : ℝ)| ≤ C i := by
      intro i
      have h1 := abs_form_le p f him (c i) x
      rw [hc i] at h1
      have h2 : ‖p (c i)‖ * ‖p x‖ ≤ ‖p (c i)‖ * |T| :=
        mul_le_mul_of_nonneg_left (hx'.le.trans (le_abs_self T)) (norm_nonneg _)
      have h3 : ‖p (c i)‖ * |T| ≤ C i := Int.le_ceil _
      have h4 : b.coord i x = b.repr x i := rfl
      rw [h4] at h1
      exact h1.trans (h2.trans h3)
    constructor
    · intro i
      have := (abs_le.mp (key i)).1
      have h5 : ((-C i : ℤ) : ℝ) ≤ ((b.repr x i : ℤ) : ℝ) := by push_cast; exact this
      exact_mod_cast h5
    · intro i
      have := (abs_le.mp (key i)).2
      exact_mod_cast this

theorem period_injective (him : ∀ x y, ((f x y : ℤ) : ℝ) = (inner ℂ (p y) (p x)).im)
    (hi : Function.Injective f) : Function.Injective p := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply hi
  rw [map_zero]
  ext y
  have := him x y
  rw [hx, inner_zero_right, Complex.zero_im] at this
  simpa using this

theorem exists_shortest {v₀ : L} (hv₀ : v₀ ≠ 0) (hfin : ∀ T : ℝ, {x : L | ‖p x‖ < T}.Finite) :
    ∃ x₀, x₀ ≠ 0 ∧ ∀ v, v ≠ 0 → ‖p x₀‖ ≤ ‖p v‖ := by
  have hA : ({x : L | ‖p x‖ < ‖p v₀‖ + 1} ∩ {x | x ≠ 0}).Finite := (hfin _).inter_of_left _
  have hv : v₀ ∈ {x : L | ‖p x‖ < ‖p v₀‖ + 1} ∩ {x | x ≠ 0} := ⟨by simp, hv₀⟩
  obtain ⟨x₀, hx₀, hmin⟩ := Set.exists_min_image _ (fun x => ‖p x‖) hA ⟨v₀, hv⟩
  refine ⟨x₀, hx₀.2, fun v hv' => ?_⟩
  by_cases h : ‖p v‖ < ‖p v₀‖ + 1
  · exact hmin v ⟨h, hv'⟩
  · have := hmin v₀ hv
    linarith [not_lt.mp h]

theorem norm_sq_sum_orth {ι : Type} [Fintype ι] (u : ι → V)
    (h : Pairwise fun i j => inner ℂ (u i) (u j) = (0 : ℂ)) : ‖∑ i, u i‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
  classical
  have h1 : (inner ℂ (∑ i, u i) (∑ i, u i) : ℂ) = ∑ i, inner ℂ (u i) (u i) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    exact Finset.sum_eq_single i (fun j _ hj => h hj.symm) (by simp)
  have h2 : ∀ w : V, ‖w‖ ^ 2 = (inner ℂ w w : ℂ).re := fun w => norm_sq_eq_re_inner (𝕜 := ℂ) w
  rw [h2, h1, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => (h2 _).symm

end Abstract

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def Tan (_R : RiemLat E g Λ) : Type := Fin g → ℂ

instance (R : RiemLat E g Λ) : AddCommGroup (Tan R) := inferInstanceAs (AddCommGroup (Fin g → ℂ))

instance (R : RiemLat E g Λ) : Module ℂ (Tan R) := inferInstanceAs (Module ℂ (Fin g → ℂ))

theorem conj_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip y x) = R.ip x y := by
  simp only [RiemLat.ip]
  rw [starRingEnd_apply, ← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, R.herm.eq,
    ← Matrix.dotProduct_mulVec]

theorem ip_add_left (R : RiemLat E g Λ) (x y z : Fin g → ℂ) : R.ip (x + y) z = R.ip x z + R.ip y z := by
  simp only [RiemLat.ip, star_add, Matrix.mulVec_add, dotProduct_add]

theorem ip_smul_left (R : RiemLat E g Λ) (x y : Fin g → ℂ) (r : ℂ) :
    R.ip (r • x) y = starRingEnd ℂ r * R.ip x y := by
  simp only [RiemLat.ip, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, starRingEnd_apply]

theorem ip_self_nonneg (R : RiemLat E g Λ) (x : Fin g → ℂ) : 0 ≤ (R.ip x x).re := by
  by_cases h : x = 0
  · subst h
    simp [RiemLat.ip]
  · exact (R.pos x h).le

theorem ip_self_definite (R : RiemLat E g Λ) (x : Fin g → ℂ) (h : R.ip x x = 0) : x = 0 := by
  by_contra hx
  have := R.pos x hx
  have h' : (x ⬝ᵥ R.Hm *ᵥ star x) = 0 := h
  rw [h'] at this
  simp at this

@[reducible] def core (R : RiemLat E g Λ) : InnerProductSpace.Core ℂ (Tan R) where
  inner x y := R.ip x y
  conj_inner_symm x y := conj_ip R x y
  re_inner_nonneg x := ip_self_nonneg R x
  add_left x y z := ip_add_left R x y z
  smul_left x y r := ip_smul_left R x y r
  definite x h := ip_self_definite R x h

instance (R : RiemLat E g Λ) : NormedAddCommGroup (Tan R) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Tan R) _ _ _ (core R)

instance (R : RiemLat E g Λ) : InnerProductSpace ℂ (Tan R) := InnerProductSpace.ofCore (core R).toCore

instance (R : RiemLat E g Λ) : InnerProductSpace ℝ (Tan R) := InnerProductSpace.complexToReal

def per (R : RiemLat E g Λ) : Λ →+ Tan R := R.P

theorem sqrt_normSq (R : RiemLat E g Λ) (x : Λ) : Real.sqrt (R.normSq x) = ‖per R x‖ :=
  (norm_eq_sqrt_re_inner (𝕜 := ℂ) (per R x)).symm

theorem him (R : RiemLat E g Λ) (x y : Λ) :
    ((R.form x y : ℤ) : ℝ) = (inner ℂ (per R y) (per R x) : ℂ).im := (R.im x y).symm

theorem finite_ball (R : RiemLat E g Λ) (T : ℝ) : {x : Λ | ‖per R x‖ < T}.Finite := by
  haveI := R.free
  haveI := R.fin
  exact finite_short (per R) R.form (him R) R.unimod.2 T

theorem per_injective (R : RiemLat E g Λ) : Function.Injective (per R) :=
  period_injective (per R) R.form (him R) R.unimod.1

theorem shortest_vector_attains_first_minimum (R : RiemLat E g Λ) {v₀ : Λ} (hv₀ : v₀ ≠ 0) :
    0 < R.lam1 ∧ ∃ x, x ≠ 0 ∧ ‖per R x‖ = R.lam1 := by
  obtain ⟨x₀, hx₀, hmin⟩ := exists_shortest (per R) hv₀ (finite_ball R)
  have hl : IsLeast {x | ∃ v : Λ, v ≠ 0 ∧ x = Real.sqrt (R.normSq v)} ‖per R x₀‖ := by
    refine ⟨⟨x₀, hx₀, (sqrt_normSq R x₀).symm⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [sqrt_normSq]
    exact hmin v hv
  have he : R.lam1 = ‖per R x₀‖ := hl.csInf_eq
  rw [he]
  refine ⟨norm_pos_iff.mpr fun h => hx₀ (per_injective R ?_), x₀, hx₀, rfl⟩
  rw [h, map_zero]

theorem firstMinimum_le_period_norm (R : RiemLat E g Λ) {v : Λ} (hv : v ≠ 0) : R.lam1 ≤ ‖per R v‖ := by
  rw [← sqrt_normSq]
  refine csInf_le ⟨0, ?_⟩ ⟨v, hv, rfl⟩
  rintro _ ⟨w, _, rfl⟩
  exact Real.sqrt_nonneg _

end Tangent

section Embeddings

variable {E : Type} [Field E] [NumberField E]

theorem exists_mul_eq_int {a : 𝓞 E} (ha : a ≠ 0) : ∃ (c : 𝓞 E) (N : ℤ), N ≠ 0 ∧ c * a = (N : 𝓞 E) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {a}))
  refine ⟨c, (Ideal.absNorm (Ideal.span {a}) : ℕ), ?_, by simpa using hc⟩
  have : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha
  exact_mod_cast this

theorem ringHom_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  obtain ⟨c, N, hN, hc⟩ := exists_mul_eq_int h
  have h2 := congrArg s hc
  rw [map_mul, ha, mul_zero, map_intCast] at h2
  exact hN (by exact_mod_cast h2.symm)

theorem comp_bijective : Function.Bijective (fun s : E →+* ℂ => s.comp (algebraMap (𝓞 E) E)) := by
  constructor
  · intro s s' h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  · intro s
    refine ⟨IsFractionRing.lift (K := E) (ringHom_injective s), ?_⟩
    show (IsFractionRing.lift (K := E) (ringHom_injective s)).comp (algebraMap (𝓞 E) E) = s
    refine RingHom.ext fun a => ?_
    exact IsFractionRing.lift_algebraMap (K := E) (ringHom_injective s) a

variable [IsCMField E]

theorem conj_comp_injective : Function.Injective (fun s : 𝓞 E →+* ℂ => (starRingEnd ℂ).comp s) := by
  intro s s' h
  ext a
  have := congrArg (fun t : 𝓞 E →+* ℂ => starRingEnd ℂ (t a)) h
  simpa using this

theorem finrank_eq_two_mul {Ψ : Type} [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) :
    Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  have hΦ : Function.Bijective (Sum.elim σ (fun τ => (starRingEnd ℂ).comp (σ τ)) : Ψ ⊕ Ψ → (𝓞 E →+* ℂ)) := by
    constructor
    · rintro (τ | τ) (τ' | τ') e
      · simp only [Sum.elim_inl] at e
        rw [h.1 e]
      · simp only [Sum.elim_inl, Sum.elim_inr] at e
        exact absurd ⟨τ, e⟩ ((h.2 (σ τ')).1 ⟨τ', rfl⟩)
      · simp only [Sum.elim_inl, Sum.elim_inr] at e
        exact absurd ⟨τ', e.symm⟩ ((h.2 (σ τ)).1 ⟨τ, rfl⟩)
      · simp only [Sum.elim_inr] at e
        rw [h.1 (conj_comp_injective e)]
    · intro s
      by_cases hs : ∃ τ, σ τ = s
      · obtain ⟨τ, rfl⟩ := hs
        exact ⟨Sum.inl τ, rfl⟩
      · have hB : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
          by_contra hB
          exact hs ((h.2 s).2 hB)
        obtain ⟨τ, hτ⟩ := hB
        refine ⟨Sum.inr τ, ?_⟩
        simp only [Sum.elim_inr, hτ]
        ext a
        simp
  have e := (Equiv.ofBijective _ (comp_bijective (E := E))).trans (Equiv.ofBijective _ hΦ).symm
  rw [← NumberField.Embeddings.card E ℂ, Fintype.card_congr e, Fintype.card_sum, two_mul]

end Embeddings

section Short

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem norm_act_le (R : RiemLat E g Λ) {a : 𝓞 E} {vr : ℝ} (hvr : 0 < vr)
    (ha : ∀ s : E →+* ℂ, ‖s (a : E)‖ ≤ vr) (x : Λ) : ‖per R (a • x)‖ ≤ vr * ‖per R x‖ := by
  obtain ⟨-, -, h3, h4, h5⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  let u : (E →+* ℂ) → Tan R := fun s => eigComp R.B (s.comp (algebraMap (𝓞 E) E)) (R.P x)
  let w : (E →+* ℂ) → Tan R := fun s => eigComp R.B (s.comp (algebraMap (𝓞 E) E)) (R.B a (R.P x))
  have hu : ∑ s, u s = per R x := h4 (R.P x)
  have hw : ∑ s, w s = per R (a • x) := by
    have : per R (a • x) = R.B a (R.P x) := R.act a x
    rw [this]
    exact h4 _
  have hwu : ∀ s, w s = (s (a : E)) • u s := fun s => (h3 _).2.2.2 a (R.P x)
  have hne : ∀ s s' : E →+* ℂ, s ≠ s' →
      s.comp (algebraMap (𝓞 E) E) ≠ s'.comp (algebraMap (𝓞 E) E) :=
    fun s s' h e => h ((comp_bijective (E := E)).1 e)
  have hou : Pairwise fun s s' => inner ℂ (u s) (u s') = (0 : ℂ) := fun s s' h =>
    h5 _ _ (hne s s' h) _ ((h3 _).1 _) _ ((h3 _).1 _)
  have how : Pairwise fun s s' => inner ℂ (w s) (w s') = (0 : ℂ) := fun s s' h =>
    h5 _ _ (hne s s' h) _ ((h3 _).1 _) _ ((h3 _).1 _)
  have e1 := norm_sq_sum_orth u hou
  have e2 := norm_sq_sum_orth w how
  rw [hu] at e1
  rw [hw] at e2
  have key : ‖per R (a • x)‖ ^ 2 ≤ (vr * ‖per R x‖) ^ 2 := by
    rw [e2, mul_pow, e1, Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [hwu s, norm_smul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha s) 2) (by positivity)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp key

theorem form_act_eq_zero (R : RiemLat E g Λ) {a : 𝓞 E} {vr : ℝ} (hvr : 0 < vr)
    (ha : ∀ s : E →+* ℂ, ‖s (a : E)‖ ≤ vr) {x y : Λ} (hx : ‖per R x‖ < vr ^ (-(1 / 2 : ℝ)))
    (hy : ‖per R y‖ < vr ^ (-(1 / 2 : ℝ))) : R.form (a • x) y = 0 := by
  set r := vr ^ (-(1 / 2 : ℝ)) with hr
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hvr _
  have hrr : vr * (r * r) = 1 := by
    rw [hr, GroundTheory.Heights₂.Heights.LowerBound.ShortVectorsOrthogonal.rpow_neg_half_mul_self hvr,
      mul_inv_cancel₀ hvr.ne']
  have h1 := abs_form_le (per R) R.form (him R) (a • x) y
  have h2 := norm_act_le R hvr ha x
  have h3 : ‖per R (a • x)‖ * ‖per R y‖ < 1 := by
    have hx0 := norm_nonneg (per R x)
    have hy0 := norm_nonneg (per R y)
    calc ‖per R (a • x)‖ * ‖per R y‖ ≤ (vr * ‖per R x‖) * ‖per R y‖ :=
          mul_le_mul_of_nonneg_right h2 hy0
      _ = vr * (‖per R x‖ * ‖per R y‖) := by ring
      _ < vr * (r * r) := by
          refine mul_lt_mul_of_pos_left ?_ hvr
          calc ‖per R x‖ * ‖per R y‖ ≤ ‖per R x‖ * r := mul_le_mul_of_nonneg_left hy.le hx0
            _ < r * r := mul_lt_mul_of_pos_right hx hr_pos
      _ = 1 := hrr
  have h4 : |((R.form (a • x) y : ℤ) : ℝ)| < 1 := h1.trans_lt h3
  have h5 : |R.form (a • x) y| < 1 := by exact_mod_cast h4
  exact Int.abs_lt_one_iff.mp h5

theorem form_all_eq_zero (R : RiemLat E g Λ) {vr : ℝ} (hvr : 0 < vr)
    (a : Fin (Module.finrank ℚ E) → 𝓞 E) (hli : LinearIndependent ℚ (fun i => (a i : E)))
    (hb : ∀ i (s : E →+* ℂ), ‖s (a i)‖ ≤ vr) {x y : Λ} (hx : ‖per R x‖ < vr ^ (-(1 / 2 : ℝ)))
    (hy : ‖per R y‖ < vr ^ (-(1 / 2 : ℝ))) (c : 𝓞 E) : R.form (c • x) y = 0 := by
  have hspan : Submodule.span ℚ (Set.range fun i => (a i : E)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  have key : ∀ e ∈ Submodule.span ℚ (Set.range fun i => (a i : E)),
      ∃ (N : ℤ) (b : 𝓞 E), N ≠ 0 ∧ algebraMap (𝓞 E) E b = (N : E) * e ∧ R.form (b • x) y = 0 := by
    intro e he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨i, rfl⟩ := he
      exact ⟨1, a i, one_ne_zero, by simp, form_act_eq_zero R hvr (hb i) hx hy⟩
    | zero => exact ⟨1, 0, one_ne_zero, by simp, by simp⟩
    | add e₁ e₂ _ _ h₁ h₂ =>
      obtain ⟨N₁, b₁, hN₁, hb₁, hf₁⟩ := h₁
      obtain ⟨N₂, b₂, hN₂, hb₂, hf₂⟩ := h₂
      refine ⟨N₁ * N₂, (N₂ : 𝓞 E) * b₁ + (N₁ : 𝓞 E) * b₂, mul_ne_zero hN₁ hN₂, ?_, ?_⟩
      · rw [map_add, map_mul, map_mul, map_intCast, map_intCast, hb₁, hb₂]
        push_cast
        ring
      · rw [add_smul, mul_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        simp [hf₁, hf₂]
    | smul q e _ h =>
      obtain ⟨N, b, hN, hb', hf⟩ := h
      refine ⟨N * q.den, (q.num : 𝓞 E) * b, mul_ne_zero hN (by exact_mod_cast q.den_ne_zero), ?_, ?_⟩
      · have hq : (q : E) * (q.den : E) = (q.num : E) := by exact_mod_cast Rat.mul_den_eq_num q
        rw [map_mul, map_intCast, hb', Rat.smul_def, ← hq]
        push_cast
        ring
      · rw [mul_smul, Int.cast_smul_eq_zsmul]
        simp [hf]
  obtain ⟨N, b, hN, hb', hf⟩ := key (c : E) (hspan ▸ Submodule.mem_top)
  have hbc : b = (N : 𝓞 E) * c := IsFractionRing.injective (𝓞 E) E (by
    rw [map_mul, map_intCast]
    exact hb')
  rw [hbc, mul_smul, Int.cast_smul_eq_zsmul] at hf
  simpa [hN] using hf

theorem isIso_span (R : RiemLat E g Λ) {T : Set Λ} (h : ∀ x ∈ T, ∀ y ∈ T, ∀ a : 𝓞 E, R.form (a • x) y = 0) :
    GroundTheory.Heights₂.Heights.LowerBoundFree.IsIsoSub R.form (Submodule.span (𝓞 E) T) := by
  have h1 : ∀ x ∈ T, ∀ w ∈ Submodule.span (𝓞 E) T, ∀ a : 𝓞 E, R.form (a • x) w = 0 := by
    intro x hx w hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp
    | add w₁ w₂ _ _ h₁ h₂ => intro a; simp [h₁ a, h₂ a]
    | smul c w _ hc =>
      intro a
      have e : (c : E) = IsCMField.complexConj E ((IsCMField.ringOfIntegersComplexConj E c : 𝓞 E) : E) := by
        simp [IsCMField.coe_ringOfIntegersComplexConj]
      rw [← R.adj _ c e, ← mul_smul]
      exact hc _
  have h2 : ∀ v ∈ Submodule.span (𝓞 E) T, ∀ w ∈ Submodule.span (𝓞 E) T, ∀ a : 𝓞 E, R.form (a • v) w = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact h1 x hx
    | zero => simp
    | add v₁ v₂ _ _ h₁ h₂ => intro w hw a; simp [h₁ w hw a, h₂ w hw a]
    | smul c v _ hc =>
      intro w hw a
      rw [← mul_smul]
      exact hc w hw _
  intro v hv w hw
  simpa using h2 v hv w hw 1

theorem exists_subspace (R : RiemLat E g Λ) {Ψ : Type} [Fintype Ψ] [Nonempty Ψ] {σ : Ψ → (𝓞 E →+* ℂ)} {j j' : ℕ}
    (hσ : IsCMFam σ) (hs : R.HasSig σ j j') {T : Set Λ} (hT : T.Finite)
    (hI : ∀ x ∈ T, ∀ y ∈ T, ∀ a : 𝓞 E, R.form (a • x) y = 0) :
    ∃ W : Submodule ℝ (Tan R), Module.finrank ℝ W ≤ 2 * Fintype.card Ψ * j' ∧ FiniteDimensional ℝ W ∧
      ∀ x ∈ T, per R x ∈ W := by
  classical
  obtain ⟨τ₀⟩ := ‹Nonempty Ψ›
  obtain ⟨s, hs1, hs2⟩ := exists_maximal_linearIndepOn (𝓞 E) (Subtype.val : T → Λ)
  haveI : Finite T := hT.to_subtype
  let r := Nat.card s
  let e : Fin r ≃ s := (Finite.equivFin s).symm
  let v : Fin r → Λ := fun i => ((e i : T) : Λ)
  have hv_ind : LinearIndependent (𝓞 E) v := hs1.comp e e.injective
  have hv_mem : ∀ i, v i ∈ Submodule.span (𝓞 E) T := fun i => Submodule.subset_span (e i : T).2
  have hC := (GlobalTheory.T.isotropic_eigencomponent_conjugate_form E g Λ Ψ R (Submodule.span (𝓞 E) T) (isIso_span R hI) (σ τ₀)).2 r v hv_mem hv_ind
  have hmem := ((GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Ψ R).2.2.1 (σ τ₀)).1
  have hr : r ≤ j' := by
    let w : Fin r → eigSp R.B (σ τ₀) := fun a => ⟨_, hmem (R.P (v a))⟩
    have hw : LinearIndependent ℂ w := LinearIndependent.of_comp (eigSp R.B (σ τ₀)).subtype hC
    have := hw.fintype_card_le_finrank
    rw [(hs τ₀).1] at this
    simpa using this
  let b := Module.Free.chooseBasis ℤ (𝓞 E)
  let fam : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin r → Tan R := fun q => per R (b q.1 • v q.2)
  let W : Submodule ℝ (Tan R) := Submodule.span ℝ (Set.range fam)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = 2 * Fintype.card Ψ := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, finrank_eq_two_mul hσ]
  have hzs : ∀ (n : ℤ) (w : Tan R), w ∈ W → n • w ∈ W := fun n w hw => W.toAddSubgroup.zsmul_mem hw n
  have hbase : ∀ (a : 𝓞 E) (i : Fin r), per R (a • v i) ∈ W := by
    intro a i
    have ha : a = ∑ k, (b.repr a k) • b k := (b.sum_repr a).symm
    rw [ha, Finset.sum_smul, map_sum]
    refine W.sum_mem fun k _ => ?_
    rw [smul_assoc, map_zsmul]
    exact hzs _ _ (Submodule.subset_span ⟨(k, i), rfl⟩)
  have hspan : ∀ y ∈ Submodule.span (𝓞 E) (Set.range v), ∀ a : 𝓞 E, per R (a • y) ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact fun a => hbase a i
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ =>
      intro a
      rw [smul_add, map_add]
      exact W.add_mem (h₁ a) (h₂ a)
    | smul c y _ h =>
      intro a
      rw [← mul_smul]
      exact h _
  have hmult : ∀ x : T, ∃ a : 𝓞 E, a ≠ 0 ∧ a • (x : Λ) ∈ Submodule.span (𝓞 E) (Set.range v) := by
    intro x
    by_cases hx : x ∈ s
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [one_smul]
      refine Submodule.subset_span ⟨e.symm ⟨x, hx⟩, ?_⟩
      simp [v]
    · obtain ⟨a, ha, hax⟩ := hs2 x hx
      refine ⟨a, ha, Submodule.span_mono ?_ hax⟩
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨e.symm ⟨z, hz⟩, by simp [v]⟩
  refine ⟨W, ?_, FiniteDimensional.span_of_finite ℝ (Set.finite_range fam), ?_⟩
  · have h1 : Module.finrank ℝ W ≤ Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin r) :=
      finrank_range_le_card fam
    rw [Fintype.card_prod, hcard, Fintype.card_fin] at h1
    exact h1.trans (Nat.mul_le_mul_left _ hr)
  · intro x hx
    obtain ⟨a, ha, hax⟩ := hmult ⟨x, hx⟩
    obtain ⟨c, N, hN, hc⟩ := exists_mul_eq_int ha
    have h1 := hspan _ hax c
    rw [← mul_smul, hc, Int.cast_smul_eq_zsmul, map_zsmul] at h1
    have h2 : ((N : ℝ)⁻¹) • (N • per R x) ∈ W := W.smul_mem _ h1
    rwa [← Int.cast_smul_eq_zsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN), one_smul] at h2

end Short

theorem short_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (vr : ℝ), IsCMFam σ → R.HasSig σ j j' → 1 ≤ j' → 0 < vr → (∃ a : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧ ∀ i (s : E →+* ℂ), ‖s (a i)‖ ≤ vr) → 0 < R.lam1 ∧ (∃ x, x ≠ 0 ∧ Real.sqrt (R.normSq x) = R.lam1) ∧ (∀ x y, Real.sqrt (R.normSq x) < vr ^ (-(1 / 2 : ℝ)) → Real.sqrt (R.normSq y) < vr ^ (-(1 / 2 : ℝ)) → ∀ a : 𝓞 E, R.form (a • x) y = 0) ∧ ∀ t : ℝ, R.lam1 < t → t ≤ vr ^ (-(1 / 2 : ℝ)) → {x : Λ | x ≠ 0 ∧ Real.sqrt (R.normSq x) < t}.Finite ∧ (({x : Λ | x ≠ 0 ∧ Real.sqrt (R.normSq x) < t}.ncard : ℝ)) ≤ (3 * t / R.lam1) ^ (2 * Fintype.card Ψ * j') := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ R σ vr hσ hs hj hvr ⟨a, hli, hb⟩
  have hΨ : Nonempty Ψ := by
    have h1 := finrank_eq_two_mul hσ
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact Fintype.card_pos_iff.mp (by omega)
  obtain ⟨τ₀⟩ := id hΨ
  have hg : g ≠ 0 := by
    rintro rfl
    have h1 := (hs τ₀).1
    rw [Module.finrank_zero_of_subsingleton] at h1
    omega
  have hv₀ : ∃ v₀ : Λ, v₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    haveI : Subsingleton Λ := ⟨fun x y => by rw [hcon x, hcon y]⟩
    have h1 := R.rank
    rw [Module.finrank_zero_of_subsingleton] at h1
    omega
  obtain ⟨v₀, hv₀⟩ := hv₀
  obtain ⟨hpos, x₀, hx₀, hx₀'⟩ := shortest_vector_attains_first_minimum R hv₀
  have horth : ∀ x y, Real.sqrt (R.normSq x) < vr ^ (-(1 / 2 : ℝ)) → Real.sqrt (R.normSq y) < vr ^ (-(1 / 2 : ℝ)) →
      ∀ a : 𝓞 E, R.form (a • x) y = 0 := by
    intro x y hx hy c
    rw [sqrt_normSq] at hx hy
    exact form_all_eq_zero R hvr a hli hb hx hy c
  refine ⟨hpos, ⟨x₀, hx₀, by rw [sqrt_normSq, hx₀']⟩, horth, ?_⟩
  intro t ht ht'
  have hfin : {x : Λ | x ≠ 0 ∧ Real.sqrt (R.normSq x) < t}.Finite := by
    refine (finite_ball R t).subset ?_
    rintro x ⟨_, hx⟩
    rw [sqrt_normSq] at hx
    exact hx
  refine ⟨hfin, ?_⟩
  obtain ⟨W, hW, hWf, hmem⟩ := exists_subspace R hσ hs hfin
    (fun x hx y hy c => horth x y (hx.2.trans_le ht') (hy.2.trans_le ht') c)
  have hshort : per R x₀ ∈ W := hmem x₀ ⟨hx₀, by rw [sqrt_normSq, hx₀']; exact ht⟩
  have hne : per R x₀ ≠ 0 := fun h => hx₀ (per_injective R (by rw [h, map_zero]))
  have hone : 1 ≤ Module.finrank ℝ W := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h
    rw [h] at hshort
    exact hne ((Submodule.mem_bot ℝ).mp hshort)
  have hp := (GroundTheory.Heights₂.Heights.LowerBound.PackingCount.full (Tan R) (Set.range (per R)) W R.lam1 t
    (Module.finrank ℝ W) {
      zero_mem := ⟨0, map_zero _⟩
      sub_mem := by
        rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        exact ⟨x - y, map_sub _ _ _⟩
      lam_pos := hpos
      lam_le_norm := by
        rintro _ ⟨x, rfl⟩ hx
        exact firstMinimum_le_period_norm R fun h => hx (by rw [h, map_zero])
      finrank_eq := rfl
      one_le_a := hone
      short_mem := by
        rintro _ ⟨x, rfl⟩ hx
        by_cases h0 : x = 0
        · rw [h0, map_zero]
          exact W.zero_mem
        · exact hmem x ⟨h0, by rw [sqrt_normSq]; exact hx⟩
      lam_le_r := ht.le }).2
  have himg : {v | v ∈ Set.range (per R) ∧ v ≠ 0 ∧ ‖v‖ < t} =
      per R '' {x : Λ | x ≠ 0 ∧ Real.sqrt (R.normSq x) < t} := by
    ext v
    constructor
    · rintro ⟨⟨x, rfl⟩, h0, h1⟩
      exact ⟨x, ⟨fun h => h0 (by rw [h, map_zero]), by rw [sqrt_normSq]; exact h1⟩, rfl⟩
    · rintro ⟨x, ⟨h0, h1⟩, rfl⟩
      rw [sqrt_normSq] at h1
      exact ⟨⟨x, rfl⟩, fun h => h0 (per_injective R (by rw [h, map_zero])), h1⟩
  rw [himg, Set.ncard_image_of_injective _ (per_injective R)] at hp
  refine hp.trans (pow_le_pow_right₀ ?_ hW)
  rw [one_le_div hpos]
  linarith

end GlobalTheory.CompanionTheory.Ar.Cusp.ShortVec
