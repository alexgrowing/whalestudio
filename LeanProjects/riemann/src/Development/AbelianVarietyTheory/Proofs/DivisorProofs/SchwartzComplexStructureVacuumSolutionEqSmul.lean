import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

namespace GlobalTheory.VacCore

theorem ray_formula {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (k : V → ℂ) (hk : Differentiable ℝ k) (w : V) (ℓ : V →ₗ[ℝ] ℂ)
    (h : ∀ z, fderiv ℝ k z w = ℓ z * k z) : k w = k 0 * Complex.exp (ℓ w / 2) := by
  set c := ℓ w
  let E : ℝ → ℂ := fun s => Complex.exp (((-(s ^ 2) / 2 : ℝ) : ℂ) * c)
  have hE : ∀ s : ℝ, HasDerivAt E (Complex.exp (((-(s ^ 2) / 2 : ℝ) : ℂ) * c) * (((-(2 * s) / 2 : ℝ) : ℂ) * c)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (-(s ^ 2) / 2 : ℝ)) (-(2 * s) / 2) s := by
      have := ((hasDerivAt_pow 2 s).neg).div_const 2
      simpa using this
    exact ((h1.ofReal_comp).mul_const c).cexp
  have hK : ∀ s : ℝ, HasDerivAt (fun s : ℝ => k (s • w)) (fderiv ℝ k (s • w) w) s := by
    intro s
    have := (hk (s • w)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const w)
    rw [one_smul] at this
    exact this
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => k (s • w) * E s) 0 s := by
    intro s
    have := (hK s).mul (hE s)
    refine this.congr_deriv ?_
    rw [h, map_smul]
    simp only [Complex.real_smul, E]
    push_cast
    ring
  have hc := is_const_of_deriv_eq_zero (f := fun s : ℝ => k (s • w) * E s)
    (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) 1 0
  simp only [E, one_smul, zero_smul] at hc
  have : Complex.exp (((-((1:ℝ) ^ 2) / 2 : ℝ) : ℂ) * c) * Complex.exp (c / 2) = 1 := by
    rw [← Complex.exp_add]; push_cast; ring_nf; simp
  calc k w = k w * (Complex.exp (((-((1:ℝ) ^ 2) / 2 : ℝ) : ℂ) * c) * Complex.exp (c / 2)) := by rw [this, mul_one]
    _ = _ := by rw [← mul_assoc, hc]; simp

theorem conj_mul_eq_zero_of_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f g : SchwartzMap V ℂ) (y₀ : V) (hy : y₀ ≠ 0)
    (h : ∀ z, fderiv ℝ f z y₀ * (starRingEnd ℂ) (g z) + f z * (starRingEnd ℂ) (fderiv ℝ g z y₀) = 0) :
    ∀ z, f z * (starRingEnd ℂ) (g z) = 0 := by
  intro z
  let φ : ℝ → ℂ := fun t => f (z + t • y₀) * (starRingEnd ℂ) (g (z + t • y₀))
  have hL : ∀ t : ℝ, HasDerivAt (fun t : ℝ => z + t • y₀) y₀ t := by
    intro t
    have := ((hasDerivAt_id t).smul_const y₀).const_add z
    simpa using this
  have hφ : ∀ t, HasDerivAt φ 0 t := by
    intro t
    have hf := (f.differentiableAt (x := z + t • y₀)).hasFDerivAt.comp_hasDerivAt t (hL t)
    have hg := (g.differentiableAt (x := z + t • y₀)).hasFDerivAt.comp_hasDerivAt t (hL t)
    have hg' := hg.star
    have := hf.mul hg'
    refine this.congr_deriv ?_
    have := h (z + t • y₀)
    simpa [Complex.star_def] using this
  have hc : ∀ t, φ t = φ 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) t 0
  have hlin : Filter.Tendsto (fun t : ℝ => z + t • y₀) (Filter.cocompact ℝ) (Filter.cocompact V) := by
    apply Filter.tendsto_cocompact_cocompact_of_norm
    intro ε
    have hy' : 0 < ‖y₀‖ := norm_pos_iff.mpr hy
    refine ⟨(ε + ‖z‖) / ‖y₀‖, fun t ht => ?_⟩
    have h1 : ‖t • y₀‖ ≤ ‖z + t • y₀‖ + ‖z‖ := by
      calc ‖t • y₀‖ = ‖(z + t • y₀) - z‖ := by simp
        _ ≤ _ := norm_sub_le _ _
    rw [norm_smul] at h1
    rw [div_lt_iff₀ hy'] at ht
    linarith
  have hf0 : Filter.Tendsto (fun t : ℝ => f (z + t • y₀)) (Filter.cocompact ℝ) (nhds 0) :=
    (f.tendsto_cocompact).comp hlin
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖g x‖ ≤ C := ⟨_, fun x => (g.toBoundedContinuousFunction).norm_coe_le_norm x⟩
  have hφ0 : Filter.Tendsto φ (Filter.cocompact ℝ) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hf0 ⊢
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    have := hf0.mul_const C
    rw [zero_mul] at this
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) this
    simp only [φ, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hconst : Filter.Tendsto φ (Filter.cocompact ℝ) (nhds (φ 0)) := by
    have : φ = fun _ => φ 0 := funext hc
    rw [this]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hconst hφ0
  simpa [φ] using this

noncomputable def lin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (a b : V) : V →ₗ[ℝ] ℂ where
  toFun z := 2 * Real.pi * Complex.I * (B z a : ℂ) + 2 * Real.pi * (B z b : ℂ)
  map_add' x y := by simp only [map_add, LinearMap.add_apply, Complex.ofReal_add]; ring
  map_smul' c x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul]
    ring

theorem lin_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (a b z : V) :
    lin B a b z = 2 * Real.pi * Complex.I * (B z a : ℂ) + 2 * Real.pi * (B z b : ℂ) := rfl

theorem schwartz_vacuum_eq_smul : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ y, (∀ x, B x y = 0) → y = 0) →
    ∀ (J e : (V × V) →ₗ[ℝ] (V × V)) (e' : V →ₗ[ℝ] V), (∀ y, J (J y) = -y) → (∀ y, e (e y) = e y) →
    (∀ y, J (e y) = e (J y)) → (∀ y, (e y).1 = e' y.1) → (∀ y x, B x (e y).2 = B (e' x) y.2) →
    ∀ (f g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ y x, fderiv ℝ g x (J y).1 - 2 * Real.pi * Complex.I * (B x (J y).2 : ℝ) * g x =
      Complex.I * (fderiv ℝ g x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * g x)) →
    (∀ y x, fderiv ℝ f x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I * (B x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f x =
      Complex.I * (fderiv ℝ f x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * f x)) →
    ∃ z : ℂ, f = z • g := by
  intro V _ _ _ B hB J e e' hJ he hJe he1 he2 f g hg0 hg hf

  have hinj : ∀ y, (J y).1 = 0 → y.1 = 0 → y = 0 := by
    intro y hJy hy1
    have key : ∀ x, g x ≠ 0 → B x y.2 = 0 := by
      intro x hx
      have h := hg y x
      simp only [hJy, hy1, map_zero] at h
      have h2 : g x * (2 * Real.pi * (B x y.2 : ℂ) + 2 * Real.pi * Complex.I * (B x (J y).2 : ℂ)) = 0 := by
        linear_combination (-1 : ℂ) * h + (2 * Real.pi * (B x y.2 : ℂ) * g x) * Complex.I_sq
      have h3 := (mul_eq_zero.mp h2).resolve_left hx
      have h4 := congrArg Complex.re h3
      simpa [Real.pi_ne_zero] using h4
    have hy2 : y.2 = 0 := by
      apply hB
      by_contra hne
      push_neg at hne
      obtain ⟨x₀, hx₀⟩ := hne
      apply hg0
      ext x
      simp only [SchwartzMap.zero_apply]
      set t₀ : ℝ := -(B x y.2) / B x₀ y.2
      have hS : IsClosed {t : ℝ | g (x + t • x₀) = 0} :=
        isClosed_eq (g.continuous.comp (continuous_const.add (continuous_id.smul continuous_const)))
          continuous_const
      have hsub : ({t₀}ᶜ : Set ℝ) ⊆ {t : ℝ | g (x + t • x₀) = 0} := by
        intro t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
        simp only [Set.mem_setOf_eq]
        by_contra hgt
        have := key _ hgt
        rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at this
        apply ht
        simp only [t₀]
        field_simp
        linarith
      have hcl := hS.closure_subset_iff.mpr hsub
      rw [(dense_compl_singleton t₀).closure_eq] at hcl
      have := hcl (Set.mem_univ 0)
      simpa using this
    exact Prod.ext hy1 hy2
  let T : (V × V) →ₗ[ℝ] (V × V) := (LinearMap.fst ℝ V V ∘ₗ J).prod (LinearMap.fst ℝ V V)
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hinj y (congrArg Prod.fst hy) (congrArg Prod.snd hy)
  have hTs : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTi

  choose yx hyx using fun x : V => hTs (x, 0)
  have hyx1 : ∀ x, (J (yx x)).1 = x := fun x => by simpa [T] using congrArg Prod.fst (hyx x)
  have hyx2 : ∀ x, (yx x).1 = 0 := fun x => by simpa [T] using congrArg Prod.snd (hyx x)
  have hray : ∀ k : SchwartzMap V ℂ, (∀ (y : V × V) (z : V), fderiv ℝ k z (J y).1 -
      2 * Real.pi * Complex.I * (B z (J y).2 : ℝ) * k z =
      Complex.I * (fderiv ℝ k z y.1 - 2 * Real.pi * Complex.I * (B z y.2 : ℝ) * k z)) →
      ∀ x, k x = k 0 * Complex.exp (lin B (J (yx x)).2 (yx x).2 x / 2) := by
    intro k hk x
    apply ray_formula k k.differentiable x (lin B (J (yx x)).2 (yx x).2)
    intro z
    have h := hk (yx x) z
    rw [hyx1, hyx2, map_zero] at h
    rw [lin_apply]
    linear_combination h - (2 * Real.pi * (B z (yx x).2 : ℂ) * k z) * Complex.I_sq
  have hg_ray := hray g hg
  have hg00 : g 0 ≠ 0 := by
    intro h0; apply hg0; ext x; rw [hg_ray x, h0]; simp
  have hgne : ∀ x, g x ≠ 0 := fun x => by
    rw [hg_ray x]; exact mul_ne_zero hg00 (Complex.exp_ne_zero _)
  have he'2 : ∀ v, e' (e' v) = e' v := by
    intro v
    have := congrArg Prod.fst (he (v, 0))
    simp only [he1] at this
    simpa using this
  by_cases hz : ∀ v, e' v = 0
  · have he0 : ∀ y, e y = 0 := by
      intro y; apply Prod.ext
      · rw [he1, hz]; rfl
      · apply hB; intro x; rw [he2, hz, map_zero, LinearMap.zero_apply]
    have hf' : ∀ (y : V × V) (z : V), fderiv ℝ f z (J y).1 -
        2 * Real.pi * Complex.I * (B z (J y).2 : ℝ) * f z =
        Complex.I * (fderiv ℝ f z y.1 - 2 * Real.pi * Complex.I * (B z y.2 : ℝ) * f z) := by
      intro y z; have := hf y z; rwa [he0, smul_zero, sub_zero] at this
    have hf_ray := hray f hf'
    refine ⟨f 0 / g 0, ?_⟩
    ext x
    rw [SchwartzMap.smul_apply, smul_eq_mul, hf_ray x, hg_ray x]
    field_simp
  · push_neg at hz
    obtain ⟨v, hv⟩ := hz
    set y₀ := e' v with hy₀def
    have hy₀ : e' y₀ = y₀ := he'2 v
    obtain ⟨u, hu⟩ := hTs (y₀, 0)
    have hu1 : (J u).1 = y₀ := by simpa [T] using congrArg Prod.fst hu
    have hu2 : u.1 = 0 := by simpa [T] using congrArg Prod.snd hu
    have heu : e u = u := by
      have : e u - u = 0 := hinj _
        (by rw [map_sub, Prod.fst_sub, hJe, he1, hu1, hy₀, sub_self])
        (by rw [Prod.fst_sub, he1, hu2, map_zero, sub_self])
      exact sub_eq_zero.mp this
    have hfu : ∀ z, fderiv ℝ f z y₀ = (2 * Real.pi * Complex.I * (B z (J u).2 : ℂ)
        - 2 * Real.pi * (B z u.2 : ℂ)) * f z := by
      intro z
      have h := hf u z
      rw [heu, two_smul, sub_add_cancel_left, map_neg, Prod.fst_neg, Prod.snd_neg, map_neg,
        map_neg, hu1, hu2, map_zero, Complex.ofReal_neg] at h
      linear_combination (-1 : ℂ) * h + (2 * Real.pi * (B z u.2 : ℂ) * f z) * Complex.I_sq
    have hgu : ∀ z, fderiv ℝ g z y₀ = (2 * Real.pi * Complex.I * (B z (J u).2 : ℂ)
        + 2 * Real.pi * (B z u.2 : ℂ)) * g z := by
      intro z
      have h := hg u z
      rw [hu1, hu2, map_zero] at h
      linear_combination h - (2 * Real.pi * (B z u.2 : ℂ) * g z) * Complex.I_sq
    have hk := conj_mul_eq_zero_of_line f g y₀ hv (fun z => by
      rw [hfu z, hgu z]
      simp only [map_add, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      ring)
    refine ⟨0, ?_⟩
    ext z
    rw [zero_smul, SchwartzMap.zero_apply]
    exact (mul_eq_zero.mp (hk z)).resolve_right ((map_ne_zero _).mpr (hgne z))

end GlobalTheory.VacCore
