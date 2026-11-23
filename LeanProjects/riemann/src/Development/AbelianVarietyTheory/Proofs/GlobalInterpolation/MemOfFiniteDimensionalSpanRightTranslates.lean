import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinitePointsDetect

open MeasureTheory

namespace GlobalTheory.UnitaryBC

theorem exists_finset_detecting_of_finiteDimensional {X : Type} (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] :
    ∃ s : Finset X, ∀ v : W, (∀ x ∈ s, (v : X → ℂ) x = 0) → v = 0 := by
  first
  | exact @_root_.GlobalTheory.FinitePointsDetect.finite_points_detect
  | exact _root_.GlobalTheory.FinitePointsDetect.finite_points_detect
  | (apply _root_.GlobalTheory.FinitePointsDetect.finite_points_detect <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinitePointsDetect.finite_points_detect <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinitePointsDetect.finite_points_detect <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinitePointsDetect.finite_points_detect ..)

theorem exists_interpolation_of_finiteDimensional {X : Type} (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] :
    ∃ (s : Finset X) (w : s → X → ℂ), ∀ v ∈ W, ∀ y, v y = ∑ x : s, v x * w x y := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_detecting_of_finiteDimensional W
  let r : W →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun x : s => (LinearMap.proj (x : X)) ∘ₗ W.subtype
  have hr : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hs v fun x hx => congrFun hv ⟨x, hx⟩
  obtain ⟨L, hL⟩ := r.exists_leftInverse_of_injective hr
  refine ⟨s, fun x => (L fun j => if x = j then 1 else 0 : W), fun v hv y => ?_⟩
  have h1 : L (r ⟨v, hv⟩) = ⟨v, hv⟩ := LinearMap.congr_fun hL ⟨v, hv⟩
  rw [LinearMap.pi_apply_eq_sum_univ] at h1
  have h2 := congrFun (congrArg Subtype.val h1) y
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul] at h2
  exact h2.symm

theorem eq_zero_of_integral_mul_eq_zero_of_separating {K : Type} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (R : Subalgebra ℂ (K → ℂ))
    (hc : ∀ p ∈ R, Continuous p) (hs : ∀ p ∈ R, star p ∈ R)
    (hsep : ∀ x y : K, x ≠ y → ∃ p ∈ R, p x ≠ p y) (g : K → ℂ) (hg : Continuous g)
    (h0 : ∀ p ∈ R, ∫ k, g k * p k ∂μ = 0) : g = 0 := by
  let A : StarSubalgebra ℂ C(K, ℂ) :=
    { carrier := {φ | (φ : K → ℂ) ∈ R}
      mul_mem' := fun ha hb => R.mul_mem ha hb
      add_mem' := fun ha hb => R.add_mem ha hb
      algebraMap_mem' := fun c => R.algebraMap_mem c
      star_mem' := fun ha => hs _ ha }
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨p, hp, hne⟩ := hsep x y hxy
    exact ⟨p, ⟨⟨p, hc p hp⟩, hp, rfl⟩, hne⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  let G : C(K, ℂ) := ⟨g, hg⟩
  have hcont : Continuous fun φ : C(K, ℂ) => ∫ k, g k * φ k ∂μ := by
    have h1 : Continuous fun φ : C(K, ℂ) =>
        ∫ k, (ContinuousMap.toLp (E := ℂ) 1 μ ℂ (G * φ)) k ∂μ :=
      MeasureTheory.continuous_integral.comp
        ((ContinuousMap.toLp (E := ℂ) 1 μ ℂ).continuous.comp (continuous_const.mul continuous_id))
    convert h1 using 2 with φ
    exact (integral_congr_ae (ContinuousMap.coeFn_toLp (E := ℂ) (p := 1) (𝕜 := ℂ) μ (G * φ))).symm
  have hcl : IsClosed {φ : C(K, ℂ) | ∫ k, g k * φ k ∂μ = 0} := isClosed_eq hcont continuous_const
  have hmem : star G ∈ closure (A : Set C(K, ℂ)) := by
    have : star G ∈ A.topologicalClosure := htop ▸ StarSubalgebra.mem_top
    exact this
  have hsub : (A : Set C(K, ℂ)) ⊆ {φ : C(K, ℂ) | ∫ k, g k * φ k ∂μ = 0} :=
    fun φ hφ => h0 _ hφ
  have hz : ∫ k, g k * (starRingEnd ℂ) (g k) ∂μ = 0 := closure_minimal hsub hcl hmem
  simp only [Complex.mul_conj] at hz
  rw [integral_complex_ofReal] at hz
  have hz' : ∫ k, Complex.normSq (g k) ∂μ = 0 := by exact_mod_cast hz
  have hcn : Continuous fun k => Complex.normSq (g k) := Complex.continuous_normSq.comp hg
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg (g k))
    (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 hz'
  have := (Continuous.ae_eq_iff_eq μ hcn continuous_zero).1 hae
  funext k
  exact Complex.normSq_eq_zero.1 (congrFun this k)

theorem mem_of_finiteDimensional_span_rightTranslates :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (R : Subalgebra ℂ (K → ℂ)), (∀ p ∈ R, Continuous p) → (∀ p ∈ R, star p ∈ R) → (∀ x y : K, x ≠ y → ∃ p ∈ R, p x ≠ p y) → (∀ p ∈ R, ∃ (m : ℕ) (a b : Fin m → K → ℂ), (∀ i, a i ∈ R ∧ Continuous (b i)) ∧ ∀ x k, p (x⁻¹ * k) = ∑ i, a i x * b i k) → ∀ f : K → ℂ, Continuous f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x : K => f (x * k))) → f ∈ R := by
  intro K _ _ _ _ _ R hc hs hsep hsplit f hf hfd
  classical
  borelize K
  let μ : Measure K := Measure.haar
  have hint : ∀ u : K → ℂ, Continuous u → Integrable u μ := fun u hu =>
    hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfx : ∀ x : K, Continuous fun k => f (x * k) := fun x =>
    hf.comp (continuous_const.mul continuous_id)
  obtain ⟨s, w, hw⟩ := exists_interpolation_of_finiteDimensional
    (Submodule.span ℂ (Set.range fun k : K => fun x : K => f (x * k)))
  have hdec : ∀ y k, f (y * k) = ∑ x : s, f (x * k) * w x y := fun y k =>
    hw _ (Submodule.subset_span ⟨k, rfl⟩) y

  have hconv : ∀ p ∈ R, (fun y => ∫ k, f (y * k) * p k ∂μ) ∈ R := by
    intro p hp
    obtain ⟨m, a, b, hab, hp'⟩ := hsplit p hp
    have : (fun y => ∫ k, f (y * k) * p k ∂μ) = ∑ i, (∫ k, f k * b i k ∂μ) • a i := by
      funext y
      have h1 := integral_mul_left_eq_self (μ := μ) (fun k => f k * p (y⁻¹ * k)) y
      simp only [inv_mul_cancel_left] at h1
      rw [h1]
      simp only [hp', Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_finset_sum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← integral_mul_const]
        congr 1
        funext k
        ring
      · intro i _
        exact hint _ (hf.mul (continuous_const.mul (hab i).2))
    rw [this]
    exact R.sum_mem fun i _ => R.smul_mem (hab i).1 _
  let T : R →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun p x => ∫ k, f (x * k) * (p : K → ℂ) k ∂μ
      map_add' := fun p q => by
        funext x
        simp only [Subalgebra.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint _ ((hfx x).mul (hc _ p.2))) (hint _ ((hfx x).mul (hc _ q.2)))
      map_smul' := fun c p => by
        funext x
        simp only [Subalgebra.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext k
        ring }
  have hmem : (fun x : s => f x) ∈ LinearMap.range T := by
    by_contra hne
    obtain ⟨l, hl1, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
    let c : s → ℂ := fun x => l fun j => if x = j then 1 else 0
    have hl : ∀ v : s → ℂ, l v = ∑ x, v x * c x := fun v => LinearMap.pi_apply_eq_sum_univ l v
    have hg : (fun k => ∑ x : s, f (x * k) * c x) = 0 := by
      refine eq_zero_of_integral_mul_eq_zero_of_separating μ R hc hs hsep _
        (continuous_finset_sum _ fun x _ => (hfx x).mul continuous_const) fun p hp => ?_
      have h1 : l (T ⟨p, hp⟩) = 0 := by
        have : l (T ⟨p, hp⟩) ∈ Submodule.map l (LinearMap.range T) :=
          Submodule.mem_map_of_mem ⟨_, rfl⟩
        rw [hl0] at this
        exact (Submodule.mem_bot ℂ).1 this
      rw [hl] at h1
      rw [← h1]
      simp only [Finset.sum_mul]
      rw [integral_finset_sum]
      · refine Finset.sum_congr rfl fun x _ => ?_
        change _ = (∫ k, f (x * k) * p k ∂μ) * c x
        rw [← integral_mul_const]
        congr 1
        funext k
        ring
      · intro x _
        exact hint _ (((hfx x).mul continuous_const).mul (hc p hp))
    apply hl1
    rw [hl]
    simpa using congrFun hg 1
  obtain ⟨p, hp⟩ := hmem
  have hfeq : f = fun y => ∫ k, f (y * k) * (p : K → ℂ) k ∂μ := by
    funext y
    have h1 := hdec y 1
    simp only [mul_one] at h1
    rw [h1]
    have h2 : ∀ k, f (y * k) * (p : K → ℂ) k = ∑ x : s, f (x * k) * (p : K → ℂ) k * w x y := by
      intro k
      rw [hdec y k, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    simp only [h2]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_mul_const]
      congr 1
      exact (congrFun hp x).symm
    · intro x _
      exact hint _ (((hfx x).mul (hc _ p.2)).mul continuous_const)
  rw [hfeq]
  exact hconv _ p.2

end GlobalTheory.UnitaryBC
