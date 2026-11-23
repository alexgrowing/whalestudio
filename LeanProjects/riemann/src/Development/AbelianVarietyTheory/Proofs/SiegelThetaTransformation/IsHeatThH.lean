import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.ExpSum

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} {U : Set V}

omit [FiniteDimensional ℂ V] in

theorem convexOn_norm_term (c : ℂ) (L : V →L[ℂ] ℂ) :
    ConvexOn ℝ Set.univ fun p => ‖c * cexp (L p)‖ := by
  have h : ConvexOn ℝ Set.univ fun p => Real.exp ((L p).re) := by
    have := convexOn_exp.comp_linearMap
      (Complex.reLm ∘ₗ (L.toLinearMap.restrictScalars ℝ))
    exact this
  simpa only [norm_mul, Complex.norm_exp, smul_eq_mul] using h.smul (norm_nonneg c)

theorem locally_normal (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) :
    ∀ x ∈ U, ∃ W ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ p ∈ W, ‖c i * cexp (L i p)‖ ≤ u i := by
  intro x hx
  have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  obtain ⟨b, hb, hbU⟩ := exists_mem_interior_convexHull_affineBasis (hU.mem_nhds hx)
  refine ⟨_, mem_interior_iff_mem_nhds.1 hb, fun i => ∑ j, ‖c i * cexp (L i (b j))‖,
    summable_sum fun j _ => hs _ (hbU (subset_convexHull ℝ _ ⟨j, rfl⟩)), fun i p hp => ?_⟩
  obtain ⟨y, ⟨j, rfl⟩, hy⟩ := (convexOn_norm_term (c i) (L i)).exists_ge_of_mem_convexHull
    (Set.subset_univ _) hp
  exact hy.trans (Finset.single_le_sum (f := fun j => ‖c i * cexp (L i (b j))‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ j))

theorem differentiableOn (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) :
    DifferentiableOn ℂ (fun p => ∑' i, c i * cexp (L i p)) U :=
  GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hU
    (fun i => Differentiable.differentiableOn (by fun_prop)) (locally_normal hU c L hs)

theorem hasSum_deriv (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) {p : V} (hp : p ∈ U) (v : V) :
    HasSum (fun i => c i * L i v * cexp (L i p))
      (deriv (fun s : ℂ => ∑' i, c i * cexp (L i (p + s • v))) 0) := by
  have h1 := GlobalTheory.SCV.hasSum_fderiv_of_locally_normal (F := fun i p => c i * cexp (L i p)) hU
    (fun i => Differentiable.differentiableOn (by fun_prop)) (locally_normal hU c L hs) hp
  have h2 := (ContinuousLinearMap.apply ℂ ℂ v).hasSum h1
  have h3 := ((differentiableOn hU c L hs).differentiableAt (hU.mem_nhds hp)).lineDeriv_eq_fderiv
    (v := v)
  rw [lineDeriv] at h3
  rw [h3]
  have e : (fun i => c i * L i v * cexp (L i p)) = fun i =>
      ContinuousLinearMap.apply ℂ ℂ v (fderiv ℂ (fun p => c i * cexp (L i p)) p) := by
    funext i
    have : HasFDerivAt (fun p => c i * cexp (L i p)) (c i • cexp (L i p) • L i) p :=
      ((L i).hasFDerivAt.cexp).const_mul (c i)
    rw [this.fderiv]
    simp
    ring
  rw [e]
  exact h2

theorem hasSum_deriv_deriv (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) {p : V} (v w : V)
    (hp : ∀ s : ℂ, p + s • v ∈ U) :
    HasSum (fun i => c i * L i w * L i v * cexp (L i p))
      (deriv (fun s : ℂ => deriv (fun t : ℂ => ∑' i, c i * cexp (L i (p + s • v + t • w))) 0) 0) := by
  have h := hasSum_deriv hU (fun i => c i * L i w) L
    (fun q hq => summable_norm_iff.2 (hasSum_deriv hU c L hs hq w).summable)
    (p := p) (by simpa using hp 0) v
  convert h using 3 with s
  exact (hasSum_deriv hU c L hs (hp s) w).tsum_eq.symm

end General

variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem imH_isHermitian (Z : Matrix (Fin N) (Fin N) ℂ) : (imH Z).IsHermitian := by
  unfold imH IsHermitian
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, ← neg_sub Z, smul_neg,
    ← neg_smul]
  congr 1
  simp

theorem isOpen_dom : IsOpen {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := by
  refine isOpen_iff_mem_nhds.2 fun p hp => ?_
  refine Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
    (fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N => imH (q.1 τ)) (fun i j => ?_)
    (fun q => imH_isHermitian _) p (hp τ)
  change Continuous fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
    (2 * I)⁻¹ * (q.1 τ i j - star (q.1 τ j i))
  fun_prop

theorem expo_eq (x : Matrix (Fin n) (Fin N) E) (Z : CF Ψ N N) (z z' : CF Ψ n N) :
    expo Ψ x Z z z' = ∑ τ : Ψ, ∑ k, (∑ a, ∑ b, τ.1 (x k a) * (Z τ a b * conj (τ.1 (x k b))) +
      ∑ a, τ.1 (x k a) * z τ k a + ∑ a, z' τ k a * conj (τ.1 (x k a))) := by
  simp only [expo, dotProduct, mulVec, Finset.mul_sum]

noncomputable def form (x : Matrix (Fin n) (Fin N) E) :
    (CF Ψ N N × CF Ψ n N × CF Ψ n N) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => 2 * π * I * expo Ψ x p.1 p.2.1 p.2.2
      map_add' := fun p q => by
        simp only [expo_eq, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, add_mul,
          Finset.sum_add_distrib]
        ring
      map_smul' := fun c p => by
        simp only [expo_eq, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        congr 1
        · congr 1
          · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => by ring
        · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => by ring }

theorem form_apply (x : Matrix (Fin n) (Fin N) E) (p : CF Ψ N N × CF Ψ n N × CF Ψ n N) :
    form Ψ x p = 2 * π * I * expo Ψ x p.1 p.2.1 p.2.2 := rfl

open Classical in

noncomputable def dir {m : ℕ} (τ : Ψ) (k : Fin m) (a : Fin N) : CF Ψ m N :=
  fun σ i j => if σ = τ then if i = k then if j = a then 1 else 0 else 0 else 0

open Classical in

theorem add_smul_dir {m : ℕ} (x : CM Ψ m N) (τ : Ψ) (k : Fin m) (a : Fin N) (s : ℂ) :
    (fun σ => x σ + if σ = τ then Matrix.single k a s else 0 : CM Ψ m N) =
      (HAdd.hAdd (α := CF Ψ m N) (β := CF Ψ m N) x (s • dir Ψ τ k a) : CF Ψ m N) := by
  funext σ i j
  change x σ i j + (if σ = τ then Matrix.single k a s else 0 : Matrix (Fin m) (Fin N) ℂ) i j =
    x σ i j + s * dir Ψ τ k a σ i j
  by_cases h : σ = τ <;> by_cases h1 : i = k <;> by_cases h2 : j = a <;>
    simp [dir, h, h1, h2, Matrix.single] <;> tauto

theorem form_dir₁ (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (a b : Fin N) :
    form Ψ x (dir Ψ τ a b, 0, 0) = 2 * π * I * ∑ k, τ.1 (x k a) * conj (τ.1 (x k b)) := by
  classical
  rw [form_apply, expo_eq, Finset.sum_eq_single τ]
  · simp [dir]
  · intro σ _ h
    simp [dir, h]
  · simp

theorem form_dir₂ (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (k : Fin n) (a : Fin N) :
    form Ψ x (0, dir Ψ τ k a, 0) = 2 * π * I * τ.1 (x k a) := by
  classical
  rw [form_apply, expo_eq, Finset.sum_eq_single τ]
  · simp [dir]
  · intro σ _ h
    simp [dir, h]
  · simp

theorem form_dir₃ (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (k : Fin n) (a : Fin N) :
    form Ψ x (0, 0, dir Ψ τ k a) = 2 * π * I * conj (τ.1 (x k a)) := by
  classical
  rw [form_apply, expo_eq, Finset.sum_eq_single τ]
  · simp [dir]
  · intro σ _ h
    simp [dir, h]
  · simp

open Classical in

theorem line₁ (Z : CF Ψ N N) (z z' : CF Ψ n N) (τ : Ψ) (a b : Fin N) (s : ℂ) :
    (Z, z, z') + s • ((dir Ψ τ a b, 0, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N) =
      (Z + s • dir Ψ τ a b, z, z') := by simp

theorem line₂ (Z : CF Ψ N N) (z z' v : CF Ψ n N) (s : ℂ) :
    (Z, z, z') + s • ((0, v, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N) = (Z, z + s • v, z') := by simp

theorem line₃ (Z : CF Ψ N N) (z z' v : CF Ψ n N) (s : ℂ) :
    (Z, z, z') + s • ((0, 0, v) : CF Ψ N N × CF Ψ n N × CF Ψ n N) = (Z, z, z' + s • v) := by simp

theorem heat_dir (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (hs : ∀ p ∈ {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N},
      Summable fun x => ‖φ x * cexp (form Ψ x p)‖)
    (Z : CF Ψ N N) (hZ : (Z : CM Ψ N N) ∈ Hn Ψ N) (z z' : CF Ψ n N) (τ : Ψ) (a b : Fin N) :
    2 * π * I * deriv (fun s : ℂ => ∑' x, φ x * cexp (form Ψ x (Z + s • dir Ψ τ a b, z, z'))) 0 =
      ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ => ∑' x, φ x *
        cexp (form Ψ x (Z, z + s • dir Ψ τ k a, z' + t • dir Ψ τ k b))) 0) 0 := by
  have h1 := (hasSum_deriv (isOpen_dom Ψ) φ (form Ψ) hs (p := (Z, z, z')) hZ
    (dir Ψ τ a b, 0, 0)).mul_left (2 * π * I)
  have h2 := hasSum_sum (s := Finset.univ) fun k _ =>
    hasSum_deriv_deriv (isOpen_dom Ψ) φ (form Ψ) hs (p := (Z, z, z'))
      (0, dir Ψ τ k a, 0) (0, 0, dir Ψ τ k b) (fun s => by rw [line₂]; exact hZ)
  have e : (fun x => 2 * π * I * (φ x * form Ψ x (dir Ψ τ a b, 0, 0) * cexp (form Ψ x (Z, z, z')))) =
      fun x => ∑ k, φ x * form Ψ x (0, 0, dir Ψ τ k b) * form Ψ x (0, dir Ψ τ k a, 0) *
        cexp (form Ψ x (Z, z, z')) := by
    funext x
    simp only [form_dir₁, form_dir₂, form_dir₃, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e] at h1
  have h3 := h1.unique h2
  simp only [line₁, line₂, line₃] at h3
  exact h3

end GlobalTheory.SW.ExpSum

open GlobalTheory.SW.ExpSum in

theorem GlobalTheory.SW.isHeat_thH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → IsHeat Ψ (thH Ψ φ) := by
  intro E _ _ _ Ψ hΨ n N φ hφ
  have hs : ∀ p ∈ {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N},
      Summable fun x => ‖φ x * cexp (form Ψ x p)‖ := fun p hp =>
    (GlobalTheory.SW.thH_summable_and_inj E Ψ hΨ n N φ hφ _ hp).1 _ _
  refine ⟨differentiableOn (isOpen_dom Ψ) φ (form Ψ) hs, fun Z hZ z z' τ a b => ?_⟩
  simp only [add_smul_dir]
  exact heat_dir Ψ φ hs Z hZ z z' τ a b
