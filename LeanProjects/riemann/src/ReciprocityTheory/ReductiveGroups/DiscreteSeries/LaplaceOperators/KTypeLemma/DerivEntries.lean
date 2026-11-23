import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensorActionApplyDual
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem ode_zero {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (A : Module.End ℂ U)
    (G : ℝ → U →ₗ[ℂ] ℂ) (hG : ∀ s y, HasDerivAt (fun s => G s y) (-(G s (A y))) s) (h0 : G 0 = 0)
    (s : ℝ) : G s = 0 := by
  let b := Module.finBasis ℂ U
  let L : (Fin (Module.finrank ℂ U) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ U) → ℂ) :=
    LinearMap.toContinuousLinearMap
      (LinearMap.pi fun i => -∑ j, b.repr (A (b i)) j • LinearMap.proj j)
  have hg : ∀ t, HasDerivAt (fun s i => G s (b i)) (L fun i => G t (b i)) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    refine (hG t (b i)).congr_deriv ?_
    have := congrArg (G t) (b.sum_repr (A (b i)))
    simp only [map_sum, map_smul, smul_eq_mul] at this
    simp [L, this]
  have hz := ODE_solution_unique_univ (v := fun _ x => L x) (s := fun _ => Set.univ) (K := ‖L‖₊)
    (t₀ := 0) (f := fun s i => G s (b i)) (g := fun _ => 0)
    (fun _ => L.lipschitz.lipschitzOnWith) (fun t => ⟨hg t, trivial⟩)
    (fun t => ⟨by simpa using hasDerivAt_const t (0 : Fin (Module.finrank ℂ U) → ℂ), trivial⟩)
    (by funext i; simp [h0])
  exact b.ext fun i => congrFun (congrFun hz s) i

def ei (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (((-s : ℝ) : ℂ) • X)

def cj (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ei X s * Y * NormedSpace.exp ((s : ℂ) • X)

open scoped Matrix.Norms.Operator in
theorem deriv_entries (X Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (a b : Fin n) :
    HasDerivAt (fun s => ei X s a b) (-((ei X s * X) a b)) s ∧
      HasDerivAt (fun s => cj X s Y a b) (-(cj X s (X * Y - Y * X) a b)) s := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) s
  have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) X s
  have e : ∀ s : ℝ, s • (-X) = ((-s : ℝ) : ℂ) • X := fun s => by
    rw [Complex.coe_smul, smul_neg, neg_smul]
  have e' : ∀ s : ℝ, s • X = (s : ℂ) • X := fun s => (Complex.coe_smul s X).symm
  simp only [e] at h1
  simp only [e'] at h2
  let P := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)
  refine ⟨(P.hasFDerivAt.comp_hasDerivAt s h1).congr_deriv ?_,
    (P.hasFDerivAt.comp_hasDerivAt s ((h1.mul_const Y).mul h2)).congr_deriv ?_⟩
  · show (ei X s * -X) a b = _
    rw [Matrix.mul_neg]; rfl
  · show (ei X s * -X * Y * NormedSpace.exp ((s : ℂ) • X) +
      ei X s * Y * (X * NormedSpace.exp ((s : ℂ) • X))) a b = _
    have e2 : ei X s * -X * Y * NormedSpace.exp ((s : ℂ) • X) +
        ei X s * Y * (X * NormedSpace.exp ((s : ℂ) • X)) = -cj X s (X * Y - Y * X) := by
      simp only [cj]; noncomm_ring
    rw [e2]; rfl

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def actL (E : Fin n → Fin n → Module.End ℂ M) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M where
  toFun := actM E
  map_add' X Y := by simp [actM, add_smul, sum_add_distrib]
  map_smul' c X := by simp [actM, smul_sum, smul_smul]

theorem actM_single (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b 1) = E a b := by
  simp [actM, Matrix.single_apply, ite_smul, ite_and]

def wB (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (w : List (Fin n × Fin n)) : M :=
  (w.map fun p => actM E (cj X s (Matrix.single p.1 p.2 1))).prod φ

def adX (X : Matrix (Fin n) (Fin n) ℂ) (w : List (Fin n × Fin n)) : List (Fin n × Fin n) →₀ ℂ :=
  ∑ a, ∑ b, X a b • adLW a b w

theorem lc_adL (a b : Fin n) (p : Fin n × Fin n) :
    Finsupp.linearCombination ℂ (fun q : Fin n × Fin n => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))
      (adL a b p) = Matrix.single a b 1 * Matrix.single p.1 p.2 1 -
        Matrix.single p.1 p.2 1 * Matrix.single a b 1 := by
  rw [adL, map_sub]
  congr 1
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ h]
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ h]

theorem lc_adX_cons (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    Finsupp.linearCombination ℂ (wB E φ X s) (adX X (p :: w)) =
      actM E (cj X s (X * Matrix.single p.1 p.2 1 - Matrix.single p.1 p.2 1 * X)) (wB E φ X s w) +
        actM E (cj X s (Matrix.single p.1 p.2 1))
          (Finsupp.linearCombination ℂ (wB E φ X s) (adX X w)) := by
  let C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M :=
    { toFun := fun Y => actM E (cj X s Y) (wB E φ X s w)
      map_add' := fun Y Y' => by
        have := (actL E).map_add (cj X s Y) (cj X s Y')
        simp only [cj, Matrix.mul_add, Matrix.add_mul]
        exact congrArg (fun A : Module.End ℂ M => A (wB E φ X s w)) this
      map_smul' := fun c Y => by
        have := (actL E).map_smul c (cj X s Y)
        simp only [cj, Matrix.mul_smul, Matrix.smul_mul]
        exact congrArg (fun A : Module.End ℂ M => A (wB E φ X s w)) this }
  have h1 : ∀ u : (Fin n × Fin n) →₀ ℂ,
      Finsupp.linearCombination ℂ (wB E φ X s) (u.mapDomain (· :: w)) =
        C (Finsupp.linearCombination ℂ
          (fun q : Fin n × Fin n => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ)) u) := fun u => by
    rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]; rfl
  have h2 : ∀ u : List (Fin n × Fin n) →₀ ℂ,
      Finsupp.linearCombination ℂ (wB E φ X s) (u.mapDomain (p :: ·)) =
        actM E (cj X s (Matrix.single p.1 p.2 1)) (Finsupp.linearCombination ℂ (wB E φ X s) u) :=
    fun u => by rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]; rfl
  have h3 : X * Matrix.single p.1 p.2 1 - Matrix.single p.1 p.2 1 * X =
      ∑ a, ∑ b, X a b • ((Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) * Matrix.single p.1 p.2 1 -
        Matrix.single p.1 p.2 1 * Matrix.single a b 1) := by
    have hX : X = ∑ a, ∑ b, X a b • (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp
    conv_lhs => rw [hX]
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_sub,
      sum_sub_distrib]
  show _ = C _ + _
  rw [h3]
  simp only [adX, adLW, map_sum, map_smul, map_add, smul_add, sum_add_distrib, h1, h2, lc_adL]

theorem deriv_word (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (w : List (Fin n × Fin n)) : ∀ l : M →ₗ[ℂ] ℂ, HasDerivAt (fun s => l (wB E φ X s w))
      (-(l (Finsupp.linearCombination ℂ (wB E φ X s) (adX X w)))) s := by
  induction w with
  | nil => intro l; simpa [wB, adX, adLW] using hasDerivAt_const s (l φ)
  | cons p w ih =>
    intro l
    have e : (fun s => l (wB E φ X s (p :: w))) = fun s => ∑ a, ∑ b,
        cj X s (Matrix.single p.1 p.2 1) a b * (l ∘ₗ E a b) (wB E φ X s w) := by
      funext s
      simp [wB, actM, map_sum]
    rw [e]
    refine (HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ =>
      ((deriv_entries X (Matrix.single p.1 p.2 1) s a b).2.mul (ih (l ∘ₗ E a b)))).congr_deriv ?_
    rw [lc_adX_cons]
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_add, map_sum, map_smul,
      smul_eq_mul, LinearMap.comp_apply, neg_add, ← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

theorem adLW_length (a b : Fin n) : ∀ (w w' : List (Fin n × Fin n)), w' ∈ (adLW a b w).support →
    w'.length = w.length := by
  classical
  intro w
  induction w with
  | nil => intro w' h; simp [adLW] at h
  | cons p w ih =>
    intro w' h
    rcases mem_union.mp (Finsupp.support_add h) with h | h
    · obtain ⟨q, -, rfl⟩ := mem_image.mp (Finsupp.mapDomain_support h); rfl
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp (Finsupp.mapDomain_support h)
      simp [ih q hq]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA
