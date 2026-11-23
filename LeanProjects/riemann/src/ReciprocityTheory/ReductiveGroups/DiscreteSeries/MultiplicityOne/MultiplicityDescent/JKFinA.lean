import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.BesselIsometryScalar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.LocalSquareIntegrableKFinite
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoWA

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down.KF

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

section abstract

variable {K : Type} [Group K] [TopologicalSpace K]

def Fin2 (α : C(K, ℂ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → K → ℂ) (β : ι → C(K, ℂ)), ∀ k₀ κ, α (k₀ * κ) = ∑ i, a i k₀ * β i κ

def finAlg (K : Type) [Group K] [TopologicalSpace K] : StarSubalgebra ℂ C(K, ℂ) where
  carrier := {α | Fin2 α}
  mul_mem' := by
    rintro α α' ⟨ι, _, a, β, h⟩ ⟨ι', _, a', β', h'⟩
    refine ⟨ι × ι', inferInstance, fun i k => a i.1 k * a' i.2 k, fun i => β i.1 * β' i.2, fun k₀ κ => ?_⟩
    rw [ContinuousMap.mul_apply, h, h', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousMap.mul_apply]; ring
  add_mem' := by
    rintro α α' ⟨ι, _, a, β, h⟩ ⟨ι', _, a', β', h'⟩
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim β β', fun k₀ κ => ?_⟩
    rw [ContinuousMap.add_apply, h, h', Fintype.sum_sum_type]
    rfl
  algebraMap_mem' c := ⟨Unit, inferInstance, fun _ _ => c, fun _ => 1, fun k₀ κ => by simp⟩
  star_mem' := by
    rintro α ⟨ι, _, a, β, h⟩
    refine ⟨ι, inferInstance, fun i k => star (a i k), fun i => star (β i), fun k₀ κ => ?_⟩
    rw [ContinuousMap.star_apply, h, star_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [star_mul', ContinuousMap.star_apply]

theorem exists_pairing [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (hsep : (finAlg K).SeparatesPoints) (g : C(K, ℂ)) (hg : g 1 ≠ 0) :
    ∃ α : C(K, ℂ), Fin2 α ∧ ∫ κ, α κ * g κ ∂μ ≠ 0 := by
  by_contra hn
  push Not at hn
  have hint : ∀ α : C(K, ℂ), Integrable (fun κ => α κ * g κ) μ := fun α =>
    (BoundedContinuousFunction.mkOfCompact (α * g)).integrable μ
  let Λ : C(K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun α => ∫ κ, α κ * g κ ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hint a) (hint b)]
        simp only [ContinuousMap.add_apply, add_mul]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc] }
  have hΛ : ∀ α, ‖Λ α‖ ≤ (‖g‖ * μ.real Set.univ) * ‖α‖ := fun α => by
    refine (norm_integral_le_of_norm_le_const (C := ‖α‖ * ‖g‖) (Filter.Eventually.of_forall fun κ => ?_)).trans
      (le_of_eq (by ring))
    rw [norm_mul]
    exact mul_le_mul (α.norm_coe_le_norm κ) (g.norm_coe_le_norm κ) (norm_nonneg _) (norm_nonneg _)
  have hcl : IsClosed {α : C(K, ℂ) | Λ.mkContinuous _ hΛ α = 0} := isClosed_eq (Λ.mkContinuous _ hΛ).continuous continuous_const
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (finAlg K) hsep
  have hmem : star g ∈ closure ((finAlg K : StarSubalgebra ℂ C(K, ℂ)) : Set C(K, ℂ)) := by
    have : star g ∈ (finAlg K).topologicalClosure := by rw [htop]; trivial
    exact this
  have h0 : ∫ κ, (star g) κ * g κ ∂μ = 0 := hcl.closure_subset_iff.2 (fun α hα => hn α hα) hmem
  have e : ∀ κ, (star g) κ * g κ = ((‖g κ‖ ^ 2 : ℝ) : ℂ) := fun κ => by
    rw [ContinuousMap.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [e] at h0
  rw [integral_complex_ofReal] at h0
  have h1 : ∫ κ, ‖g κ‖ ^ 2 ∂μ = 0 := by exact_mod_cast h0
  have hc : Continuous fun κ => ‖g κ‖ ^ 2 := g.continuous.norm.pow 2
  have hi : Integrable (fun κ => ‖g κ‖ ^ 2) μ :=
    (BoundedContinuousFunction.mkOfCompact (⟨_, hc⟩ : C(K, ℝ))).integrable μ
  have h2 := (integral_eq_zero_iff_of_nonneg (fun κ => sq_nonneg _) hi).1 h1
  have h3 := congrFun ((hc.ae_eq_iff_eq μ continuous_const).1 h2) 1
  exact hg (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3))

end abstract

variable {k r : ℕ}

def KK (k r : ℕ) : Set (Mat k r) := GV k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)

theorem kk_closed (h : UnitaryGroupStructuralFacts) : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ KK k r} := by
  have h1 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r)ᴴ * Matrix.of x = 1} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose).matrix_mul continuous_id) continuous_const
  have e : {x : Mt k r | (Matrix.of x : Mat k r) ∈ KK k r} =
      {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} ∩ {x : Mt k r | (Matrix.of x : Mat k r)ᴴ * Matrix.of x = 1} := by
    ext x
    exact and_congr_right fun _ => Matrix.mem_unitaryGroup_iff'
  rw [e]
  exact (SquareIntegrabilityOnOrbit.closed_GV h).inter h1

theorem kk_sub (h : UnitaryGroupStructuralFacts) : IsClosedSubgroup (KK k r) where
  one_mem := ⟨SquareIntegrabilityOnOrbit.gv_one', one_mem _⟩
  mul_mem a ha b hb := ⟨gv_mul ha.1 hb.1, mul_mem ha.2 hb.2⟩
  inv_mem a ha := by
    refine ⟨gv_inv ha.1, ?_⟩
    have p1 : aᴴ * a = 1 := Matrix.mem_unitaryGroup_iff'.1 ha.2
    rw [Matrix.inv_eq_left_inv p1]
    refine Matrix.mem_unitaryGroup_iff.2 ?_
    show aᴴ * (aᴴ)ᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose, p1]
  unit a ha := Matrix.isUnit_det_of_left_inverse (gv_inv_mul ha.1)
  closed := kk_closed h

theorem kk_compact (h : UnitaryGroupStructuralFacts) : IsCompact {x : Mt k r | (Matrix.of x : Mat k r) ∈ KK k r} := by
  refine Metric.isCompact_of_isClosed_isBounded (kk_closed h) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Mt k r)) (r := 1)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  exact entry_norm_bound_of_unitary hx.2 i j

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down.KF
