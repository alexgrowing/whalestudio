import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlSpanImageContinuousRepFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRepStatement
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.SmallTrace

theorem exists_ball_sub_image {l : ℕ} [Fact l.Prime] {ι F : Type} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℚ_[l] F] (S : (ι → ℚ_[l]) →ₗ[ℚ_[l]] F) :
    ∃ ε > 0, ∀ w ∈ LinearMap.range S, ‖w‖ < ε → ∃ x : ι → ℚ_[l], ‖x‖ < 1 ∧ S x = w := by
  have hS' : Function.Surjective S.rangeRestrict := LinearMap.surjective_rangeRestrict S
  have ho : IsOpenMap S.rangeRestrict := LinearMap.isOpenMap_of_finiteDimensional _ hS'
  have hU : IsOpen (S.rangeRestrict '' Metric.ball 0 1) := ho _ Metric.isOpen_ball
  have h0 : (0 : LinearMap.range S) ∈ S.rangeRestrict '' Metric.ball 0 1 := ⟨0, by simp, by simp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  refine ⟨ε, hε, fun w hw hwε => ?_⟩
  have hmem : (⟨w, hw⟩ : LinearMap.range S) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]; exact hwε
  obtain ⟨x, hx, hxw⟩ := hball hmem
  refine ⟨x, by simpa using hx, ?_⟩
  have := congrArg Subtype.val hxw
  simpa using this

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

noncomputable def matOf (r : Γ →* GL (Fin a) (PadicAlgCl l)) (f : Γ →₀ ℤ_[l]) :
    Matrix (Fin a) (Fin a) (PadicAlgCl l) :=
  f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
    ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))

theorem matOf_eq_lc (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ) (f : Γ →₀ ℤ_[l])
    (hf : f.support ⊆ t) :
    matOf r f = Fintype.linearCombination ℚ_[l]
      (fun i : t => ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))
      (fun i => (f i : ℚ_[l])) := by
  rw [Fintype.linearCombination_apply, matOf, Finsupp.sum_of_support_subset f hf _ (by simp)]
  rw [← Finset.sum_coe_sort t]
  simp [algebraMap_smul]

theorem exists_matOf_eq (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ) (y : t → ℤ_[l]) :
    ∃ f' : Γ →₀ ℤ_[l], matOf r f' = Fintype.linearCombination ℚ_[l]
      (fun i : t => ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))
      (fun i => (y i : ℚ_[l])) := by
  classical
  let f' : Γ →₀ ℤ_[l] := Finsupp.onFinset t (fun g => if h : g ∈ t then y ⟨g, h⟩ else 0)
    (by intro g hg; by_contra h; simp [h] at hg)
  refine ⟨f', ?_⟩
  rw [matOf_eq_lc r t f' (Finsupp.support_onFinset_subset)]
  congr 1
  funext i
  simp [f', Finsupp.onFinset_apply, i.2]

end GlobalTheory.SmallTrace

namespace GlobalTheory.SmallTrace
variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

theorem matOf_single (r : Γ →* GL (Fin a) (PadicAlgCl l)) (g : Γ) :
    matOf r (Finsupp.single g 1) =
      ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
  rw [matOf, Finsupp.sum_single_index (by simp)]
  simp

theorem matOf_mem_span (r : Γ →* GL (Fin a) (PadicAlgCl l)) (f : Γ →₀ ℤ_[l]) :
    matOf r f ∈ Submodule.span (PadicAlgCl l) (Set.range fun g =>
      ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  rw [matOf]
  exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)

theorem trace_zero_of_finset (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ)
    (ht : ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ matOf r f = matOf r f')
    (D : Matrix (Fin a) (Fin a) (PadicAlgCl l))
    (hD : ∀ i : t, (D * ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace = 0)
    (g : Γ) : (D * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace = 0 := by
  obtain ⟨f', hf't, hf'⟩ := ht (Finsupp.single g 1)
  rw [matOf_single, matOf_eq_lc r t f' hf't, Fintype.linearCombination_apply] at hf'
  rw [hf', Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, hD i, smul_zero]

end GlobalTheory.SmallTrace

namespace GlobalTheory.SmallTrace
variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

theorem finiteRing_sq_sub_mul_sq_eq_of_card [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (r : Γ →* GL (Fin a) (PadicAlgCl l)) (hr : Continuous r) (hss : IsSSRep r) :
    ∃ c : ℕ, ∀ (n : ℕ) (f : Γ →₀ ℤ_[l]),
      (∀ g, ‖(matOf r f * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace‖
        ≤ ((l : ℝ)⁻¹) ^ (n + c)) →
      ∃ f' : Γ →₀ ℤ_[l], matOf r f = ((l : PadicAlgCl l) ^ n) • matOf r f' := by
  obtain ⟨t, ht⟩ := GlobalTheory.T.zlSpan_image_continuous_rep_finite l Γ a r hr
  have ht' : ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ matOf r f = matOf r f' := ht
  let v : t → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun i =>
    ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))
  let Φ : Matrix (Fin a) (Fin a) (PadicAlgCl l) →ₗ[ℚ_[l]] (t → PadicAlgCl l) :=
    { toFun := fun M i => (M * v i).trace
      map_add' := by intro M N; funext i; simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := by intro c M; funext i; simp [Matrix.smul_mul, Matrix.trace_smul] }
  let S : (t → ℚ_[l]) →ₗ[ℚ_[l]] (t → PadicAlgCl l) := Φ ∘ₗ Fintype.linearCombination ℚ_[l] v
  obtain ⟨ε, hε, hball⟩ := exists_ball_sub_image S
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ((l : ℝ)⁻¹) ^ c < ε :=
    exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl1)
  refine ⟨c, fun n f hf => ?_⟩
  obtain ⟨f0, hf0t, hf0⟩ := ht' f
  set x0 : t → ℚ_[l] := fun i => (f0 i : ℚ_[l]) with hx0
  have hMf : matOf r f = Fintype.linearCombination ℚ_[l] v x0 := by
    rw [hf0]; exact matOf_eq_lc r t f0 hf0t
  have hΦf : ‖Φ (matOf r f)‖ ≤ ((l : ℝ)⁻¹) ^ (n + c) :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => hf i
  set q : ℚ_[l] := ((l : ℚ_[l]) ^ n)⁻¹ with hq
  have hlQ : (l : ℚ_[l]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hqn : ‖q‖ = (l : ℝ) ^ n := by
    rw [hq, norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]
  set w : t → PadicAlgCl l := q • Φ (matOf r f) with hw
  have hwS : w = S (q • x0) := by
    rw [hw, map_smul, hMf]; rfl
  have hwε : ‖w‖ < ε := by
    rw [hw, norm_smul, hqn]
    calc (l : ℝ) ^ n * ‖Φ (matOf r f)‖ ≤ (l : ℝ) ^ n * ((l : ℝ)⁻¹) ^ (n + c) :=
          mul_le_mul_of_nonneg_left hΦf (by positivity)
      _ = ((l : ℝ)⁻¹) ^ c := by
          rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hl0.ne', one_pow, one_mul]
      _ < ε := hc
  obtain ⟨y, hy1, hy⟩ := hball w ⟨_, hwS.symm⟩ hwε
  have hyi : ∀ i, ‖y i‖ ≤ 1 := fun i => (norm_le_pi_norm y i).trans hy1.le
  let yz : t → ℤ_[l] := fun i => ⟨y i, hyi i⟩
  obtain ⟨f', hf'⟩ := exists_matOf_eq r t yz
  refine ⟨f', ?_⟩
  have hlK : ((l : PadicAlgCl l) ^ n) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℚ_[l]) ^ n) := by simp
  rw [← sub_eq_zero]
  apply GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep (PadicAlgCl l) Γ a r hss
  · exact Submodule.sub_mem _ (matOf_mem_span r f)
      (Submodule.smul_mem _ _ (matOf_mem_span r f'))
  · apply trace_zero_of_finset r t ht'
    intro i
    have hy' : Fintype.linearCombination ℚ_[l] v (fun i => (yz i : ℚ_[l])) = Fintype.linearCombination ℚ_[l] v y := rfl
    have key : Φ (matOf r f - ((l : PadicAlgCl l) ^ n) • matOf r f') = 0 := by
      rw [hf', hy', hlK, algebraMap_smul, map_sub, map_smul]
      have : Φ (Fintype.linearCombination ℚ_[l] v y) = w := hy
      rw [this, hw, smul_smul, hq, mul_inv_cancel₀ hlQ, one_smul, sub_self]
    exact congrFun key i

end GlobalTheory.SmallTrace

theorem GlobalTheory.smallTrace_dvd_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → IsSSRep r → ∃ c : ℕ, ∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) = ((l : PadicAlgCl l) ^ n) • (f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  intro l _ Γ _ _ _ _ a r hr hss
  exact GlobalTheory.SmallTrace.finiteRing_sq_sub_mul_sq_eq_of_card r hr hss
