import Mathlib
import Formalism.HermitianLattices.DefsCS
import Formalism.HermitianLattices.HermitianLatticesProofs.ThetaSummable
import Lemmata.GeneralBFactSecondSide.Imports

open Module Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section TR

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

lemma traceReal_star (z : K) : Algebra.trace ℚ K (starRingEnd K z) = Algebra.trace ℚ K z := by
  let e : K ≃ₐ[ℚ] K :=
    AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut K)) (fun q => by simp [starRingAut])
  exact Algebra.trace_eq_of_algEquiv e z

lemma traceReal_star_rat (q : ℚ) : starRingEnd K (algebraMap ℚ K q) = algebraMap ℚ K q := by
  rw [eq_ratCast (algebraMap ℚ K) q, map_ratCast]

lemma traceReal_trace_smul (q : ℚ) (z : K) :
    Algebra.trace ℚ K (algebraMap ℚ K q * z) = q * Algebra.trace ℚ K z := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

lemma traceReal_den (a : K) :
    ∃ k : ℤ, k ≠ 0 ∧ ∃ α : NumberField.RingOfIntegers K, (k : K) * a = (α : K) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) {a}
  refine ⟨y, hy0, ⟨y • a, hy a (by simp)⟩, ?_⟩
  simp [zsmul_eq_mul]

variable [Module (NumberField.RingOfIntegers K) V]
  [IsScalarTower (NumberField.RingOfIntegers K) K V]

lemma traceReal_mult (M : Submodule (NumberField.RingOfIntegers K) V) (hM : Submodule.IsLattice K M)
    (x : V) : ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ M := by
  first | exact Bl.general_b_fact_second'''''.goal1 .. | (apply Bl.general_b_fact_second'''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second'''''.goal1 <;> assumption)

lemma traceReal_lower (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (L : Submodule (NumberField.RingOfIntegers K) V) [Submodule.IsLattice K L] :
    ∃ l : ℝ, 0 < l ∧ ∀ x ∈ L, x ≠ 0 → l ≤ ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
  classical
  have := isAddTorsionFree_ringOfIntegers_submodule L
  have : Module.Finite ℤ L := Module.Finite.trans (NumberField.RingOfIntegers K) L
  let b := Module.Free.chooseBasis ℤ L
  let e : Module.Free.ChooseBasisIndex ℤ L → V := fun i => ((b i : L) : V)
  let G : Matrix (Module.Free.ChooseBasisIndex ℤ L) (Module.Free.ChooseBasisIndex ℤ L) ℚ :=
    fun i j => Algebra.trace ℚ K (h (e i) (e j))
  have hcoe : ∀ c : Module.Free.ChooseBasisIndex ℤ L → ℤ,
      (((∑ i, c i • b i : L)) : V) = ∑ i, c i • e i := by
    intro c; simp [e]
  have hqc : ∀ c : Module.Free.ChooseBasisIndex ℤ L → ℤ,
      Algebra.trace ℚ K (h (∑ i, c i • e i) (∑ i, c i • e i)) =
        (fun i => (c i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℚ)) := by
    intro c
    rw [thetaSummable_expand]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, G]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hZ : ∀ c : Module.Free.ChooseBasisIndex ℤ L → ℤ, c ≠ 0 →
      0 < (fun i => (c i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℚ)) := by
    intro c hc
    rw [← hqc]
    apply hpos
    rw [← hcoe]
    intro h0
    apply hc
    have h1 : (∑ i, c i • b i : L) = 0 := Subtype.ext h0
    funext i
    exact Fintype.linearIndependent_iff.mp b.linearIndependent c h1 i
  obtain ⟨l, hl, hcoer⟩ := thetaSummable_coercive_rat G (thetaSummable_ratpos G hZ)
  refine ⟨l, hl, fun x hx hx0 => ?_⟩
  set c := b.equivFun ⟨x, hx⟩ with hcdef
  have hxc : x = ∑ i, c i • e i := by
    rw [← hcoe, hcdef, b.sum_equivFun]
  have hc0 : c ≠ 0 := by
    intro hc
    apply hx0
    rw [hxc, hc]
    simp
  have hco := hcoer (fun i => (c i : ℚ))
  rw [← hqc, ← hxc] at hco
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hc0 (funext hh)
  have h2 : 0 < (c i) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))
  have h3 : (1 : ℤ) ≤ (c i) ^ 2 := by linarith [Int.add_one_le_iff.mpr h2]
  have h4 : (1 : ℝ) ≤ (((c i : ℤ) : ℚ) : ℝ) ^ 2 := by exact_mod_cast h3
  have h5 : (1 : ℝ) ≤ ∑ j, (((c j : ℤ) : ℚ) : ℝ) ^ 2 :=
    h4.trans (Finset.single_le_sum (f := fun j => (((c j : ℤ) : ℚ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  nlinarith

variable [FiniteDimensional K V]

theorem traceReal_main (h : V →ₗ⋆[K] V →ₗ[K] K) (hS : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) :
    ∃ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) ∧
      (∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖) ∧
      (∀ M : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K M →
        ∃ _ : DiscreteTopology (zmap ι M), IsZLattice ℝ (zmap ι M)) := by
  classical
  let iQ : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  have hQs : ∀ (q : ℚ) (x : V), q • x = (algebraMap ℚ K q) • x := fun _ _ => rfl
  have : IsScalarTower ℚ K V := ⟨fun q a x => by rw [hQs, Algebra.smul_def, mul_smul]⟩
  have : FiniteDimensional ℚ V := Module.Finite.trans K V
  let B : LinearMap.BilinForm ℚ V := LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ K (h x y))
    (fun x₁ x₂ y => by simp only [map_add, LinearMap.add_apply])
    (fun q x y => by
      simp only [hQs, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        traceReal_star_rat, traceReal_trace_smul])
    (fun x y₁ y₂ => by simp only [map_add])
    (fun q x y => by simp only [hQs, map_smul, smul_eq_mul, traceReal_trace_smul])
  have hB : ∀ x y, B x y = Algebra.trace ℚ K (h x y) := fun _ _ => rfl
  have hBS : LinearMap.IsSymm B := ⟨fun x y => by
    simp only [RingHom.id_apply, hB]
    rw [← hS.eq x y, traceReal_star]⟩
  obtain ⟨v, hv⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (K := ℚ) (V := V) (B := B)
      (hK := invertibleOfNonzero (two_ne_zero : (2 : ℚ) ≠ 0)) hBS
  let d : Fin (finrank ℚ V) → ℚ := fun i => B (v i) (v i)
  have hd : ∀ i, 0 < d i := fun i => hpos _ (v.ne_zero i)
  have hdr : ∀ i, 0 < ((d i : ℚ) : ℝ) := fun i => by exact_mod_cast hd i
  have hsq : ∀ i, 0 < Real.sqrt (d i) := fun i => Real.sqrt_pos.mpr (hdr i)
  let f : V → EuclideanSpace ℝ (Fin (finrank ℚ V)) := fun x =>
    WithLp.toLp 2 (fun i => Real.sqrt (d i) * (v.repr x i : ℝ))
  let ι : V →+ EuclideanSpace ℝ (Fin (finrank ℚ V)) :=
    { toFun := f
      map_zero' := by ext i; simp [f]
      map_add' := fun x y => by ext i; simp [f, mul_add] }
  have hιapp : ∀ x i, (ι x) i = Real.sqrt (d i) * (v.repr x i : ℝ) := fun _ _ => rfl
  have hBexp : ∀ x y, B x y = ∑ i, v.repr x i * v.repr y i * d i := by
    intro x y
    calc B x y = B (∑ i, v.repr x i • v i) (∑ j, v.repr y j • v j) := by
          rw [v.sum_repr, v.sum_repr]
      _ = ∑ i, ∑ j, v.repr x i * v.repr y j * B (v i) (v j) := by
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
            Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = ∑ i, v.repr x i * v.repr y i * d i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single i]
          · intro j _ hji
            rw [hv (Ne.symm hji)]
            simp
          · simp
  have hinner : ∀ x y, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ) := by
    intro x y
    rw [← hB, hBexp]
    simp only [PiLp.inner_apply, hιapp, RCLike.inner_apply, conj_trivial]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Real.mul_self_sqrt (hdr i).le
    linear_combination (((v.repr x i : ℚ) : ℝ) * ((v.repr y i : ℚ) : ℝ)) * this
  have hιq : ∀ (q : ℚ) x, ι (q • x) = (q : ℝ) • ι x := by
    intro q x
    ext i
    simp only [hιapp, map_smul, Finsupp.smul_apply, smul_eq_mul, Rat.cast_mul, PiLp.smul_apply]
    ring
  have hcoord : ∀ x i, |(v.repr x i : ℝ)| ≤ ‖ι x‖ / Real.sqrt (d i) := by
    intro x i
    have h1 := PiLp.norm_apply_le (ι x) i
    rw [hιapp, Real.norm_eq_abs, abs_mul, abs_of_pos (hsq i)] at h1
    rw [le_div_iff₀ (hsq i)]
    linarith [mul_comm (Real.sqrt (d i)) |(v.repr x i : ℝ)|]
  have hbound : ∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖ := by
    intro a
    refine ⟨∑ j, ‖ι (a • v j)‖ / Real.sqrt (d j), fun x => ?_⟩
    have hax : a • x = ∑ j, v.repr x j • (a • v j) := by
      conv_lhs => rw [← v.sum_repr x]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hQs, hQs, smul_smul, smul_smul, mul_comm]
    rw [hax, map_sum]
    simp only [hιq]
    calc ‖∑ j, ((v.repr x j : ℚ) : ℝ) • ι (a • v j)‖
        ≤ ∑ j, ‖((v.repr x j : ℚ) : ℝ) • ι (a • v j)‖ := norm_sum_le _ _
      _ = ∑ j, |(v.repr x j : ℝ)| * ‖ι (a • v j)‖ :=
          Finset.sum_congr rfl fun j _ => by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ j, ‖ι x‖ / Real.sqrt (d j) * ‖ι (a • v j)‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcoord x j) (norm_nonneg _)
      _ = (∑ j, ‖ι (a • v j)‖ / Real.sqrt (d j)) * ‖ι x‖ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  have hmem : ∀ (M : Submodule (NumberField.RingOfIntegers K) V) y,
      y ∈ zmap ι M ↔ ∃ m ∈ M, ι m = y := by
    intro M y
    show y ∈ AddSubgroup.map ι M.toAddSubgroup ↔ _
    rw [AddSubgroup.mem_map]
    rfl
  have hnorm : ∀ x, ‖ι x‖ ^ 2 = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
    intro x
    rw [← hinner, real_inner_self_eq_norm_sq]
  refine ⟨finrank ℚ V, ι, hinner, hbound, fun M hM => ?_⟩
  have := hM
  obtain ⟨l, hl, hlow⟩ := traceReal_lower h hpos M
  have hdisc : DiscreteTopology (zmap ι M) := by
    apply discreteTopology_of_isOpen_singleton_zero
    rw [Metric.isOpen_singleton_iff]
    refine ⟨Real.sqrt l, Real.sqrt_pos.mpr hl, fun y hy => ?_⟩
    by_contra hy0
    obtain ⟨m, hm, hmy⟩ := (hmem M y.1).mp y.2
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hy0
      apply Subtype.ext
      rw [← hmy, map_zero]
      rfl
    have hy' : ‖ι m‖ < Real.sqrt l := by
      rw [hmy]
      simpa [dist_zero_right] using hy
    have h1 := (Real.lt_sqrt (norm_nonneg _)).mp hy'
    have h2 := hlow m hm hm0
    rw [← hnorm] at h2
    linarith
  have hspan : Submodule.span ℝ (zmap ι M : Set (EuclideanSpace ℝ (Fin (finrank ℚ V)))) = ⊤ := by
    have hin : ∀ x : V, ι x ∈ Submodule.span ℝ (zmap ι M : Set (EuclideanSpace ℝ (Fin (finrank ℚ V)))) := by
      intro x
      obtain ⟨n, hn, hnx⟩ := traceReal_mult M hM x
      have h1 : ι (n • x) ∈ Submodule.span ℝ (zmap ι M : Set (EuclideanSpace ℝ (Fin (finrank ℚ V)))) :=
        Submodule.subset_span ((hmem M _).mpr ⟨_, hnx, rfl⟩)
      rw [map_zsmul] at h1
      have h2 := Submodule.smul_mem _ ((n : ℝ)⁻¹) h1
      rwa [← Int.cast_smul_eq_zsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn),
        one_smul] at h2
    rw [eq_top_iff, ← (EuclideanSpace.basisFun (Fin (finrank ℚ V)) ℝ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hvi : ι (v i) = Real.sqrt (d i) • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      rw [hιapp, v.repr_self, PiLp.smul_apply, PiLp.single_apply, Finsupp.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    have := Submodule.smul_mem _ (Real.sqrt (d i))⁻¹ (hin (v i))
    rw [hvi, smul_smul, inv_mul_cancel₀ (hsq i).ne', one_smul] at this
    simpa [EuclideanSpace.basisFun_apply] using this
  exact ⟨hdisc, ⟨hspan⟩⟩

end TR

theorem traceReal : TraceReal := by
  intro K V _ _ _ _ _ _ _ _ h hS hpos
  exact traceReal_main h hS hpos

end Formalism.HermitianLatticesTheory
