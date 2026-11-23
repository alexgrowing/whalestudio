import Mathlib
import Formalism.HermitianLattices.GenusCovolBound
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic

open Module Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Trace

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem classSetAssembly_tr_add_left (h : V →ₗ⋆[K] V →ₗ[K] K) (x y z : V) :
    Algebra.trace ℚ K (h (x + y) z) = Algebra.trace ℚ K (h x z) + Algebra.trace ℚ K (h y z) := by
  simp only [map_add, LinearMap.add_apply]

theorem classSetAssembly_tr_sub_left (h : V →ₗ⋆[K] V →ₗ[K] K) (x y z : V) :
    Algebra.trace ℚ K (h (x - y) z) = Algebra.trace ℚ K (h x z) - Algebra.trace ℚ K (h y z) := by
  simp only [map_sub, LinearMap.sub_apply]

theorem classSetAssembly_tr_add_right (h : V →ₗ⋆[K] V →ₗ[K] K) (x y z : V) :
    Algebra.trace ℚ K (h z (x + y)) = Algebra.trace ℚ K (h z x) + Algebra.trace ℚ K (h z y) := by
  simp only [map_add]

theorem classSetAssembly_ratCast_mul (q : ℚ) (a : K) :
    Algebra.trace ℚ K ((q : K) * a) = q * Algebra.trace ℚ K a := by
  have e : (q : K) * a = q • a := by
    rw [Algebra.smul_def, eq_ratCast]
  rw [e, map_smul, smul_eq_mul]

theorem classSetAssembly_tr_qsmul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (q : ℚ) (x y : V) :
    Algebra.trace ℚ K (h ((q : K) • x) y) = q * Algebra.trace ℚ K (h x y) := by
  have e : h ((q : K) • x) y = (q : K) * h x y := by
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_ratCast]
  rw [e, classSetAssembly_ratCast_mul]

theorem classSetAssembly_tr_qsmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (q : ℚ) (x y : V) :
    Algebra.trace ℚ K (h x ((q : K) • y)) = q * Algebra.trace ℚ K (h x y) := by
  rw [map_smul, smul_eq_mul, classSetAssembly_ratCast_mul]

theorem classSetAssembly_tr_sum_left (h : V →ₗ⋆[K] V →ₗ[K] K) {ι : Type*} (s : Finset ι)
    (f : ι → V) (y : V) :
    Algebra.trace ℚ K (h (∑ i ∈ s, f i) y) = ∑ i ∈ s, Algebra.trace ℚ K (h (f i) y) := by
  rw [map_sum, LinearMap.sum_apply, map_sum]

theorem classSetAssembly_tr_sum_right (h : V →ₗ⋆[K] V →ₗ[K] K) {ι : Type*} (s : Finset ι)
    (f : ι → V) (y : V) :
    Algebra.trace ℚ K (h y (∑ i ∈ s, f i)) = ∑ i ∈ s, Algebra.trace ℚ K (h y (f i)) := by
  rw [map_sum, map_sum]

theorem classSetAssembly_trace_int (o : NumberField.RingOfIntegers K) :
    ∃ z : ℤ, Algebra.trace ℚ K (algebraMap (NumberField.RingOfIntegers K) K o) = z := by
  have hint_r : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K o) := by
    exact (NumberField.RingOfIntegers.isIntegral o).algebraMap
  have ht : IsIntegral ℤ (Algebra.trace ℚ K (algebraMap (NumberField.RingOfIntegers K) K o)) :=
    Algebra.isIntegral_trace hint_r
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp ht
  exact ⟨z, hz.symm.trans (eq_intCast (algebraMap ℤ ℚ) z)⟩

theorem classSetAssembly_dint [Module (NumberField.RingOfIntegers K) V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (d : ℕ) (x y : V)
    (hxy : (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K)) :
    ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x y) = z := by
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp hxy
  obtain ⟨z, hz⟩ := classSetAssembly_trace_int o
  refine ⟨z, ?_⟩
  rw [← hz, ho, ← classSetAssembly_ratCast_mul, Rat.cast_natCast]

end Trace

section Real

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

private theorem span_eq_top_of_li_lemma {n : ℕ} (w : Fin n → EuclideanSpace ℝ (Fin n))
    (hw : LinearIndependent ℝ w) : Submodule.span ℝ (Set.range w) = ⊤ := by
  have hc : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp
  exact hw.span_eq_top_of_card_eq_finrank' hc

private theorem eq_zero_of_inner_li_lemma_2 {n : ℕ} (w : Fin n → EuclideanSpace ℝ (Fin n))
    (hw : LinearIndependent ℝ w) (v : EuclideanSpace ℝ (Fin n))
    (hv : ∀ j, inner ℝ v (w j) = 0) : v = 0 := by
  have hs := span_eq_top_of_li_lemma w hw
  obtain ⟨b, hb⟩ : ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), ∀ i, b i = w i :=
    ⟨Basis.mk hw (by rw [hs]), fun i => by simp [Basis.mk_apply]⟩
  have key : inner ℝ v (∑ i, b.repr v i • b i) = 0 := by
    rw [inner_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_right, hb i, hv i, mul_zero]
  rw [b.sum_repr v] at key
  exact inner_self_eq_zero.mp key

theorem classSetAssembly_nondeg {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (y : V)
    (hy : ∀ j, Algebra.trace ℚ K (h y (u j)) = 0) : y = 0 := by
  have h0 : ι y = 0 := eq_zero_of_inner_li_lemma_2 (ι ∘ u) hu (ι y) (fun j => by
    rw [Function.comp_apply, hι, hy j, Rat.cast_zero])
  by_contra hne
  have hp := hpos y hne
  have h2 : ((Algebra.trace ℚ K (h y y) : ℚ) : ℝ) = 0 := by rw [← hι, h0, inner_zero_left]
  have h3 : Algebra.trace ℚ K (h y y) = 0 := by exact_mod_cast h2
  rw [h3] at hp
  exact lt_irrefl _ hp

private theorem addHom_ratCast_smul_lemma_3 {K V : Type*} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n)) (q : ℚ) (x : V) :
    ι ((q : K) • x) = (q : ℝ) • ι x := by
  exact map_ratCast_smul ι K ℝ q x

theorem classSetAssembly_qindep {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (g : Fin n → ℚ)
    (hg : ∑ i, (g i : K) • u i = 0) : g = 0 := by
  have hsum : ∑ i, ((g i : ℚ) : ℝ) • (ι ∘ u) i = 0 := by
    have e := congrArg ι hg
    rw [map_sum, map_zero] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Function.comp_apply, addHom_ratCast_smul_lemma_3 ι (g i) (u i)]
  funext i
  have := Fintype.linearIndependent_iff.mp hu (fun i => ((g i : ℚ) : ℝ)) hsum i
  simpa using this

theorem classSetAssembly_coord_zero {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (r : Fin n → ℚ)
    (hr : ∀ j, ∑ i, r i * Algebra.trace ℚ K (h (u i) (u j)) = 0) : r = 0 := by
  have hty : ∀ j, Algebra.trace ℚ K (h (∑ i, (r i : K) • u i) (u j)) = 0 := by
    intro j
    rw [classSetAssembly_tr_sum_left, ← hr j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [classSetAssembly_tr_qsmul_left]
  have h0 : ∑ i, (r i : K) • u i = 0 := classSetAssembly_nondeg h hpos ι hι u hu _ hty
  exact classSetAssembly_qindep (K := K) ι u hu r h0

theorem classSetAssembly_span {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (x : V) :
    ∃ t : Fin n → ℚ, x = ∑ i, (t i : K) • u i := by
  classical
  let L : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) :=
    { toFun := fun r j => ∑ i, r i * Algebra.trace ℚ K (h (u i) (u j))
      map_add' := fun a b => by funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by funext j; simp [Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro r hr0
    exact classSetAssembly_coord_zero h hpos ι hι u hu r (fun j => congrFun hr0 j)
  obtain ⟨t, ht⟩ := (LinearMap.injective_iff_surjective.mp hinj)
    (fun j => Algebra.trace ℚ K (h x (u j)))
  refine ⟨t, ?_⟩
  have hz : x - ∑ i, (t i : K) • u i = 0 := by
    apply classSetAssembly_nondeg h hpos ι hι u hu
    intro j
    have e : ∑ i, t i * Algebra.trace ℚ K (h (u i) (u j)) = Algebra.trace ℚ K (h x (u j)) :=
      congrFun ht j
    rw [classSetAssembly_tr_sub_left, classSetAssembly_tr_sum_left, ← e, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [classSetAssembly_tr_qsmul_left]
  exact sub_eq_zero.mp hz

theorem classSetAssembly_denom {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (d : ℕ) (hd : 0 < d)
    (hint : ∀ i j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = z) :
    ∃ e : ℤ, e ≠ 0 ∧ ∀ x : V, (∀ j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x (u j)) = z) →
      e • x ∈ AddSubgroup.closure (Set.range u) := by
  obtain ⟨M, hM⟩ : ∃ M : Fin n → Fin n → ℤ,
      ∀ i j, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = M i j := by
    choose M hM using ‹∀ i j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = z›
    exact ⟨M, hM⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin n) (Fin n) ℚ,
      A = (Int.castRingHom ℚ).mapMatrix (Matrix.of M) := ⟨_, rfl⟩
  have hA : ∀ i j, A i j = (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) := fun i j => by
    rw [hAdef, hM i j]
    simp
  have hdetA : A.det = (((Matrix.of M).det : ℤ) : ℚ) := by
    rw [hAdef, ← RingHom.map_det]
    simp
  have hadj : A.adjugate = (Int.castRingHom ℚ).mapMatrix (Matrix.of M).adjugate := by
    rw [hAdef, RingHom.map_adjugate]
  have hdet : (Matrix.of M).det ≠ 0 := by
    intro h0
    have hA0 : A.det = 0 := by rw [hdetA, h0, Int.cast_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hA0
    have hr := classSetAssembly_coord_zero h hpos ι hι u hu (fun i => (d : ℚ) * v i)
      (fun j => by
        have e := congrFun hv j
        simp only [Matrix.vecMul, dotProduct, hA, Pi.zero_apply] at e
        rw [← e]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring)
    apply hv0
    funext i
    have e := congrFun hr i
    simp only [Pi.zero_apply] at e
    exact (mul_eq_zero.mp e).resolve_left (by exact_mod_cast hd.ne')
  refine ⟨(Matrix.of M).det, hdet, fun x hx => ?_⟩
  choose w hw using hx
  obtain ⟨t, ht⟩ := classSetAssembly_span h hpos ι hι u hu x
  have hvec : Matrix.vecMul t A = fun j => ((w j : ℤ) : ℚ) := by
    funext j
    rw [← hw j, ht, classSetAssembly_tr_sum_left, Finset.mul_sum]
    simp only [Matrix.vecMul, dotProduct, hA]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [classSetAssembly_tr_qsmul_left]
    ring
  have hkey : A.det • t = Matrix.vecMul (fun j => ((w j : ℤ) : ℚ)) A.adjugate := by
    rw [← hvec, Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul,
      Matrix.vecMul_one]
  set z : Fin n → ℤ := Matrix.vecMul w (Matrix.of M).adjugate with hzdef
  have hz : ∀ i, ((z i : ℤ) : ℚ) = (((Matrix.of M).det : ℤ) : ℚ) * t i := by
    intro i
    have e := congrFun hkey i
    rw [Pi.smul_apply, smul_eq_mul, hdetA, hadj] at e
    rw [e, hzdef]
    simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]
    push_cast
    rfl
  have hx' : (Matrix.of M).det • x = ∑ i, z i • u i := by
    rw [ht, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K, smul_smul]
    congr 1
    have e := congrArg (fun q : ℚ => (q : K)) (hz i)
    simp only [Rat.cast_mul, Rat.cast_intCast] at e
    exact e.symm
  rw [hx']
  exact sum_mem fun i _ => zsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self i)) _

end Real

section Finite

theorem classSetAssembly_finite_rat (d : ℕ) (hd : 0 < d) (R : ℝ) :
    {q : ℚ | (∃ z : ℤ, (d : ℚ) * q = z) ∧ |(q : ℝ)| ≤ R}.Finite := by
  set N : ℤ := ⌈(d : ℝ) * R⌉
  refine ((Set.finite_Icc (-N) N).image (fun z : ℤ => (z : ℚ) / d)).subset ?_
  rintro q ⟨⟨z, hz⟩, hq⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hzR : ((z : ℚ) : ℝ) = (d : ℝ) * (q : ℝ) := by
    rw [← hz, Rat.cast_mul, Rat.cast_natCast]
  have hzR' : (z : ℝ) = (d : ℝ) * (q : ℝ) := by exact_mod_cast hzR
  have habs : |(z : ℝ)| ≤ (d : ℝ) * R := by
    rw [hzR', abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ d)]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  have hN : (d : ℝ) * R ≤ (N : ℝ) := Int.le_ceil _
  have h1 : (z : ℝ) ≤ N := le_trans (le_abs_self _) (habs.trans hN)
  have h2 : -(N : ℝ) ≤ z := by
    have := neg_abs_le (z : ℝ)
    linarith
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · have h3 : ((-N : ℤ) : ℝ) ≤ (z : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  · exact_mod_cast h1
  · show (z : ℚ) / d = q
    rw [← hz]
    field_simp

variable {V : Type*} [AddCommGroup V]

theorem classSetAssembly_torsion {K : Type*} [Field K] [CharZero K] [Module K V] {n : ℕ} (u : Fin n → V)
    (e : ℤ) (he : e ≠ 0) :
    AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) ≤
      (AddSubgroup.closure (Set.range u)).comap (zsmulAddGroupHom e) := by
  have heK : (e : K) ≠ 0 := Int.cast_ne_zero.mpr he
  rw [AddSubgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  have hx : (zsmulAddGroupHom e : V →+ V) (((e : K)⁻¹) • u i) = u i := by
    show e • (((e : K)⁻¹) • u i) = u i
    rw [← Int.cast_smul_eq_zsmul K, smul_smul, mul_inv_cancel₀ heK, one_smul]
  rw [hx]
  exact AddSubgroup.subset_closure ⟨i, rfl⟩

theorem classSetAssembly_le_Q {K : Type*} [Field K] [CharZero K] [Module K V] {n : ℕ} (u : Fin n → V)
    (e : ℤ) (he : e ≠ 0) (x : V) (hx : e • x ∈ AddSubgroup.closure (Set.range u)) :
    x ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) := by
  have heK : (e : K) ≠ 0 := Int.cast_ne_zero.mpr he
  let f : V →+ V :=
    { toFun := fun v => ((e : K)⁻¹) • v
      map_zero' := smul_zero _
      map_add' := fun a b => smul_add _ a b }
  have hfx : f (e • x) = x := by
    show ((e : K)⁻¹) • (e • x) = x
    rw [← Int.cast_smul_eq_zsmul K, smul_smul, inv_mul_cancel₀ heK, one_smul]
  have hle : AddSubgroup.closure (Set.range u) ≤
      (AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i)).comap f := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    have hm : ((e : K)⁻¹) • u i ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) :=
      AddSubgroup.subset_closure ⟨i, rfl⟩
    exact hm
  have h1 := hle hx
  rw [AddSubgroup.mem_comap, hfx] at h1
  exact h1

theorem closure_range_le_closure_range_inv_smul {K : Type*} [Field K] [CharZero K] [Module K V] {n : ℕ} (u : Fin n → V)
    (e : ℤ) (he : e ≠ 0) :
    AddSubgroup.closure (Set.range u) ≤
      AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) := by
  have heK : (e : K) ≠ 0 := Int.cast_ne_zero.mpr he
  rw [AddSubgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have hx : u i = e • (((e : K)⁻¹) • u i) := by
    rw [← Int.cast_smul_eq_zsmul K, smul_smul, mul_inv_cancel₀ heK, one_smul]
  have hm : ((e : K)⁻¹) • u i ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) :=
    AddSubgroup.subset_closure ⟨i, rfl⟩
  rw [SetLike.mem_coe, hx]
  exact AddSubgroup.zsmul_mem _ hm e

private theorem exists_coeffs_of_mem_closure_lemma_4 {W : Type*} [AddCommGroup W] {n : ℕ} (g : Fin n → W)
    (q : W) (hq : q ∈ AddSubgroup.closure (Set.range g)) :
    ∃ c : Fin n → ℤ, ∑ i, c i • g i = q := by
  classical
  let S : AddSubgroup W :=
    { carrier := {q | ∃ c : Fin n → ℤ, ∑ i, c i • g i = q}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, by simp [neg_smul, Finset.sum_neg_distrib]⟩ }
  have hle : AddSubgroup.closure (Set.range g) ≤ S := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨Pi.single j 1, by simp [Pi.single_apply]⟩
  exact hle hq

theorem classSetAssembly_finite_between (hE : FinIntermediate) {K W : Type} [Field K] [CharZero K]
    [AddCommGroup W] [Module K W] {n : ℕ} (u : Fin n → W) (e : ℤ) (he : e ≠ 0) :
    {M : AddSubgroup W | AddSubgroup.closure (Set.range u) ≤ M ∧
      M ≤ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i)}.Finite := by
  classical
  unfold FinIntermediate at hE
  have hPQ := closure_range_le_closure_range_inv_smul (K := K) u e he
  have hkill : ∀ q ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i),
      e • q ∈ AddSubgroup.closure (Set.range u) :=
    fun q hq => classSetAssembly_torsion (K := K) u e he hq
  refine hE W _ _ hPQ ?_
  set P := AddSubgroup.closure (Set.range u) with hP
  set Q := AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) with hQ
  have hgQ : ∀ i, ((e : K)⁻¹) • u i ∈ Q := fun i => AddSubgroup.subset_closure ⟨i, rfl⟩
  let F : (Fin n → ℤ) → Q ⧸ P.addSubgroupOf Q := fun k =>
    QuotientAddGroup.mk ⟨∑ i, k i • (((e : K)⁻¹) • u i),
      Q.sum_mem fun i _ => Q.zsmul_mem (hgQ i) (k i)⟩
  have hsurj : (Set.univ : Set (Q ⧸ P.addSubgroupOf Q)) ⊆
      F '' (Set.univ.pi fun _ => Set.Ico (0 : ℤ) (e.natAbs : ℤ)) := by
    intro z _
    obtain ⟨⟨q, hq⟩, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨c, hc⟩ := exists_coeffs_of_mem_closure_lemma_4 (fun i => ((e : K)⁻¹) • u i) q hq
    refine ⟨fun i => c i % e, ?_, ?_⟩
    · intro i _
      exact Set.mem_Ico.mpr ⟨Int.emod_nonneg _ he, Int.emod_lt _ he⟩
    · apply QuotientAddGroup.eq.mpr
      rw [AddSubgroup.mem_addSubgroupOf]
      show -(∑ i, (c i % e) • (((e : K)⁻¹) • u i)) + q ∈ P
      have hsum : -(∑ i, (c i % e) • (((e : K)⁻¹) • u i)) + q =
          ∑ i, (c i / e) • (e • (((e : K)⁻¹) • u i)) := by
        rw [← hc, neg_add_eq_sub, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← sub_smul]
        congr 1
        have key : c i % e + e * (c i / e) = c i := by
          first
          | exact Int.emod_add_ediv (c i) e
          | (have := Int.ediv_add_emod (c i) e; linarith)
          | (rw [Int.emod_def]; ring)
        linarith
      rw [hsum]
      exact P.sum_mem fun i _ => P.zsmul_mem (hkill _ (hgQ i)) _
  have hfin : (Set.univ : Set (Q ⧸ P.addSubgroupOf Q)).Finite :=
    ((Set.Finite.pi fun _ => Set.finite_Ico _ _).image F).subset hsurj
  exact Set.finite_univ_iff.mp hfin

end Finite

section Isom

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

private theorem eq_of_trace_apply_eq_lemma_5 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (w : Fin n → V) (hw : LinearIndependent ℝ (ι ∘ w)) (y y' : V)
    (hyy : ∀ l, Algebra.trace ℚ K (h y (w l)) = Algebra.trace ℚ K (h y' (w l))) : y = y' := by
  have hz : y - y' = 0 := classSetAssembly_nondeg h hpos ι hι w hw _ (fun l => by
    rw [classSetAssembly_tr_sub_left, hyy l, sub_self])
  exact sub_eq_zero.mp hz

private theorem trace_sum_coeffs_lemma_6 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (t : Fin n → ℚ)
    (w : Fin n → V) (z : V) :
    Algebra.trace ℚ K (h (∑ i, (t i : K) • w i) z) =
      ∑ i, t i * Algebra.trace ℚ K (h (w i) z) := by
  rw [classSetAssembly_tr_sum_left]
  exact Finset.sum_congr rfl fun i _ => classSetAssembly_tr_qsmul_left h _ _ _

private theorem trace_smul_sum_coeffs_lemma_7 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (a : K) (t : Fin n → ℚ)
    (w : Fin n → V) (z : V) :
    Algebra.trace ℚ K (h (a • ∑ i, (t i : K) • w i) z) =
      ∑ i, t i * Algebra.trace ℚ K (h (a • w i) z) := by
  rw [Finset.smul_sum, classSetAssembly_tr_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm a, ← smul_smul, classSetAssembly_tr_qsmul_left]

private theorem trace_smul_left_basis_lemma_8 {κ : Type*} [Fintype κ] (ω : Basis κ ℚ K)
    (h : V →ₗ⋆[K] V →ₗ[K] K) (a : K) (y z : V) :
    Algebra.trace ℚ K (h (a • y) z) =
      ∑ k, ω.repr a k * Algebra.trace ℚ K (h (ω k • y) z) := by
  have ha : a = ∑ k, ((ω.repr a k : ℚ) : K) * ω k := by
    conv_lhs => rw [← ω.sum_repr a]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, eq_ratCast]
  conv_lhs => rw [ha]
  rw [Finset.sum_smul, classSetAssembly_tr_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul, classSetAssembly_tr_qsmul_left]

private theorem exists_linearMap_of_gram_lemma_9 {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    {κ : Type*} [Fintype κ] (ω : Basis κ ℚ K)
    (u u' : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (hu' : LinearIndependent ℝ (ι ∘ u'))
    (hG : ∀ i l, Algebra.trace ℚ K (h (u i) (u l)) = Algebra.trace ℚ K (h (u' i) (u' l)))
    (hA : ∀ k i l, Algebra.trace ℚ K (h (ω k • u i) (u l)) =
      Algebra.trace ℚ K (h (ω k • u' i) (u' l))) :
    ∃ φ : V →ₗ[K] V, ∀ x l,
      Algebra.trace ℚ K (h (φ x) (u' l)) = Algebra.trace ℚ K (h x (u l)) := by
  choose t ht using classSetAssembly_span h hpos ι hι u hu
  have hP : ∀ x l, Algebra.trace ℚ K (h (∑ i, (t x i : K) • u' i) (u' l)) =
      Algebra.trace ℚ K (h x (u l)) := by
    intro x l
    conv_rhs => rw [ht x]
    rw [trace_sum_coeffs_lemma_6, trace_sum_coeffs_lemma_6]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hG i l]
  have hQ : ∀ (k : κ) x l, Algebra.trace ℚ K (h (ω k • ∑ i, (t x i : K) • u' i) (u' l)) =
      Algebra.trace ℚ K (h (ω k • x) (u l)) := by
    intro k x l
    conv_rhs => rw [ht x]
    rw [trace_smul_sum_coeffs_lemma_7, trace_smul_sum_coeffs_lemma_7]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA k i l]
  obtain ⟨f, hf⟩ : ∃ f : V → V, ∀ x l,
      Algebra.trace ℚ K (h (f x) (u' l)) = Algebra.trace ℚ K (h x (u l)) ∧
      ∀ k, Algebra.trace ℚ K (h (ω k • f x) (u' l)) = Algebra.trace ℚ K (h (ω k • x) (u l)) :=
    ⟨fun x => ∑ i, (t x i : K) • u' i, fun x l => ⟨hP x l, fun k => hQ k x l⟩⟩
  refine ⟨{ toFun := f
            map_add' := fun x y => eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by
              rw [classSetAssembly_tr_add_left, (hf (x + y) l).1, (hf x l).1, (hf y l).1,
                classSetAssembly_tr_add_left])
            map_smul' := fun a x => eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by
              rw [(hf (a • x) l).1]
              try rw [RingHom.id_apply]
              rw [trace_smul_left_basis_lemma_8 ω h a x (u l), trace_smul_left_basis_lemma_8 ω h a (f x) (u' l)]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [(hf x l).2 k]) }, fun x l => (hf x l).1⟩

theorem classSetAssembly_exists_isom {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    {κ : Type*} [Fintype κ] (ω : Basis κ ℚ K)
    (u u' : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (hu' : LinearIndependent ℝ (ι ∘ u'))
    (hG : ∀ i l, Algebra.trace ℚ K (h (u i) (u l)) = Algebra.trace ℚ K (h (u' i) (u' l)))
    (hA : ∀ k i l, Algebra.trace ℚ K (h (ω k • u i) (u l)) =
      Algebra.trace ℚ K (h (ω k • u' i) (u' l))) :
    ∃ φ : V ≃ₗ[K] V, (∀ x y, Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)) ∧
      ∀ i, φ (u i) = u' i := by
  obtain ⟨φ, hφ⟩ := exists_linearMap_of_gram_lemma_9 h hpos ι hι ω u u' hu hu' hG hA
  obtain ⟨ψ, hψ⟩ := exists_linearMap_of_gram_lemma_9 h hpos ι hι ω u' u hu' hu
    (fun i l => (hG i l).symm) (fun k i l => (hA k i l).symm)
  have h1 : ∀ y, φ (ψ y) = y := fun y =>
    eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by rw [hφ, hψ])
  have h2 : ∀ x, ψ (φ x) = x := fun x =>
    eq_of_trace_apply_eq_lemma_5 h hpos ι hι u hu _ _ (fun l => by rw [hψ, hφ])
  have hφu : ∀ i, φ (u i) = u' i := fun i =>
    eq_of_trace_apply_eq_lemma_5 h hpos ι hι u' hu' _ _ (fun l => by rw [hφ, hG i l])
  refine ⟨LinearEquiv.ofLinear φ ψ (LinearMap.ext h1) (LinearMap.ext h2), ?_, hφu⟩
  intro x y
  show Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)
  obtain ⟨s, hs⟩ := classSetAssembly_span h hpos ι hι u hu y
  have hφy : φ y = ∑ j, (s j : K) • u' j := by
    rw [hs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hφu j]
  rw [hφy, hs, classSetAssembly_tr_sum_right, classSetAssembly_tr_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [classSetAssembly_tr_qsmul_right, classSetAssembly_tr_qsmul_right, hφ]

end Isom

section Main

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

theorem classSetAssembly_mem_zmap {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n))
    (M : Submodule (NumberField.RingOfIntegers K) V) (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ zmap ι M ↔ ∃ x ∈ M, ι x = v := by
  exact Iff.rfl

theorem classSetAssembly_min {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (d : ℕ) (hd : 0 < d) (M : Submodule (NumberField.RingOfIntegers K) V)
    (hdM : ∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (x : V) (hx : x ∈ M) (hx0 : x ≠ 0) : 1 / (d : ℝ) ≤ ‖ι x‖ := by
  obtain ⟨z, hz⟩ := classSetAssembly_dint h d x x (hdM x hx x hx)
  have hp := hpos x hx0
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hz0 : (0 : ℤ) < z := by
    have : (0 : ℚ) < z := by rw [← hz]; exact mul_pos hdQ hp
    exact_mod_cast this
  have hz1 : (1 : ℝ) ≤ z := by
    have : (1 : ℤ) ≤ z := by omega
    exact_mod_cast this
  have hn : ‖ι x‖ ^ 2 = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, hι]
  have hzR : (d : ℝ) * ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = (z : ℝ) := by
    exact_mod_cast hz
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdR1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN := norm_nonneg (ι x)
  have key : 1 ≤ (‖ι x‖ * d) ^ 2 := by
    have e : (‖ι x‖ * d) ^ 2 = (z : ℝ) * d := by
      rw [mul_pow, hn, ← hzR]; ring
    rw [e]
    nlinarith
  have hNd : 0 ≤ ‖ι x‖ * d := mul_nonneg hN hdR.le
  rw [div_le_iff₀ hdR]
  nlinarith

theorem classSetAssembly_w_mem (o : Option (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K))) :
    ∃ r : NumberField.RingOfIntegers K,
      o.elim (1 : K) (NumberField.integralBasis K) = algebraMap _ K r := by
  cases o with
  | none => exact ⟨1, (map_one _).symm⟩
  | some i =>
    exact ⟨_, NumberField.integralBasis_apply K i⟩

theorem classSetAssembly_main (hE : FinIntermediate) (hF : IsomOfTrace)
    (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (hmul : ∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖)
    (d : ℕ) (hd : 0 < d) (S : Set (Submodule (NumberField.RingOfIntegers K) V))
    (hdM : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (B : ℝ)
    (hgood : ∀ M ∈ S, ∃ u : Fin n → V, (∀ i, u i ∈ M) ∧ LinearIndependent ℝ (ι ∘ u) ∧
      ∀ i, ‖ι (u i)‖ ≤ B) :
    ∃ s : Finset (Submodule (NumberField.RingOfIntegers K) V), (∀ M ∈ s, M ∈ S) ∧
      ∀ M ∈ S, ∃ N ∈ s, ∃ g ∈ isom h, gmap g N = M := by
  classical
  unfold IsomOfTrace at hF
  choose! u humem huli hubd using hgood
  have hωmem : ∀ M : Submodule (NumberField.RingOfIntegers K) V, ∀ k x, x ∈ M →
      NumberField.integralBasis K k • x ∈ M := by
    intro M k x hx
    obtain ⟨r, hr⟩ := classSetAssembly_w_mem (K := K) (some k)
    have hr' : NumberField.integralBasis K k = algebraMap (NumberField.RingOfIntegers K) K r := hr
    rw [hr', algebraMap_smul]
    exact M.smul_mem r hx
  obtain ⟨C, hC⟩ : ∃ C : Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → ℝ,
      ∀ k x, ‖ι (NumberField.integralBasis K k • x)‖ ≤ C k * ‖ι x‖ :=
    ⟨fun k => (hmul (NumberField.integralBasis K k)).choose,
      fun k => (hmul (NumberField.integralBasis K k)).choose_spec⟩
  obtain ⟨R, hR1, hR2⟩ : ∃ R : ℝ, B * B ≤ R ∧ ∀ k, |C k| * B * B ≤ R := by
    have hs : 0 ≤ ∑ k, |C k| := Finset.sum_nonneg fun k _ => abs_nonneg (C k)
    refine ⟨B * B * (1 + ∑ k, |C k|), ?_, fun k => ?_⟩
    · exact le_mul_of_one_le_right (mul_self_nonneg B) (by linarith)
    · have hk : |C k| ≤ 1 + ∑ k, |C k| := by
        have := Finset.single_le_sum (fun k _ => abs_nonneg (C k)) (Finset.mem_univ k)
        linarith
      calc |C k| * B * B = B * B * |C k| := by ring
        _ ≤ B * B * (1 + ∑ k, |C k|) := mul_le_mul_of_nonneg_left hk (mul_self_nonneg B)
  have hT := classSetAssembly_finite_rat d hd R
  have hbound : ∀ M ∈ S, ∀ x y : V, x ∈ M → y ∈ M → ∀ c : ℝ, ‖ι x‖ ≤ c → ‖ι y‖ ≤ B →
      c * B ≤ R → Algebra.trace ℚ K (h x y) ∈
        {q : ℚ | (∃ z : ℤ, (d : ℚ) * q = z) ∧ |(q : ℝ)| ≤ R} := by
    intro M hM x y hx hy c hc hyB hcR
    refine ⟨classSetAssembly_dint h d x y (hdM M hM x hx y hy), ?_⟩
    rw [← hι]
    calc |inner ℝ (ι x) (ι y)| ≤ ‖ι x‖ * ‖ι y‖ := abs_real_inner_le_norm _ _
      _ ≤ c * B := mul_le_mul hc hyB (norm_nonneg _) ((norm_nonneg _).trans hc)
      _ ≤ R := hcR
  obtain ⟨D, hD⟩ : ∃ D : Submodule (NumberField.RingOfIntegers K) V →
      (Fin n → Fin n → ℚ) × (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → Fin n → Fin n → ℚ),
      ∀ M, D M = (fun i l => Algebra.trace ℚ K (h (u M i) (u M l)),
        fun k i l => Algebra.trace ℚ K (h (NumberField.integralBasis K k • u M i) (u M l))) :=
    ⟨_, fun _ => rfl⟩
  have hDfin : (D '' S).Finite := by
    refine ((Set.Finite.pi fun i => Set.Finite.pi fun l => hT).prod
      (Set.Finite.pi fun k => Set.Finite.pi fun i => Set.Finite.pi fun l => hT)).subset ?_
    rintro _ ⟨M, hM, rfl⟩
    rw [hD]
    refine Set.mem_prod.mpr ⟨Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun l => ?_,
      Set.mem_univ_pi.mpr fun k => Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun l => ?_⟩
    · exact hbound M hM _ _ (humem M hM i) (humem M hM l) B (hubd M hM i) (hubd M hM l) hR1
    · refine hbound M hM _ _ (hωmem M k _ (humem M hM i)) (humem M hM l) (|C k| * B) ?_
        (hubd M hM l) (hR2 k)
      exact (hC k _).trans (mul_le_mul (le_abs_self _) (hubd M hM i) (norm_nonneg _) (abs_nonneg _))
  have hEprop : ∀ M ∈ S, ∃ e : ℤ, e ≠ 0 ∧ ∀ x : V,
      (∀ j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x (u M j)) = z) →
      x ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u M i) := by
    intro M hM
    obtain ⟨e, he, hx⟩ := classSetAssembly_denom h hpos ι hι (u M) (huli M hM) d hd
      (fun i j => classSetAssembly_dint h d (u M i) (u M j)
        (hdM M hM _ (humem M hM i) _ (humem M hM j)))
    exact ⟨e, he, fun x hxj => classSetAssembly_le_Q (K := K) (u M) e he x (hx x hxj)⟩
  choose! e he hemem using hEprop
  have hφex : ∀ M : Submodule (NumberField.RingOfIntegers K) V, ∃ φ : V ≃ₗ[K] V, M ∈ S →
      (∀ x y, Algebra.trace ℚ K (h (φ x) (φ y)) = Algebra.trace ℚ K (h x y)) ∧
      ∀ i, φ (u (Function.invFunOn D S (D M)) i) = u M i := by
    intro M
    by_cases hM : M ∈ S
    · obtain ⟨hRS, hRD⟩ : Function.invFunOn D S (D M) ∈ S ∧
          D (Function.invFunOn D S (D M)) = D M := Function.invFunOn_pos ⟨M, hM, rfl⟩
      generalize Function.invFunOn D S (D M) = M₀ at hRS hRD ⊢
      have h1 := congrArg Prod.fst hRD
      have h2 := congrArg Prod.snd hRD
      rw [hD M₀, hD M] at h1 h2
      obtain ⟨φ, h3, h4⟩ := classSetAssembly_exists_isom h hpos ι hι
        (NumberField.integralBasis K) (u M₀) (u M) (huli M₀ hRS) (huli M hM)
        (fun i l => congrFun (congrFun h1 i) l)
        (fun k i l => congrFun (congrFun (congrFun h2 k) i) l)
      exact ⟨φ, fun _ => ⟨h3, h4⟩⟩
    · exact ⟨LinearEquiv.refl K V, fun h' => absurd h' hM⟩
  choose φ hφ using hφex
  obtain ⟨Key, hKey⟩ : ∃ Key : Submodule (NumberField.RingOfIntegers K) V →
      ((Fin n → Fin n → ℚ) × (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) → Fin n → Fin n → ℚ)) ×
        AddSubgroup V,
      ∀ M, Key M = (D M, M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom) :=
    ⟨_, fun _ => rfl⟩
  have hKfin : (Key '' S).Finite := by
    refine (Set.Finite.biUnion hDfin fun δ hδ =>
      ((classSetAssembly_finite_between (K := K) hE (u (Function.invFunOn D S δ))
        (e (Function.invFunOn D S δ)) (he _ (Function.invFunOn_pos hδ).1)).image
          (Prod.mk δ))).subset ?_
    rintro _ ⟨M, hM, rfl⟩
    rw [Set.mem_iUnion₂]
    refine ⟨D M, ⟨M, hM, rfl⟩, ?_⟩
    rw [hKey]
    have hRS : Function.invFunOn D S (D M) ∈ S := (Function.invFunOn_pos ⟨M, hM, rfl⟩).1
    refine ⟨_, ⟨?_, ?_⟩, rfl⟩
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show φ M (u (Function.invFunOn D S (D M)) i) ∈ M
      rw [(hφ M hM).2 i]
      exact humem M hM i
    · intro x hx
      have hx' : φ M x ∈ M := hx
      refine hemem _ hRS x (fun j => ?_)
      rw [← (hφ M hM).1 x, (hφ M hM).2 j]
      exact classSetAssembly_dint h d _ _ (hdM M hM _ hx' _ (humem M hM j))
  refine ⟨hKfin.toFinset.image (Function.invFunOn Key S), ?_, ?_⟩
  · intro N hN
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hN
    exact (Function.invFunOn_pos (hKfin.mem_toFinset.mp hy)).1
  · intro M hM
    have hy : Key M ∈ Key '' S := ⟨M, hM, rfl⟩
    obtain ⟨hNS, hNK⟩ := Function.invFunOn_pos hy
    refine ⟨Function.invFunOn Key S (Key M),
      Finset.mem_image.mpr ⟨Key M, hKfin.mem_toFinset.mpr hy, rfl⟩, ?_⟩
    generalize Function.invFunOn Key S (Key M) = N at hNS hNK ⊢
    rw [hKey N, hKey M] at hNK
    have hCN : N.toAddSubgroup.comap (φ N).toLinearMap.toAddMonoidHom =
        M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom := congrArg Prod.snd hNK
    refine ⟨(φ N).symm.trans (φ M), ?_, ?_⟩
    · apply hF K V h
      intro x y
      show Algebra.trace ℚ K (h (φ M ((φ N).symm x)) (φ M ((φ N).symm y))) =
        Algebra.trace ℚ K (h x y)
      rw [(hφ M hM).1]
      have h5 := (hφ N hNS).1 ((φ N).symm x) ((φ N).symm y)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h5
      exact h5.symm
    · ext x
      rw [isomAct_mem_gmap]
      have hc : (φ M).symm x ∈ N.toAddSubgroup.comap (φ N).toLinearMap.toAddMonoidHom ↔
          (φ M).symm x ∈ M.toAddSubgroup.comap (φ M).toLinearMap.toAddMonoidHom := by
        rw [hCN]
      change φ N ((φ M).symm x) ∈ N ↔ φ M ((φ M).symm x) ∈ M at hc
      rw [LinearEquiv.apply_symm_apply] at hc
      exact hc

end Main

theorem classSetFinite_core (hC : ShortVectors) (hE : FinIntermediate) (hF : IsomOfTrace)
    {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (n : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (hmul : ∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖)
    (d : ℕ) (hd : 0 < d) (C : ℝ) (S : Set (Submodule (NumberField.RingOfIntegers K) V))
    (hSd : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (hSlat : ∀ M ∈ S, ∃ _ : DiscreteTopology (zmap ι M), IsZLattice ℝ (zmap ι M))
    (hSC : ∀ M ∈ S, ∀ [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)],
      ZLattice.covolume (zmap ι M) ≤ C) :
    ∃ s : Finset (Submodule (NumberField.RingOfIntegers K) V), (∀ N ∈ s, N ∈ S) ∧
      ∀ M ∈ S, ∃ N ∈ s, ∃ g ∈ isom h, gmap g N = M := by
  unfold ShortVectors at hC
  have hdR : (0 : ℝ) < 1 / (d : ℝ) := one_div_pos.mpr (by exact_mod_cast hd)
  obtain ⟨B, hB⟩ := hC n (1 / (d : ℝ)) C hdR
  refine classSetAssembly_main hE hF h hpos ι hι hmul d hd S hSd B ?_
  intro M hM
  obtain ⟨hdisc, hlat⟩ := hSlat M hM
  have := hdisc
  have := hlat
  obtain ⟨v, hvmem, hvli, hvB⟩ := hB (zmap ι M) (fun w hw hw0 => by
      obtain ⟨x, hx, rfl⟩ := (classSetAssembly_mem_zmap ι M w).mp hw
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hw0 (map_zero ι)
      exact classSetAssembly_min h hpos ι hι d hd M (hSd M hM) x hx hx0)
    (hSC M hM)
  choose x hx using fun i => (classSetAssembly_mem_zmap ι M (v i)).mp (hvmem i)
  have hxv : ι ∘ x = v := funext fun i => (hx i).2
  refine ⟨x, fun i => (hx i).1, ?_, fun i => ?_⟩
  · rw [hxv]
    exact hvli
  · rw [(hx i).2]
    exact hvB i

theorem classSetFinite_of (hA : TraceReal) (hB : GenusCovolBound) (hC : ShortVectors)
    (hD : GenusScale) (hE : FinIntermediate) (hF : IsomOfTrace) : ClassSetFinite := by
  unfold ClassSetFinite
  unfold TraceReal at hA
  unfold GenusCovolBound at hB
  unfold GenusScale at hD
  intro K V _ _ _ _ _ _ _ _ h hsymm hpos L hL
  obtain ⟨N, ι, hι, hmul, hlat⟩ := hA K V h hsymm hpos
  obtain ⟨C, hCb⟩ := hB K V h hsymm hpos N ι hι L hL
  obtain ⟨d, hd, hdM⟩ := hD K V h hsymm L hL
  exact classSetFinite_core hC hE hF h hpos N ι hι hmul d hd C
    (genus h L) hdM (fun M hM => hlat M hM.1) hCb

end Formalism.HermitianLatticesTheory
