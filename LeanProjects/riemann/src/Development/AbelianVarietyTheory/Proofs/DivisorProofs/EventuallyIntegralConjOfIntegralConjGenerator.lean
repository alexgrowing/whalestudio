import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutantOfMaximalDegreeElement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.ConjInt

section Coords

variable (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type} (b : Module.Basis κ ℚ M)

theorem isIntB_add {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y) :
    IsIntB v b (x + y) := fun i => by
  rw [map_add, Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_smul {a : v.adicCompletion ℚ} (ha : a ∈ v.adicCompletionIntegers ℚ)
    {x : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) : IsIntB v b (a • x) := fun i => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem ha (hx i)

theorem isIntB_sum {ι : Type} (s : Finset ι) (f : ι → v.adicCompletion ℚ ⊗[ℚ] M)
    (h : ∀ i ∈ s, IsIntB v b (f i)) : IsIntB v b (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isIntB_zero v b
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isIntB_add v b (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isIntB_tmul_iff (c : M) : IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) ↔
    ∀ i, algebraMap ℚ (v.adicCompletion ℚ) (b.repr c i) ∈ v.adicCompletionIntegers ℚ := by
  unfold IsIntB
  simp only [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

theorem eventually_isIntB_tmul [Finite κ] (c : M) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) := by
  have h : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ i,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr c i) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i => (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (b.repr c i)).2
  exact h.mono fun v hv => (isIntB_tmul_iff v b c).2 hv

theorem eq_sum_basis [Fintype κ] (x : v.adicCompletion ℚ ⊗[ℚ] M) :
    x = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr x i •
      ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b i) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr x]
  simp only [Algebra.TensorProduct.basis_apply]

end Coords

section Alg

variable (v : HeightOneSpectrum ℤ) {A : Type} [Ring A] [Algebra ℚ A] {κ : Type} (b : Module.Basis κ ℚ A)

theorem isIntB_mul [Finite κ] (hb : ∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j)))
    {x y : v.adicCompletion ℚ ⊗[ℚ] A} (hx : IsIntB v b x) (hy : IsIntB v b y) : IsIntB v b (x * y) := by
  haveI := Fintype.ofFinite κ
  rw [eq_sum_basis v b x, eq_sum_basis v b y, Finset.sum_mul]
  refine isIntB_sum v b _ _ fun i _ => ?_
  rw [Finset.mul_sum]
  refine isIntB_sum v b _ _ fun j _ => ?_
  rw [smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact isIntB_smul v b (mul_mem (hx i) (hy j)) (hb i j)

theorem isIntB_pow [Finite κ] (hb : ∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j)))
    (h1 : IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (1 : A)))
    {x : v.adicCompletion ℚ ⊗[ℚ] A} (hx : IsIntB v b x) (k : ℕ) : IsIntB v b (x ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact h1
  | succ k ih => rw [pow_succ]; exact isIntB_mul v b hb ih hx

theorem tmul_central_comm {R : Type} [CommRing R] [Algebra ℚ R] (z : A) (hz : ∀ c, z * c = c * z)
    (y : R ⊗[ℚ] A) : ((1 : R) ⊗ₜ[ℚ] z) * y = y * ((1 : R) ⊗ₜ[ℚ] z) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => simp [Algebra.TensorProduct.tmul_mul_tmul, hz c]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

end Alg

end GlobalTheory.ConjInt

namespace GlobalTheory.ConjInt

variable {p : ℕ} [Fact p.Prime]

theorem mem_adjoin_of_centralizer (G : HTGroup p) (γ : G.C) (hdeg : (minpoly G.F γ).natDegree = G.n)
    (L : Type) [Field L] (ι : L →+* G.C) (hι : Function.Injective ι)
    (hc : ∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) (w : L) :
    ι w ∈ Algebra.adjoin G.F ({γ} : Set G.C) := by
  set B := Algebra.adjoin G.F ({γ} : Set G.C) with hB
  have hBc : B ≤ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
    refine Algebra.adjoin_le ?_
    rw [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg; rw [Set.mem_singleton_iff] at hg; rw [hg]
  have hof : ∀ x : B, ∃ w, ι w = (x : G.C) := by
    intro x
    have hx := hBc x.2
    rw [Subalgebra.mem_centralizer_iff] at hx
    exact (hc x).1 (hx γ (Set.mem_singleton γ)).symm
  haveI : NoZeroDivisors B := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨wx, hwx⟩ := hof x
    obtain ⟨wy, hwy⟩ := hof y
    have h0 : ι (wx * wy) = 0 := by
      rw [map_mul, hwx, hwy]; exact congrArg Subtype.val hxy
    rcases mul_eq_zero.1 (hι (h0.trans (map_zero ι).symm)) with h | h
    · left; apply Subtype.ext; rw [← hwx, h, map_zero]; rfl
    · right; apply Subtype.ext; rw [← hwy, h, map_zero]; rfl
  haveI : IsDomain B := NoZeroDivisors.to_isDomain B
  have hγB : γ ∈ B := Algebra.self_mem_adjoin_singleton G.F γ
  have hint : IsIntegral G.F (⟨γ, hγB⟩ : B) := Algebra.IsIntegral.isIntegral _
  have hirr : Irreducible (minpoly G.F γ) := by
    have e := minpoly.algHom_eq B.val Subtype.val_injective ⟨γ, hγB⟩
    rw [show B.val ⟨γ, hγB⟩ = γ from rfl] at e
    rw [e]; exact minpoly.irreducible hint
  have hcom : Commute (ι w) γ := (hc (ι w)).2 ⟨w, rfl⟩
  exact (GlobalTheory.CentIrr.commute_iff_mem_adjoin G.F G.C G.n G.n_pos G.rankC γ hirr hdeg (ι w)).1 hcom

end GlobalTheory.ConjInt

namespace GlobalTheory.ConjInt

variable {p : ℕ} [Fact p.Prime]

theorem conj_tmul_smul_pow (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (X : (R ⊗[ℚ] G.C)ˣ)
    (c : G.F) (γ : G.C) (k : ℕ) :
    (X : R ⊗[ℚ] G.C) * ((1 : R) ⊗ₜ[ℚ] (c • γ ^ k)) * ↑X⁻¹ =
      ((1 : R) ⊗ₜ[ℚ] algebraMap G.F G.C c) * (↑X * ((1 : R) ⊗ₜ[ℚ] γ) * ↑X⁻¹) ^ k := by
  have hz : ∀ y : G.C, algebraMap G.F G.C c * y = y * algebraMap G.F G.C c := fun y => Algebra.commutes c y
  rw [Units.conj_pow, Algebra.smul_def, ← one_mul (1 : R), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.TensorProduct.tmul_pow, one_pow, ← mul_assoc, ← mul_assoc,
    ← tmul_central_comm _ hz (X : R ⊗[ℚ] G.C)]
  simp only [mul_assoc]

theorem isIntB_conj_map_of_isIntB_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C)
    (κ' : Type) (ℓ : Module.Basis κ' ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      ∀ ρ, IsIntB v ℓ ρ →
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ρ * ↑X⁻¹) := by
  intro p _ G γ hdeg L _ _ ι hι hc κ b κ' ℓ
  haveI : Finite κ := Module.Finite.finite_basis b
  haveI : Finite κ' := Module.Finite.finite_basis ℓ
  haveI := Fintype.ofFinite κ'
  have hq : ∀ a, ∃ q : Polynomial G.F, Polynomial.aeval (γ : G.C) q = ι (ℓ a) := by
    intro a
    have h := mem_adjoin_of_centralizer G (γ : G.C) hdeg L ι.toRingHom hι hc (ℓ a)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h
    exact h
  choose q hq using hq
  have hev : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      (∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j))) ∧
      IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (1 : G.C)) ∧
      ∀ a, ∀ k ∈ Finset.range ((q a).natDegree + 1),
        IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] algebraMap G.F G.C ((q a).coeff k)) :=
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_isIntB_tmul b _).and
      ((eventually_isIntB_tmul b _).and
        (Filter.eventually_all.2 fun a => (Filter.eventually_all_finset _).2 fun k _ =>
          eventually_isIntB_tmul b _))
  refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun v hv X hX ρ hρ => ?_⟩
  have hP := hv
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hP
  obtain ⟨hb, h1, hcoef⟩ := hP
  set ιv := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι
  have hmap : ∀ (r : v.adicCompletion ℚ) (m : L),
      ιv (r • ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] m)) = r • ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ι m) := by
    intro r m
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul']
    rfl
  have hterm : ∀ a, IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ι (ℓ a)) * ↑X⁻¹) := by
    intro a
    rw [← hq a, Polynomial.aeval_eq_sum_range, TensorProduct.tmul_sum, Finset.mul_sum, Finset.sum_mul]
    refine isIntB_sum v b _ _ fun k hk => ?_
    rw [conj_tmul_smul_pow]
    exact isIntB_mul v b hb (hcoef a k hk) (isIntB_pow v b hb h1 hX k)
  rw [eq_sum_basis v ℓ ρ, map_sum, Finset.mul_sum, Finset.sum_mul]
  refine isIntB_sum v b _ _ fun a _ => ?_
  rw [hmap, mul_smul_comm, smul_mul_assoc]
  exact isIntB_smul v b (hρ a) (hterm a)

end GlobalTheory.ConjInt

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C)
    (κ' : Type) (ℓ : Module.Basis κ' ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      ∀ ρ, IsIntB v ℓ ρ →
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ρ * ↑X⁻¹) :=
  GlobalTheory.ConjInt.isIntB_conj_map_of_isIntB_conj
