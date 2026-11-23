import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StarMulOfMulStar
import GroundTheory.AutomorphicForms.StableConjCyclic
import GroundTheory.Brauer.Degree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange

namespace GlobalTheory.LKInv

open Module Polynomial TensorProduct

theorem isUnit_of_isUnit_mulLeft {k A : Type} [Field k] [Ring A] [Algebra k A] (x : A)
    (h : IsUnit (LinearMap.mulLeft k x)) : IsUnit x := by
  set u := h.unit with hu
  set y : A := ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) 1 with hy
  have hxy : x * y = 1 := by
    change LinearMap.mulLeft k x (((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) 1) = 1
    rw [← Module.End.mul_apply]
    have : LinearMap.mulLeft k x = (u : Module.End k A) := rfl
    rw [this, Units.mul_inv, Module.End.one_apply]
  have hly : LinearMap.mulLeft k y = ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) := by
    have e : (u : Module.End k A) * LinearMap.mulLeft k y = 1 := by
      change LinearMap.mulLeft k x * LinearMap.mulLeft k y = 1
      ext z
      simp [← mul_assoc, hxy]
    calc LinearMap.mulLeft k y = ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) *
          ((u : Module.End k A) * LinearMap.mulLeft k y) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [e, mul_one]
  have hyx : y * x = 1 := by
    have := congrArg (fun f : Module.End k A => f 1) (Units.inv_mul u)
    simp only [← hly] at this
    change y * (x * 1) = 1 at this
    rwa [mul_one] at this
  exact ⟨⟨x, y, hxy, hyx⟩, rfl⟩

theorem baseChange_mulLeft {k A K : Type} [Field k] [Ring A] [Algebra k A] [Field K] [Algebra k K]
    (a : A) : (LinearMap.mulLeft k a).baseChange K = LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] a) := by
  ext x
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem exists_isUnit_mem_of_span_baseChange {k A K : Type} [Field k] [Infinite k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Field K] [Algebra k K] (V : Submodule k A) (u : K ⊗[k] A)
    (hu : u ∈ Submodule.span K ((fun a : A => (1 : K) ⊗ₜ[k] a) '' (V : Set A))) (hunit : IsUnit u) :
    ∃ x ∈ V, IsUnit x := by
  classical
  set r := finrank k V
  let b : Basis (Fin r) k V := Module.finBasis k V
  set m := finrank k A
  let bA : Basis (Fin m) k A := Module.finBasis k A
  let M : Fin r → Matrix (Fin m) (Fin m) k := fun i => LinearMap.toMatrix bA bA (LinearMap.mulLeft k (b i : A))
  set D : MvPolynomial (Fin r) k := (∑ i, (MvPolynomial.X i : MvPolynomial (Fin r) k) •
      (M i).map (MvPolynomial.C : k →+* MvPolynomial (Fin r) k)).det with hD
  have key : ∀ {T : Type} [CommRing T] (ψ : MvPolynomial (Fin r) k →+* T),
      ψ D = (∑ i, ψ (MvPolynomial.X i) • (M i).map (ψ.comp (MvPolynomial.C : k →+* MvPolynomial (Fin r) k))).det := by
    intro T _ ψ
    rw [hD, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext p q
    simp [Matrix.sum_apply]

  have hlin : ∀ t : Fin r → k, ∑ i, t i • M i =
      LinearMap.toMatrix bA bA (LinearMap.mulLeft k (∑ i, t i • (b i : A))) := by
    intro t
    have : LinearMap.mulLeft k (∑ i, t i • (b i : A)) = ∑ i, t i • LinearMap.mulLeft k (b i : A) := by
      ext z; simp [Finset.sum_mul]
    rw [this, map_sum]
    simp [M, map_smul]

  have hD0 : D ≠ 0 := by
    have hspan : Submodule.span K ((fun a : A => (1 : K) ⊗ₜ[k] a) '' (V : Set A)) ≤
        Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[k] (b i : A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      have hrep := b.sum_repr ⟨a, ha⟩
      have : (1 : K) ⊗ₜ[k] a = ∑ i, (algebraMap k K (b.repr ⟨a, ha⟩ i)) • ((1 : K) ⊗ₜ[k] (b i : A)) := by
        conv_lhs => rw [show a = ((⟨a, ha⟩ : V) : A) from rfl, ← hrep]
        simp only [Submodule.coe_sum, Submodule.coe_smul, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
          algebraMap_smul]
      show (1 : K) ⊗ₜ[k] a ∈ Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[k] (b i : A))
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hspan hu)
    intro h0
    have h1 := key (MvPolynomial.eval₂Hom (algebraMap k K) s)
    rw [h0, map_zero] at h1
    have hmat : ∑ i, (MvPolynomial.eval₂Hom (algebraMap k K) s) (MvPolynomial.X i) •
        (M i).map ((MvPolynomial.eval₂Hom (algebraMap k K) s).comp MvPolynomial.C) =
        LinearMap.toMatrix (Algebra.TensorProduct.basis K bA) (Algebra.TensorProduct.basis K bA)
          (LinearMap.mulLeft K u) := by
      rw [← hs]
      have : LinearMap.mulLeft K (∑ i, s i • (1 : K) ⊗ₜ[k] (b i : A)) =
          ∑ i, s i • LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] (b i : A)) := by
        ext z; simp [Finset.sum_mul]
      rw [this, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← baseChange_mulLeft, LinearMap.toMatrix_baseChange]
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      rw [MvPolynomial.eval₂Hom_comp_C]
    rw [hmat, LinearMap.det_toMatrix] at h1
    have hu' : IsUnit (LinearMap.mulLeft K u) := by
      obtain ⟨w, rfl⟩ := hunit
      refine ⟨⟨LinearMap.mulLeft K (w : K ⊗[k] A), LinearMap.mulLeft K ((w⁻¹ : (K ⊗[k] A)ˣ) : K ⊗[k] A),
        ?_, ?_⟩, rfl⟩ <;> ext z <;> simp [← mul_assoc]
    have := (LinearMap.isUnit_iff_isUnit_det _).1 hu'
    rw [← h1] at this
    exact not_isUnit_zero this

  obtain ⟨t, ht⟩ : ∃ t : Fin r → k, MvPolynomial.eval t D ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hD0 (MvPolynomial.funext fun x => by rw [hne x, map_zero])
  refine ⟨∑ i, t i • (b i : A), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2, ?_⟩
  apply isUnit_of_isUnit_mulLeft (k := k)
  rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.det_toMatrix bA, ← hlin, isUnit_iff_ne_zero]
  rw [key] at ht
  convert ht using 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_X]
  congr 1
  ext p q
  simp

end GlobalTheory.LKInv

namespace GlobalTheory.LKInv

open Module Polynomial TensorProduct

theorem exists_unit_conj_of_baseChange {k A K : Type} [Field k] [Infinite k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Field K] [Algebra k K] (x₀ x : A) (w : (K ⊗[k] A)ˣ)
    (hw : (w : K ⊗[k] A) * ((1 : K) ⊗ₜ[k] x₀) = ((1 : K) ⊗ₜ[k] x) * w) :
    ∃ g : Aˣ, (g : A) * x₀ = x * g := by
  let a : A →ₗ[k] A := LinearMap.mulRight k x₀ - LinearMap.mulLeft k x
  let a' : K ⊗[k] A →ₗ[K] K ⊗[k] A :=
    LinearMap.mulRight K ((1 : K) ⊗ₜ[k] x₀) - LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] x)
  have hbc := (GlobalTheory.BadCount.finrank_iInf_ker_baseChange k K A (K ⊗[k] A) Unit
    (TensorProduct.mk k K A 1) (TensorProduct.isBaseChange k A K) (fun _ => a) (fun _ => a')
    (fun _ v => by simp [a, a', Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub])).2
  rw [_root_.iInf_const, _root_.iInf_const] at hbc
  have hwmem : (w : K ⊗[k] A) ∈ LinearMap.ker a' := by
    rw [LinearMap.mem_ker]
    simp [a', hw]
  rw [hbc] at hwmem
  obtain ⟨y, hyV, hyu⟩ := exists_isUnit_mem_of_span_baseChange (K := K) (LinearMap.ker a)
    (w : K ⊗[k] A) hwmem w.isUnit
  refine ⟨hyu.unit, ?_⟩
  rw [LinearMap.mem_ker] at hyV
  simpa [a, sub_eq_zero] using hyV

theorem charpoly_eq_map_minpoly {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    {n : ℕ} (e : AlgebraicClosure F ⊗[F] B ≃ₐ[AlgebraicClosure F] Matrix (Fin n) (Fin n) (AlgebraicClosure F))
    (y : B) (hsep : (minpoly F y).Separable) (hdeg : (minpoly F y).natDegree = n) :
    (e ((1 : AlgebraicClosure F) ⊗ₜ[F] y)).charpoly = (minpoly F y).map (algebraMap F (AlgebraicClosure F)) := by
  set K := AlgebraicClosure F
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K y hzi
  have hmap0 : (minpoly F y).map (algebraMap F K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr (minpoly.ne_zero hyi)
  have hzdeg : (minpoly K z).natDegree = n := by
    refine le_antisymm ?_ (hdeg ▸ hge)
    calc (minpoly K z).natDegree ≤ ((minpoly F y).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap0
      _ = n := by rw [natDegree_map, hdeg]
  have hzeq : minpoly K z = (minpoly F y).map (algebraMap F K) := by
    have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
      (by rw [natDegree_map, hdeg, hzdeg])
    rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]
  set N := e z with hN
  have hmN : minpoly K N = minpoly K z := minpoly.algEquiv_eq e z
  have hd : minpoly K N ∣ N.charpoly := minpoly.dvd K N (Matrix.aeval_self_charpoly N)
  rw [hmN] at hd
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hd
    (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hzdeg])
  rw [this, (Matrix.charpoly_monic N).leadingCoeff, C_1, one_mul, hzeq]

theorem exists_unit_conj_of_minpoly_eq (F B : Type) [Field F] [Infinite F] [Ring B] [Algebra F B]
    [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ)
    (hn : Module.finrank F B = n ^ 2) (x₀ x : B) (hsep : (minpoly F x₀).Separable)
    (hdeg : (minpoly F x₀).natDegree = n) (hmin : minpoly F x = minpoly F x₀) :
    ∃ g : Bˣ, (g : B) * x₀ = x * g := by
  classical
  obtain ⟨m, hm0, hmB, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F B
  have hmn : m = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hmB.symm.trans hn)
  subst hmn
  set K := AlgebraicClosure F
  set N₀ := e ((1 : K) ⊗ₜ[F] x₀) with hN₀
  set N := e ((1 : K) ⊗ₜ[F] x) with hN
  have hc₀ := charpoly_eq_map_minpoly e x₀ hsep hdeg
  have hc := charpoly_eq_map_minpoly e x (hmin ▸ hsep) (hmin ▸ hdeg)
  rw [hmin] at hc
  have hsepK : (Matrix.toLin' N₀).charpoly.Separable := by
    rw [Matrix.charpoly_toLin', hc₀]; exact hsep.map
  obtain ⟨e', he'⟩ := GroundTheory.Automorphic.exists_conj_of_charpoly_eq hsepK
    (f' := Matrix.toLin' N) (by rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin', hc₀, hc])
  set P := LinearMap.toMatrix' (e' : (Fin m → K) →ₗ[K] (Fin m → K)) with hP
  set Q := LinearMap.toMatrix' (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) with hQ
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← LinearMap.toMatrix'_comp]
    have : (e' : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) =
        LinearMap.id := by ext v; simp
    rw [this, LinearMap.toMatrix'_id]
  have hQP : Q * P = 1 := by
    rw [hP, hQ, ← LinearMap.toMatrix'_comp]
    have : (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ (e' : (Fin m → K) →ₗ[K] (Fin m → K)) =
        LinearMap.id := by ext v; simp
    rw [this, LinearMap.toMatrix'_id]
  have hPN : P * N₀ = N * P := by
    have : (e' : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ Matrix.toLin' N₀ =
        Matrix.toLin' N ∘ₗ (e' : (Fin m → K) →ₗ[K] (Fin m → K)) :=
      LinearMap.ext fun v => he' v
    have h2 := congrArg LinearMap.toMatrix' this
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_toLin'] at h2

  set w : (K ⊗[F] B)ˣ := ⟨e.symm P, e.symm Q, by rw [← map_mul, hPQ, map_one],
    by rw [← map_mul, hQP, map_one]⟩ with hw
  refine exists_unit_conj_of_baseChange x₀ x w ?_
  apply e.injective
  rw [map_mul, map_mul]
  simp only [hw, Units.val_mk, AlgEquiv.apply_symm_apply]
  rw [← hN₀, ← hN, hPN]

end GlobalTheory.LKInv
