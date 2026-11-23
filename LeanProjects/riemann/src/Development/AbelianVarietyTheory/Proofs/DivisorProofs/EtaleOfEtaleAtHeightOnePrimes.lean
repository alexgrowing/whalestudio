import Mathlib
open IsLocalRing

namespace GlobalTheory.PurityDisc
open TensorProduct

theorem trace_one_tmul (R A S : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing S]
    [Algebra R S] [Module.Free R A] [Module.Finite R A] (a : A) :
    Algebra.trace S (S ⊗[R] A) (1 ⊗ₜ a) = algebraMap R S (Algebra.trace R A a) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]

theorem discr_baseChange (R A S : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing S]
    [Algebra R S] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) :
    Algebra.discr S (Algebra.TensorProduct.basis S b) = algebraMap R S (Algebra.discr R b) := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, trace_one_tmul]

theorem trace_pi (K σ : Type) [Field K] [Fintype σ] [DecidableEq σ] (z : σ → K) :
    Algebra.trace K (σ → K) z = ∑ i, z i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun K σ), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Pi.single_apply]

theorem traceForm_pi_nondegenerate (K σ : Type) [Field K] [Fintype σ] [DecidableEq σ] :
    (Algebra.traceForm K (σ → K)).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · funext i
    have h := hx (Pi.single i 1)
    rw [Algebra.traceForm_apply, trace_pi] at h
    simpa [Pi.single_apply] using h
  · funext i
    have h := hx (Pi.single i 1)
    rw [Algebra.traceForm_apply, trace_pi] at h
    simpa [Pi.single_apply] using h

theorem discr_ne_zero_of_etale (K A : Type) [Field K] [CommRing A] [Algebra K A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K A) [Algebra.Etale K A] :
    Algebra.discr K b ≠ 0 := by
  classical
  let L := AlgebraicClosure K
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[K] A)
  haveI : Module.Finite L (L ⊗[K] A) := Module.Finite.of_basis (Algebra.TensorProduct.basis L b)
  haveI : IsArtinianRing (L ⊗[K] A) := isArtinian_of_tower L inferInstance
  haveI : Fintype (PrimeSpectrum (L ⊗[K] A)) := Fintype.ofFinite _
  let c := (Algebra.TensorProduct.basis L b).map e.toLinearEquiv
  have hc : Algebra.discr L c ≠ 0 := by
    have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c).mp
      (traceForm_pi_nondegenerate L (PrimeSpectrum (L ⊗[K] A)))
    rw [Algebra.discr_def]
    convert h using 2
    ext i j
    rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have h2 : Algebra.discr L c = Algebra.discr L (Algebra.TensorProduct.basis L b) := by
    rw [Algebra.discr_eq_discr_of_algEquiv (Algebra.TensorProduct.basis L b) e]
    rfl
  rw [h2, discr_baseChange] at hc
  intro h
  exact hc (by rw [h, map_zero])

theorem exists_dual (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (h : IsUnit (Algebra.discr R b)) :
    ∃ d : ι → A, ∀ i j, Algebra.trace R A (b i * d j) = if i = j then 1 else 0 := by
  classical
  set M := Algebra.traceMatrix R b
  have hM : IsUnit M.det := by rwa [Algebra.discr_def] at h
  refine ⟨fun j => ∑ k, M⁻¹ k j • b k, fun i j => ?_⟩
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have := congrFun (congrFun h1 i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  rw [← this, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, LinearMap.map_smul, smul_eq_mul, mul_comm]
  simp [M, Algebra.traceMatrix_apply, Algebra.traceForm_apply]

theorem formallyUnramified_of_dual (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (d : ι → A)
    (hd : ∀ i j, Algebra.trace R A (b i * d j) = if i = j then 1 else 0) :
    Algebra.FormallyUnramified R A := by
  classical
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  set T := Algebra.trace R A

  have hrepr : ∀ (z : A) (i : ι), b.repr z i = T (z * d i) := by
    intro z i
    conv_rhs => rw [← b.sum_repr z]
    rw [Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, LinearMap.map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp

  have hnd : ∀ u : A, (∀ k, T (u * b k) = 0) → u = 0 := by
    intro u hu
    rw [← b.sum_repr u]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hrepr, ← b.sum_repr (d j), Finset.mul_sum, map_sum]
    simp_rw [mul_smul_comm, LinearMap.map_smul, hu, smul_zero, Finset.sum_const_zero, zero_smul]

  have hexp : ∀ z : A, ∑ i, T (z * b i) • d i = z := by
    intro z
    rw [← sub_eq_zero]
    refine hnd _ fun k => ?_
    rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, LinearMap.map_smul, mul_comm (d _) (b k), hd, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    simp
  rw [Algebra.FormallyUnramified.iff_exists_tensorProduct]
  refine ⟨∑ i, b i ⊗ₜ[R] d i, fun s => ?_, ?_⟩
  · rw [sub_mul, sub_eq_zero, Finset.mul_sum, Finset.mul_sum]
    simp_rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    symm
    calc ∑ i, (s * b i) ⊗ₜ[R] d i
        = ∑ i, ∑ j, (T (s * b i * d j) • b j) ⊗ₜ[R] d i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← b.sum_repr (s * b i)]
          rw [TensorProduct.sum_tmul]
          simp_rw [hrepr]
      _ = ∑ j, b j ⊗ₜ[R] (∑ i, T ((s * d j) * b i) • d i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [TensorProduct.tmul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.smul_tmul]
          congr 2
          ring_nf
      _ = ∑ j, b j ⊗ₜ[R] (s * d j) := by simp_rw [hexp]
  · rw [map_sum]
    simp_rw [Algebra.TensorProduct.lmul'_apply_tmul]
    rw [← sub_eq_zero]
    refine hnd _ fun k => ?_
    rw [sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum]
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hrepr]
    congr 1
    ring

theorem etale_of_isUnit_discr (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (h : IsUnit (Algebra.discr R b)) :
    Algebra.Etale R A := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  obtain ⟨d, hd⟩ := exists_dual R A b h
  haveI := formallyUnramified_of_dual R A b d hd
  haveI : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  haveI : Algebra.FinitePresentation R A := inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

theorem exists_height_one_mem (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {x : R}
    (hx : x ≠ 0) (hu : ¬ IsUnit x) : ∃ P : Ideal R, P.IsPrime ∧ P.height = 1 ∧ x ∈ P := by
  have hne : Ideal.span {x} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨P, hmin, -⟩ := Ideal.exists_minimalPrimes_le hxM
  have hP : P.IsPrime := hmin.1.1
  have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hmin.1.2
  have : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have h1 : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
  have hP0 : P ≠ ⊥ := fun h => hx (by rw [h] at hxP; exact hxP)
  have h0 : P.height ≠ 0 := fun h => hP0 (Ideal.height_eq_zero_iff_eq_bot.mp h)
  exact ⟨P, hP, le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0), hxP⟩

theorem etale_of_etale_height_one : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A],
    ¬ IsField R →
    (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p)
      (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro R A _ _ _ _ _ _ _ _ hR hp
  classical
  let b := Module.Free.chooseBasis R A
  have key : ∀ p : Ideal R, p.IsPrime → p.height = 1 → Algebra.discr R b ∉ p := by
    intro p hp' h1
    haveI := hp'
    haveI := hp p h1
    let Rp := Localization.AtPrime p
    let κ := ResidueField Rp
    have h := discr_ne_zero_of_etale κ (κ ⊗[Rp] (Rp ⊗[R] A))
      (Algebra.TensorProduct.basis κ (Algebra.TensorProduct.basis Rp b))
    rw [discr_baseChange, discr_baseChange] at h
    have hu : IsUnit (algebraMap R Rp (Algebra.discr R b)) := by
      by_contra hn
      exact h ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff Rp p _).mp hu
  have hd : IsUnit (Algebra.discr R b) := by
    by_contra hn
    by_cases h0 : Algebra.discr R b = 0
    · obtain ⟨y, hy0, hyu⟩ : ∃ y : R, y ≠ 0 ∧ ¬ IsUnit y := by
        by_contra H
        push_neg at H
        exact hR ⟨exists_pair_ne R, mul_comm, fun {a} ha => (H a ha).exists_right_inv⟩
      obtain ⟨P, hP, h1, hyP⟩ := exists_height_one_mem R hy0 hyu
      exact key P hP h1 (h0 ▸ P.zero_mem)
    · obtain ⟨P, hP, h1, hdP⟩ := exists_height_one_mem R h0 hn
      exact key P hP h1 hdP
  exact etale_of_isUnit_discr R A b hd

end GlobalTheory.PurityDisc
