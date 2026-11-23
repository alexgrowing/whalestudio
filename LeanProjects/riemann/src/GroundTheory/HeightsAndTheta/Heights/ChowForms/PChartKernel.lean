import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartKernel

theorem aeval_smul_of_isHomogeneous {F σ S : Type*} [Field F] [CommRing S] [Algebra F S]
    {φ : MvPolynomial σ F} {d : ℕ} (hφ : φ.IsHomogeneous d) (a : S) (x : σ → S) :
    aeval (a • x) φ = a ^ d * aeval x φ := by
  simp only [aeval_def, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : ∑ i ∈ s.support, s i = d := by
    rw [← hφ (mem_support_iff.mp hs)]
    simp [Finsupp.weight_apply, Finsupp.sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs']
  ring

theorem map_eq_zero_iff_of_ker_eq {A B B' σ : Type*} [CommRing A] [CommRing B] [CommRing B']
    {f : A →+* B} {f' : A →+* B'} (h : RingHom.ker f = RingHom.ker f') (x : MvPolynomial σ A) :
    map f x = 0 ↔ map f' x = 0 := by
  simp only [MvPolynomial.ext_iff, coeff_map, coeff_zero]
  exact forall_congr' fun s => by rw [← RingHom.mem_ker, ← RingHom.mem_ker, h]

variable {F : Type} [Field F] {n : ℕ}

theorem pow_mul_aeval_eq {K : Type*} [Field K] [Algebra F K] (t : Fin n → F) (ξ : Fin n → K)
    (hτ : aeval ξ (linForm t) ≠ 0) (g : MvPolynomial (Fin n) F) :
    aeval ξ (linForm t) ^ g.totalDegree * aeval ((aeval ξ (linForm t))⁻¹ • ξ) g =
      aeval ξ (∑ d ∈ Finset.range (g.totalDegree + 1),
        linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) := by
  conv_lhs => arg 2; rw [← sum_homogeneousComponent g]
  rw [map_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d ≤ g.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  have key := aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d g) (aeval ξ (linForm t))
    ((aeval ξ (linForm t))⁻¹ • ξ)
  rw [smul_smul, mul_inv_cancel₀ hτ, one_smul] at key
  rw [map_mul, map_pow, key, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hd']

theorem ker_aeval_chart (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (hI : IsHomogIdeal I)
    (t : Fin n → F) (hτ : aeval (genPt I) (linForm t) ≠ 0) :
    RingHom.ker (aeval ((aeval (genPt I) (linForm t))⁻¹ • genPt I)).toRingHom =
      I ⊔ Ideal.span {linForm t - 1} := by
  set ξ := genPt I
  set τ := aeval ξ (linForm t)
  have hξ : ∀ g, aeval ξ g = 0 ↔ g ∈ I := by
    intro g
    have : aeval ξ g = algebraMap (MvPolynomial (Fin n) F ⧸ I) (FractionRing (MvPolynomial (Fin n) F ⧸ I))
        (Ideal.Quotient.mk I g) := by
      have h : (aeval ξ : MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I)) =
          (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ I) (FractionRing (MvPolynomial (Fin n) F ⧸ I))).comp
            (Ideal.Quotient.mkₐ F I) := by
        ext j
        simp [ξ, genPt]
      rw [h]
      rfl
    rw [this, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  apply le_antisymm
  · intro g hg
    rw [RingHom.mem_ker] at hg
    change aeval (τ⁻¹ • ξ) g = 0 at hg
    have hG := pow_mul_aeval_eq t ξ hτ g
    rw [hg, mul_zero, eq_comm, hξ] at hG
    have hGg : (∑ d ∈ Finset.range (g.totalDegree + 1),
        linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) - g ∈ Ideal.span {linForm t - 1} := by
      rw [show (∑ d ∈ Finset.range (g.totalDegree + 1),
          linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) - g =
          ∑ d ∈ Finset.range (g.totalDegree + 1),
            (linForm t ^ (g.totalDegree - d) * homogeneousComponent d g - homogeneousComponent d g) by
        rw [Finset.sum_sub_distrib, sum_homogeneousComponent]]
      refine Ideal.sum_mem _ fun d _ => ?_
      rw [Ideal.mem_span_singleton, ← sub_one_mul]
      exact (sub_one_dvd_pow_sub_one _ _).mul_right _
    have : g = (∑ d ∈ Finset.range (g.totalDegree + 1),
        linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) -
        ((∑ d ∈ Finset.range (g.totalDegree + 1),
        linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) - g) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hG) (Ideal.mem_sup_right hGg)
  · refine sup_le ?_ ?_
    · intro g hg
      rw [RingHom.mem_ker]
      change aeval (τ⁻¹ • ξ) g = 0
      have hG := pow_mul_aeval_eq t ξ hτ g
      have hmem : (∑ d ∈ Finset.range (g.totalDegree + 1),
          linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) ∈ I :=
        Ideal.sum_mem _ fun d _ => Ideal.mul_mem_left _ _ (hI g hg d)
      rw [← hξ] at hmem
      rw [hmem] at hG
      exact (mul_eq_zero.mp hG).resolve_left (pow_ne_zero _ hτ)
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      change aeval (τ⁻¹ • ξ) (linForm t - 1) = 0
      have : aeval (τ⁻¹ • ξ) (linForm t) = τ⁻¹ * τ := by
        simp [τ, linForm, Finset.mul_sum, mul_left_comm]
      rw [map_sub, this, inv_mul_cancel₀ hτ, map_one, sub_self]

theorem aeval_genPt_eq_zero_iff (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (g : MvPolynomial (Fin n) F) :
    aeval (genPt I) g = 0 ↔ g ∈ I := by
  have h : (aeval (genPt I) : MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I)) =
      (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ I) (FractionRing (MvPolynomial (Fin n) F ⧸ I))).comp
        (Ideal.Quotient.mkₐ F I) := by
    ext j
    simp [genPt]
  have h' : aeval (genPt I) g = algebraMap (MvPolynomial (Fin n) F ⧸ I)
      (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (Ideal.Quotient.mk I g) := by
    rw [h]
    rfl
  rw [h', map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

theorem map_genSubst_X {B : Type*} [CommRing B] {e : ℕ} (q : MvPolynomial (Fin n) F →+* B) (t : Fin n → F)
    (ij : Fin e × Fin n) :
    map q (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m)) ij) =
      genSubst (fun m => q (X m)) (fun m => q (C (t m))) ij := by
  simp [genSubst, map_sum]

theorem eval₂_genSubst_eq_map {B : Type*} [CommRing B] {e : ℕ} (q : MvPolynomial (Fin n) F →+* B)
    (t : Fin n → F) (g : MvPolynomial (Fin e × Fin n) F) :
    eval₂ (C.comp (q.comp C)) (genSubst (fun m => q (X m)) (fun m => q (C (t m)))) g =
      map q (aeval (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m))) g) := by
  rw [aeval_def, eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.algebraMap_apply, map_C,
        MvPolynomial.algebraMap_eq]
  · funext ij
    exact (map_genSubst_X q t ij).symm

theorem genSubst_scale {K : Type*} [Field K] {e : ℕ} (ξ s : Fin n → K) (τ : K) (ij : Fin e × Fin n) :
    genSubst ξ (fun m => τ⁻¹ * s m) ij = genSubst (τ⁻¹ • ξ) s ij := by
  simp only [genSubst, Pi.smul_apply, smul_eq_mul, C_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem aeval_genSubst_scale {K : Type*} [Field K] [Algebra F K] {e : ℕ} (ξ : Fin n → K) (τ : K) (t : Fin n → F)
    (g : MvPolynomial (Fin e × Fin n) F) :
    aeval (genSubst ξ (fun m => τ⁻¹ * algebraMap F K (t m))) g =
      map (aeval (τ⁻¹ • ξ)).toRingHom
        (aeval (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m))) g) := by
  have h1 : (genSubst ξ (fun m => τ⁻¹ * algebraMap F K (t m)) : Fin e × Fin n → MvPolynomial (Fin e × Fin n) K) =
      genSubst (τ⁻¹ • ξ) (fun m => algebraMap F K (t m)) := funext fun ij => genSubst_scale _ _ _ ij
  have h2 : (fun m => (aeval (τ⁻¹ • ξ)).toRingHom (X m : MvPolynomial (Fin n) F)) = τ⁻¹ • ξ := funext fun m => by simp
  have h3 : (fun m => (aeval (τ⁻¹ • ξ)).toRingHom (C (t m) : MvPolynomial (Fin n) F)) = fun m => algebraMap F K (t m) :=
    funext fun m => by simp
  have h4 : C.comp ((aeval (τ⁻¹ • ξ)).toRingHom.comp C) = algebraMap F (MvPolynomial (Fin e × Fin n) K) :=
    RingHom.ext fun r => by simp [MvPolynomial.algebraMap_apply]
  rw [← eval₂_genSubst_eq_map, h2, h3, h4, h1, aeval_def]

variable (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)

def chartSubst : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* MvPolynomial (Fin e × Fin n) (ChartInc I t e) :=
  eval₂Hom (C.comp ((chartX I t e).comp C))
    (Sum.elim (fun m => C (chartX I t e (X m)))
      (genSubst (fun m => chartX I t e (X m)) (fun m => chartX I t e (C (t m)))))

def chartEv : MvPolynomial (Fin e × Fin n) (ChartInc I t e) →+* ChartInc I t e :=
  eval₂Hom (RingHom.id _) (fun ij => chartIncHom I t e (X ij))

theorem chartSubst_inl (g : MvPolynomial (Fin n) F) :
    chartSubst I t e (rename Sum.inl g) = C (chartX I t e g) := by
  have h : (chartSubst I t e).comp (rename Sum.inl).toRingHom = C.comp (chartX I t e) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [chartSubst]
    · intro m
      simp [chartSubst]
  exact RingHom.congr_fun h g

theorem chartSubst_inr (g : MvPolynomial (Fin e × Fin n) F) :
    chartSubst I t e (rename Sum.inr g) =
      map (chartX I t e) (aeval (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m))) g) := by
  rw [← eval₂_genSubst_eq_map, chartSubst, coe_eval₂Hom, eval₂_rename, Sum.elim_comp_inr]

theorem chartX_eq_zero {g : MvPolynomial (Fin n) F} (hg : g ∈ I ⊔ Ideal.span {linForm t - 1}) :
    chartX I t e g = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))

theorem chartIncIdeal_le_ker : chartIncIdeal I t e ≤ RingHom.ker (chartSubst I t e) := by
  have h1 : ∑ m, chartX I t e (C (t m)) * chartX I t e (X m) = 1 := by
    have := chartX_eq_zero I t e (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (linForm t - 1)))
    rw [map_sub, map_one, sub_eq_zero] at this
    simpa [linForm, map_sum] using this
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    rw [chartSubst_inl, chartX_eq_zero I t e hg, map_zero]
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have hC : ∑ l, C (chartX I t e (C (t l))) * C (chartX I t e (X l)) =
        (1 : MvPolynomial (Fin e × Fin n) (ChartInc I t e)) := by
      rw [← C_1, ← h1, map_sum]
      simp only [C_mul]
    simp only [chartSubst, map_sum, map_mul, eval₂Hom_X', Sum.elim_inr, Sum.elim_inl]
    simp only [genSubst, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hC, mul_one, sub_self]

theorem chartEv_chartSubst (p : MvPolynomial (Fin n ⊕ Fin e × Fin n) F) :
    chartEv I t e (chartSubst I t e p) = Ideal.Quotient.mk (chartIncIdeal I t e) p := by
  have hXl : ∀ m, chartX I t e (X m) = Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inl m)) := fun m =>
    congrArg (Ideal.Quotient.mk (chartIncIdeal I t e)) (rename_X Sum.inl m)
  have hU : ∀ ij, chartIncHom I t e (X ij) = Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inr ij)) := fun ij =>
    congrArg (Ideal.Quotient.mk (chartIncIdeal I t e)) (rename_X Sum.inr ij)
  have hCr : ∀ r, chartX I t e (C r) = Ideal.Quotient.mk (chartIncIdeal I t e) (C r) := fun r =>
    congrArg (Ideal.Quotient.mk (chartIncIdeal I t e)) (rename_C Sum.inl r)
  have h0 : ∀ i : Fin e, ∑ l, chartIncHom I t e (X (i, l)) * chartX I t e (X l) = 0 := by
    intro i
    have : ∑ l, chartIncHom I t e (X (i, l)) * chartX I t e (X l) =
        Ideal.Quotient.mk (chartIncIdeal I t e) (∑ m, X (Sum.inr (i, m)) * X (Sum.inl m)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hU, hXl]
      exact (map_mul _ _ _).symm
    rw [this]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  have h : (chartEv I t e).comp (chartSubst I t e) = Ideal.Quotient.mk (chartIncIdeal I t e) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, chartEv, chartSubst, coe_eval₂Hom, eval₂_C, RingHom.id_apply]
      exact hCr r
    · rintro (m | ij)
      · simp only [RingHom.comp_apply, chartEv, chartSubst, coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.id_apply,
          Sum.elim_inl]
        exact hXl m
      · simp only [RingHom.comp_apply, chartEv, chartSubst, coe_eval₂Hom, eval₂_X, Sum.elim_inr, genSubst,
          eval₂_sub, eval₂_mul, eval₂_sum, eval₂_C, RingHom.id_apply, h0, zero_mul, sub_zero]
        exact hU ij
  exact RingHom.congr_fun h p

variable {I t e}

theorem proof (h₁ : IncidenceGeneric.Statement) (h₂ : ChartIncDomain.Statement) : ChartKernel.Statement := by
  intro F _ n e I t hI ht
  haveI := hI.isPrime
  obtain ⟨-, hX⟩ := h₂ F n e I t hI ht
  have hτ : aeval (genPt I) (linForm t) ≠ 0 := fun h => ht ((aeval_genPt_eq_zero_iff I _).mp h)
  have hc : ∑ j, (aeval (genPt I) (linForm t))⁻¹ *
      algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t j) * genPt I j = 1 := by
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [show ∑ j, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t j) * genPt I j =
      aeval (genPt I) (linForm t) by simp [linForm], inv_mul_cancel₀ hτ]
  ext g
  rw [RingHom.mem_ker, h₁ F n e I _ hc g, aeval_genSubst_scale,
    ← map_eq_zero_iff_of_ker_eq (hX.trans (ker_aeval_chart I hI.isHomog t hτ).symm), ← chartSubst_inr]
  change Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inr g) = 0 ↔ _
  constructor
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem] at h
    exact chartIncIdeal_le_ker I t e h
  · intro h
    have := chartEv_chartSubst I t e (rename Sum.inr g)
    rw [h, map_zero] at this
    exact this.symm

end ChartKernel

end

end GroundTheory.Heights₂.Heights
