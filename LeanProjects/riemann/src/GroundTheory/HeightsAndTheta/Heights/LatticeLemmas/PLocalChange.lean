import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights

universe u v

noncomputable section

section Congr

variable {K : Type*} [Field K] [NumberField K]
variable {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup E'] [Module (𝓞 K) E'] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E']

theorem arithDegree_congr (h : HermitianMetric K E) (h' : HermitianMetric K E') (e : E' ≃ₗ[𝓞 K] E)
    (he : ∀ (σ : K →+* ℂ) (x y : E'), (h'.form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      (h.form σ).inner ((1 : ComplexAt σ) ⊗ₜ e x) (1 ⊗ₜ e y)) :
    arithDegree h' = arithDegree h := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := E')
  have hs' : LinearIndependent (𝓞 K) (e ∘ s) := hs.map' e.toLinearMap e.ker
  rw [arithDegree_eq h' hs (Fintype.card_fin _),
    arithDegree_eq h hs' (by rw [Fintype.card_fin, e.finrank_eq])]
  unfold degreeWith
  congr 1
  · congr 2
    apply Nat.card_congr
    refine (Submodule.Quotient.equiv _ _ e ?_).toEquiv
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  · congr 2
    funext σ
    congr 1
    unfold gramDet
    congr 3
    ext i j
    exact he σ (s i) (s j)

end Congr

section Lattices

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem deg_bundle_eq_deg_sub (Nm : HermitianNorms K V) (M L : FullLattice K V)
    (hLM : L.carrier ≤ M.carrier) :
    (Nm.bundle L).deg = ((Nm.bundle M).sub (L.carrier.comap M.carrier.subtype)).deg := by
  unfold HermitianBundle.deg HermitianBundle.arithDegree
  congr 1
  refine (arithDegree_congr _ _ (Submodule.comapSubtypeEquivOfLe hLM) fun σ x y ↦ ?_).symm
  rfl

theorem exists_smul_mem (M : FullLattice K V) (x : V) :
    ∃ b : 𝓞 K, b ≠ 0 ∧ b • x ∈ M.carrier := by
  have hx : x ∈ Submodule.span K (M.carrier : Set V) := M.span_eq ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.carrier.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨b, hb, hby⟩ := hy
    obtain ⟨c, hc, hcz⟩ := hz
    refine ⟨b * c, mul_ne_zero hb hc, ?_⟩
    have e1 : (b * c) • y = c • (b • y) := by rw [mul_comm, mul_smul]
    have e2 : (b * c) • z = b • (c • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact M.carrier.add_mem (M.carrier.smul_mem c hby) (M.carrier.smul_mem b hcz)
  | smul t y _ hy =>
    obtain ⟨b, hb, hby⟩ := hy
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) t
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by simpa using hd0
    refine ⟨d * b, mul_ne_zero hd0 hb, ?_⟩
    have key : (d * b) • ((algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d) • y) = n • (b • y) := by
      rw [← algebraMap_smul K (d * b), ← algebraMap_smul K b y, ← algebraMap_smul K n, smul_smul,
        smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [key]
    exact M.carrier.smul_mem n hby

theorem exists_smulSub_le (M₁ M₂ : FullLattice K V) :
    ∃ b : 𝓞 K, b ≠ 0 ∧ smulSub b M₂.carrier ≤ M₁.carrier := by
  classical
  obtain ⟨S, hS⟩ := M₂.fg
  choose f hf0 hf using exists_smul_mem M₁
  refine ⟨∏ s ∈ S, f s, Finset.prod_ne_zero_iff.mpr fun s _ ↦ hf0 s, ?_⟩
  rw [smulSub, Submodule.map_le_iff_le_comap, ← hS, Submodule.span_le]
  intro s hs
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_coe.mp hs), mul_smul]
  exact M₁.carrier.smul_mem _ (hf s)

end Lattices

theorem finrank_submodule_eq {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    (F : Submodule R M) (hF : ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x ∈ F) :
    Module.finrank R F = Module.finrank R M := by
  have h0 : Module.rank R (M ⧸ F) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨x, rfl⟩ := F.mkQ_surjective x
    obtain ⟨a, ha, hax⟩ := hF x
    refine ⟨a, ha, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hax
  have h := rank_quotient_add_rank_of_isDomain F
  rw [h0, zero_add] at h
  simp only [Module.finrank, h]

section Local

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem det_localSmul (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hb : b ≠ 0) :
    LinearMap.det ((localSmul v hb : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _) :
      (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) =
      localScalar v b ^ Module.finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] V) := by
  have : ((localSmul v hb : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _) :
      (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) =
      localScalar v b • LinearMap.id := LinearMap.ext fun _ ↦ rfl
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

theorem norm_localScalar_eq_one (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hv : b ∉ v.asIdeal) :
    ‖localScalar v b‖ = 1 := by
  rw [localScalar_eq]
  exact (FinitePlace.norm_eq_one_iff_notMem K v b).mpr hv

theorem finite_mem_asIdeal {b : 𝓞 K} (hb : b ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | b ∈ v.asIdeal}.Finite := by
  have e : {v : HeightOneSpectrum (𝓞 K) | b ∈ v.asIdeal} =
      {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ Ideal.span {b}} := by
    ext v
    simp only [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]
  rw [e]
  apply Ideal.finite_factors
  simp only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, hb, not_false_eq_true]

end Local

theorem LocalChange.proof (h1 : Sublattice.Statement.{u, v}) (h2 : LocalIndex.Statement.{u, v}) :
    LocalChange.Statement.{u, v} := by
  intro K _ _ V _ _ _ _ Nm M₁ M₂ g hg hloc
  obtain ⟨b, hb, hbM⟩ := exists_smulSub_le M₁ M₂
  obtain ⟨c, hc, hcM⟩ := exists_smulSub_le M₂ M₁
  set L := scaledLattice M₂ hb with hLdef
  have hL2 : L.carrier ≤ M₂.carrier := smulSub_le b _
  have hL1 : L.carrier ≤ M₁.carrier := hbM
  have hloc2 : ∀ v, (localLattice v L.carrier : Set (v.adicCompletion K ⊗[K] V)) =
      localSmul v hb '' localLattice v M₂.carrier := fun v ↦ localLattice_smulSub v hb _
  have hloc1 : ∀ v, (localLattice v L.carrier : Set (v.adicCompletion K ⊗[K] V)) =
      ((g v).trans (localSmul v hb)) '' localLattice v M₁.carrier := by
    intro v
    rw [hloc2, hloc v, Set.image_image]
    rfl
  have i2 := h2 K V M₂ L (fun v ↦ localSmul v hb) hL2 hloc2
  have i1 := h2 K V M₁ L (fun v ↦ (g v).trans (localSmul v hb)) hL1 hloc1
  have f2 : Module.finrank (𝓞 K) (L.carrier.comap M₂.carrier.subtype) =
      Module.finrank (𝓞 K) M₂.carrier :=
    finrank_submodule_eq _ fun x ↦ ⟨b, hb, mem_smulSub_of_mem b x.2⟩
  have f1 : Module.finrank (𝓞 K) (L.carrier.comap M₁.carrier.subtype) =
      Module.finrank (𝓞 K) M₁.carrier := by
    refine finrank_submodule_eq _ fun x ↦ ⟨b * c, mul_ne_zero hb hc, ?_⟩
    show (b * c) • (x : V) ∈ smulSub b M₂.carrier
    rw [mul_smul]
    exact mem_smulSub_of_mem b (hcM (mem_smulSub_of_mem c x.2))
  have s2 := (h1 K (Nm.bundle M₂) (L.carrier.comap M₂.carrier.subtype) f2).1
  have s1 := (h1 K (Nm.bundle M₁) (L.carrier.comap M₁.carrier.subtype) f1).1
  rw [← deg_bundle_eq_deg_sub Nm M₂ L hL2] at s2
  rw [← deg_bundle_eq_deg_sub Nm M₁ L hL1] at s1

  have hA : ({v | b ∈ v.asIdeal} ∪ {v | g v ≠ 1} : Set (HeightOneSpectrum (𝓞 K))).Finite :=
    (finite_mem_asIdeal hb).union hg
  set T := hA.toFinset with hT
  have hout : ∀ v, v ∉ T → b ∉ v.asIdeal ∧ g v = 1 := by
    intro v hv
    simp only [hT, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or,
      not_not] at hv
    exact hv
  have hS1 : ∀ v, v ∉ T → ‖LinearMap.det ((localSmul v hb : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _) :
      (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V))‖ = 1 := by
    intro v hv
    rw [det_localSmul, norm_pow, norm_localScalar_eq_one v (hout v hv).1, one_pow]
  have hD1 : ∀ v, v ∉ T → LinearMap.det ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K]
      (v.adicCompletion K ⊗[K] V))) = 1 := by
    intro v hv
    rw [(hout v hv).2]
    exact LinearMap.det_id
  have hSne : ∀ v, LinearMap.det ((localSmul v hb : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _) :
      (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) ≠ 0 :=
    fun v ↦ (localSmul v hb).isUnit_det'.ne_zero
  have hDne : ∀ v, LinearMap.det ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K]
      (v.adicCompletion K ⊗[K] V))) ≠ 0 :=
    fun v ↦ (g v).isUnit_det'.ne_zero
  have hcomp : ∀ v, LinearMap.det (((g v).trans (localSmul v hb) : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _) :
      (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) =
      LinearMap.det ((localSmul v hb : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _) :
        (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) *
      LinearMap.det ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K]
        (v.adicCompletion K ⊗[K] V))) := by
    intro v
    rw [LinearEquiv.coe_trans, LinearMap.det_comp]

  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) (fun v hv ↦ by
    by_contra hvT
    exact hv (by simp only [hS1 v hvT, inv_one]))] at i2
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) (fun v hv ↦ by
    by_contra hvT
    exact hv (by simp only [hcomp, hS1 v hvT, hD1 v hvT, mul_one, inv_one]))] at i1
  simp only [hcomp, norm_mul, mul_inv, Finset.prod_mul_distrib] at i1
  rw [finsum_eq_sum_of_support_subset _ (s := T) (fun v hv ↦ by
    by_contra hvT
    exact hv (by simp only [hD1 v hvT, norm_one, Real.log_one]))]
  have hPS : 0 < ∏ v ∈ T, ‖LinearMap.det ((localSmul v hb : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _) :
      (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V))‖⁻¹ :=
    Finset.prod_pos fun v _ ↦ inv_pos.mpr (norm_pos_iff.mpr (hSne v))
  have hPD : 0 < ∏ v ∈ T, ‖LinearMap.det ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K]
      (v.adicCompletion K ⊗[K] V)))‖⁻¹ :=
    Finset.prod_pos fun v _ ↦ inv_pos.mpr (norm_pos_iff.mpr (hDne v))
  have hlogD : Real.log (∏ v ∈ T, ‖LinearMap.det ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K]
      (v.adicCompletion K ⊗[K] V)))‖⁻¹) = -∑ v ∈ T, Real.log ‖LinearMap.det
        ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)))‖ := by
    rw [Real.log_prod (fun v _ ↦ (inv_pos.mpr (norm_pos_iff.mpr (hDne v))).ne'), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ ↦ Real.log_inv _
  rw [s2, s1]
  erw [i2, i1]
  rw [Real.log_mul hPS.ne' hPD.ne', hlogD]
  ring

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
