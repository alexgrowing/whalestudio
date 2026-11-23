import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSubMulSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormRootSubOneLt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorRight

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct Topology

namespace GlobalTheory.Cyc.FontW

theorem as_left {R X N P : Type*} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R P] [Module.Flat R P] (i : X →ₗ[R] N) (f : N →ₗ[R] N)
    (h1 : ∀ y, ∃ b, f b - b = y) (hi : ∀ x, f (i x) = i x) (h2 : ∀ b, f b = b → ∃ x, b = i x) :
    (∀ y, ∃ b, f.lTensor P b - b = y) ∧ ∀ b, f.lTensor P b = b → ∃ x, b = i.lTensor P x := by
  have e : (f - LinearMap.id).lTensor P = f.lTensor P - LinearMap.id := by
    rw [LinearMap.lTensor_sub, LinearMap.lTensor_id]
  refine ⟨fun y => ?_, fun b hb => ?_⟩
  · obtain ⟨b, hb⟩ := LinearMap.lTensor_surjective P (g := f - LinearMap.id) (fun y => h1 y) y
    exact ⟨b, by rw [e] at hb; exact hb⟩
  · have hex : Function.Exact i (f - LinearMap.id : N →ₗ[R] N) := fun y =>
      ⟨fun hy => (h2 y (sub_eq_zero.1 hy)).imp fun _ h => h.symm, by
        rintro ⟨x, rfl⟩; exact sub_eq_zero.2 (hi x)⟩
    obtain ⟨x, hx⟩ := (Module.Flat.lTensor_exact P hex b).1 (by rw [e]; exact sub_eq_zero.2 hb)
    exact ⟨x, hx.symm⟩

theorem as_right {R X N P : Type*} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R P] [Module.Flat R P] (i : X →ₗ[R] N) (f : N →ₗ[R] N)
    (h1 : ∀ y, ∃ b, f b - b = y) (hi : ∀ x, f (i x) = i x) (h2 : ∀ b, f b = b → ∃ x, b = i x) :
    (∀ y, ∃ b, f.rTensor P b - b = y) ∧ ∀ b, f.rTensor P b = b → ∃ x, b = i.rTensor P x := by
  have e : (f - LinearMap.id).rTensor P = f.rTensor P - LinearMap.id := by
    rw [LinearMap.rTensor_sub, LinearMap.rTensor_id]
  refine ⟨fun y => ?_, fun b hb => ?_⟩
  · obtain ⟨b, hb⟩ := LinearMap.rTensor_surjective P (g := f - LinearMap.id) (fun y => h1 y) y
    exact ⟨b, by rw [e] at hb; exact hb⟩
  · have hex : Function.Exact i (f - LinearMap.id : N →ₗ[R] N) := fun y =>
      ⟨fun hy => (h2 y (sub_eq_zero.1 hy)).imp fun _ h => h.symm, by
        rintro ⟨x, rfl⟩; exact sub_eq_zero.2 (hi x)⟩
    obtain ⟨x, hx⟩ := (Module.Flat.rTensor_exact P hex b).1 (by rw [e]; exact sub_eq_zero.2 hb)
    exact ⟨x, hx.symm⟩

section Gen

variable {Z O W P : Type*} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O] [Algebra Z W]
  [AddCommGroup P] [Module O P]

theorem as_one [Module.Flat Z O] (f : W →ₐ[Z] W) (h1 : ∀ y, ∃ b, f b - b = y)
    (h2 : ∀ b, f b = b → ∃ z, b = algebraMap Z W z) :
    (∀ y, ∃ b, Algebra.TensorProduct.map (AlgHom.id O O) f b - b = y) ∧
    ∀ b, Algebra.TensorProduct.map (AlgHom.id O O) f b = b →
      ∃ x : O, b = algebraMap _ (O ⊗[Z] W) x := by
  obtain ⟨k1, k2⟩ := as_left (P := O) (Algebra.linearMap Z W) f.toLinearMap
    h1 (fun x => f.commutes x) h2
  have e : ∀ b, Algebra.TensorProduct.map (AlgHom.id O O) f b = f.toLinearMap.lTensor O b := fun b => by
    induction b using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul x y => rfl
  refine ⟨fun y => by simpa only [e] using k1 y, fun b hb => ?_⟩
  obtain ⟨x, rfl⟩ := k2 b (by rw [← e, hb])
  refine ⟨TensorProduct.rid Z _ x, ?_⟩
  clear hb
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.linearMap_apply,
      Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    rfl

theorem as_two [Module.Flat Z O] [Module.Flat O P] (f : W →ₐ[Z] W) (h1 : ∀ y, ∃ b, f b - b = y)
    (h2 : ∀ b, f b = b → ∃ z, b = algebraMap Z W z) :
    (∀ y, ∃ b, TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id O O) f).toLinearMap
      (LinearMap.id : P →ₗ[O] P) b - b = y) ∧
    ∀ b, TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id O O) f).toLinearMap
      (LinearMap.id : P →ₗ[O] P) b = b → ∃ t : P, b = (1 : O ⊗[Z] W) ⊗ₜ[O] t := by
  obtain ⟨h1, h2⟩ := as_one (O := O) f h1 h2
  obtain ⟨k1, k2⟩ := as_right (P := P) (Algebra.linearMap O (O ⊗[Z] W))
    (Algebra.TensorProduct.map (AlgHom.id O O) f).toLinearMap
    h1 (fun x => (Algebra.TensorProduct.map (AlgHom.id O O) f).commutes x) h2
  refine ⟨k1, fun b hb => ?_⟩
  obtain ⟨x, rfl⟩ := k2 b hb
  refine ⟨TensorProduct.lid _ _ x, ?_⟩
  clear hb
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, TensorProduct.tmul_add, hx, hy]
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Algebra.linearMap_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem cob_two [Module.Free Z O] [Module.Finite Z O] [Module.Free O P] [Module.Finite O P]
    {G : Type*} [Group G] (l : ℕ) (𝓕 : Filter G) (hW : Cpl l W) (a : G → W →ₐ[Z] W)
    (ρ : G → P →ₗ[O] P) (amul : ∀ g h β, a (g * h) β = a g (a h β))
    (ρmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (htr : ∀ U ∈ 𝓕, ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓕 ∧ (N : Set G) ⊆ U ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, a n β = β) ∧ ∑ s ∈ S, a s β = 1)
    (c : G → P) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (hcont : ∀ r, {g | c g ∈ Dv l r P} ∈ 𝓕) :
    ∃ b : (O ⊗[Z] W) ⊗[O] P, ∀ g, (1 : O ⊗[Z] W) ⊗ₜ[O] c g =
      TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id O O) (a g)).toLinearMap (ρ g) b - b := by
  have amul' : ∀ g h (β : O ⊗[Z] W), Algebra.TensorProduct.map (AlgHom.id O O) (a (g * h)) β =
      Algebra.TensorProduct.map (AlgHom.id O O) (a g)
        (Algebra.TensorProduct.map (AlgHom.id O O) (a h) β) := fun g h β => by
    induction β using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp [amul]
  refine avg_cob l 𝓕 (fun g β => Algebra.TensorProduct.map (AlgHom.id O O) (a g) β)
    (fun g => (TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id O O) (a g)).toLinearMap
      (ρ g)).toAddMonoidHom) hW.tensor_left.tensor_right amul' (fun g h x => ?_) (fun g β x => ?_)
    (fun U hU => ?_) (fun g => (1 : O ⊗[Z] W) ⊗ₜ[O] c g) (fun g h => ?_) (fun r => ?_)
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, amul', ρmul]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | tmul x y => simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  · obtain ⟨N, h1, h2, h3, S, h4, β, h5, h6⟩ := htr U hU
    refine ⟨N, h1, h2, h3, S, h4, (1 : O) ⊗ₜ[Z] β, fun n hn => by simp [h5 n hn], ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [← TensorProduct.tmul_sum, h6]
    rfl
  · simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.map_tmul,
      AlgHom.toLinearMap_apply, hc, TensorProduct.tmul_add, map_one]
  · filter_upwards [hcont r] with g hg
    exact Dv_map (TensorProduct.mk O (O ⊗[Z] W) P 1) hg

end Gen

theorem lattice_nhds {F O V : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [CommRing O] [Algebra O F] [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]
    [TopologicalSpace V] [IsModuleTopology F V] (T : Submodule O V) (fg : T.FG)
    (hspan : Submodule.span F (T : Set V) = ⊤) (u : ℕ)
    (hu : {x : F | ∃ o : O, x = u • algebraMap O F o} ∈ 𝓝 0) :
    {v : V | ∃ t ∈ T, v = u • t} ∈ 𝓝 0 := by
  obtain ⟨n, t, ht⟩ := Submodule.fg_iff_exists_fin_generating_family.1 fg
  have hs : Function.Surjective (Fintype.linearCombination F t) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ← hspan, ← ht,
      Submodule.span_span_of_tower]
  have ho := IsModuleTopology.isOpenMap_of_surjective hs
  have h1 : Set.pi Set.univ (fun _ : Fin n => {x : F | ∃ o : O, x = u • algebraMap O F o}) ∈
      𝓝 (0 : Fin n → F) := set_pi_mem_nhds Set.finite_univ fun _ _ => hu
  have h2 := ho.image_mem_nhds h1
  rw [map_zero] at h2
  refine Filter.mem_of_superset h2 ?_
  rintro _ ⟨x, hx, rfl⟩
  choose o ho using fun i => hx i (Set.mem_univ i)
  refine ⟨∑ i, o i • t i, sum_mem fun i _ => T.smul_mem _ (ht ▸ Submodule.subset_span ⟨i, rfl⟩), ?_⟩
  rw [Fintype.linearCombination_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [ho i, smul_assoc, algebraMap_smul]

variable {l : ℕ} [Fact l.Prime]

theorem free_OL (LL : FinExt l) : Module.Free ℤ_[l] ↥(OL LL) :=
  haveI := LL.2
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
    exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))
  IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem finite_OL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem OL_nhds (LL : FinExt l) (u : ℕ) (hu : u ≠ 0) :
    {x : ↥LL.1 | ∃ o : ↥(OL LL), x = u • algebraMap ↥(OL LL) ↥LL.1 o} ∈ 𝓝 0 := by
  have hu' : (u : Om l) ≠ 0 := Nat.cast_ne_zero.2 hu
  have hpos : 0 < ‖(u : Om l)‖ := norm_pos_iff.2 hu'
  have h1 : (fun x : ↥LL.1 => (x : Om l)) ⁻¹' Metric.ball 0 ‖(u : Om l)‖ ∈ 𝓝 (0 : ↥LL.1) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hpos)
  refine Filter.mem_of_superset h1 fun x hx => ?_
  have hx' : ‖(x : Om l)‖ < ‖(u : Om l)‖ := by simpa using hx
  refine ⟨⟨x / u, (GlobalTheory.mem_integralClosure_padicInt_iff LL.1 _).2 ?_⟩, ?_⟩
  · push_cast
    rw [norm_div, div_le_one hpos]; exact hx'.le
  · change x = u • (x / u)
    have : (u : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 hu
    rw [nsmul_eq_mul]; field_simp

theorem perfect_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
  obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
  refine ⟨algebraMap _ _ a' / algebraMap _ _ b', ?_⟩
  simp [frobenius_def, div_pow]

theorem exists_trace {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) {G : Type} [Group G]
    [TopologicalSpace G] (ι : G →* GQ l) (hι : Topology.IsEmbedding ι) (hr : ι.range = Hinf K)
    (U : Set G) (hU : U ∈ 𝓝 1) :
    ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓝 1 ∧ (N : Set G) ⊆ U ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, AI.actWCb (ι n) β = β) ∧ ∑ s ∈ S, AI.actWCb (ι s) β = 1 := by
  classical
  rw [hι.isInducing.nhds_eq_comap, map_one] at hU ⊢
  obtain ⟨W, hW, hWU⟩ := hU
  obtain ⟨E, hfd, hN, hE⟩ := (krullTopology_mem_nhds_one_iff_of_normal ℚ_[l] (Om l) W).1 hW
  haveI : E.fixingSubgroup.FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen E.fixingSubgroup E.fixingSubgroup_isOpen
    exact Subgroup.finiteIndex_of_finite_quotient
  have hEn : E.fixingSubgroup.Normal := by
    rw [← IntermediateField.restrictNormalHom_ker]; infer_instance
  let N : Subgroup G := E.fixingSubgroup.comap ι
  haveI : N.FiniteIndex := ⟨by
    rw [Subgroup.index_comap]
    exact (inferInstance : (E.fixingSubgroup.subgroupOf ι.range).FiniteIndex).index_ne_zero⟩
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let S : Finset G := Finset.univ.image (fun q : G ⧸ N => q.out)
  have hS : ∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N := by
    intro h
    have key : ∀ q : G ⧸ N, q.out⁻¹ * h ∈ N ↔ q = (h : G ⧸ N) := by
      intro q
      conv_rhs => rw [← q.out_eq']
      rw [QuotientGroup.eq]
    refine ⟨(h : G ⧸ N).out, ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (key _).2 rfl⟩, ?_⟩
    rintro s ⟨hs, hs'⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    rw [(key q).1 hs']
  have hsup : (Kinf K ⊔ E).fixingSubgroup = Hinf K ⊓ E.fixingSubgroup :=
    IntermediateField.fixingSubgroup_sup
  have hH : ∀ g, ι g ∈ Hinf K := fun g => hr ▸ ⟨g, rfl⟩
  obtain ⟨β, hβ, hsum⟩ := GlobalTheory.Cyc.TraceTilt.main l P AI K (Kinf K ⊔ E) (S.image ι) le_sup_left
    (fun h hh => by
      have : Kinf K ⊔ E ≤ (Kinf K ⊔ E).comap (h : Om l →ₐ[ℚ_[l]] Om l) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · have h1 : h x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx
          change h x ∈ Kinf K ⊔ E
          rw [h1]; exact (le_sup_left : Kinf K ≤ Kinf K ⊔ E) hx
        · change h x ∈ Kinf K ⊔ E
          have h1 := AlgEquiv.restrictNormal_commutes h E ⟨x, hx⟩
          have h2 : h x ∈ E := by
            have : h x = (h.restrictNormal E ⟨x, hx⟩ : E) := h1.symm
            rw [this]; exact Subtype.property _
          exact (le_sup_right : E ≤ Kinf K ⊔ E) h2
      exact fun x hx => this hx)
    (fun s hs => by
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hs
      exact hH t)
    (fun h hh => by
      rw [← hr] at hh
      obtain ⟨g, rfl⟩ := hh
      obtain ⟨s, ⟨hs, hs'⟩, hu⟩ := hS g
      refine ⟨ι s, ⟨Finset.mem_image_of_mem _ hs, ?_⟩, ?_⟩
      · rw [hsup, ← map_inv, ← map_mul]; exact ⟨hH _, hs'⟩
      · rintro _ ⟨ht, ht'⟩
        obtain ⟨t, ht0, rfl⟩ := Finset.mem_image.1 ht
        rw [hsup, ← map_inv, ← map_mul] at ht'
        rw [hu t ⟨ht0, ht'.2⟩])
  refine ⟨N, hEn.comap ι, ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen.mem_nhds (one_mem _), subset_rfl⟩,
    fun g hg => hWU (hE hg), S, hS, β, fun n hn => hβ _ (hsup ▸ ⟨hH n, hn⟩), ?_⟩
  rw [Finset.sum_image fun _ _ _ _ h => hι.injective h] at hsum
  exact hsum

theorem as_TW {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) : (∀ y, ∃ b, TWmap (φRW LL) T b - b = y) ∧
    ∀ b, TWmap (φRW LL) T b = b → ∃ t : ↥T.L.T, b = (1 : RW LL) ⊗ₜ[↥(OL LL)] t :=
  haveI := T.L.free
  haveI := free_OL LL
  as_two (O := ↥(OL LL)) (P := ↥T.L.T) (frobW l) (GlobalTheory.ArtinSchreierWitt.main l).1
    (GlobalTheory.ArtinSchreierWitt.main l).2.1

set_option maxHeartbeats 1600000 in

theorem cob_TW {P : LocPrime l} (AI : LocAinf l P) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (H : Subgroup ↥(GK K))
    (hH : ((GK K).subtype.comp H.subtype).range = Hinf K) (c : ↥(latticeCocycles (resLat T H))) :
    ∃ b : TW (RW LL) T, ∀ (σ : ↥H) (t : ↥T.L.T), (t : T.V) = (c : ↥H → T.V) σ →
      (1 : RW LL) ⊗ₜ[↥(OL LL)] t =
        TWact (AI.gRW LL ((σ : ↥(GK K)) : GQ l)) T (σ : ↥(GK K)) b - b := by
  haveI := T.L.free
  haveI : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI := free_OL LL
  haveI := finite_OL LL
  haveI := perfect_Cb (l := l)
  obtain ⟨c, ⟨hcont, hcoc⟩, hT⟩ := c
  let c' : ↥H → ↥T.L.T := fun σ => ⟨c σ, hT σ (Set.mem_univ _)⟩
  have h1 : c 1 = 0 := by
    have := hcoc 1 1
    rw [mul_one, map_one, Module.End.one_apply] at this
    exact left_eq_add.1 this
  obtain ⟨b, hb⟩ := cob_two (O := ↥(OL LL)) (P := ↥T.L.T) (G := ↥H) l (𝓝 1) (cpl_witt l (Cb l))
    (fun σ => (AI.actWCbHom ((σ : ↥(GK K)) : GQ l)).toAlgHom) (fun σ => T.actT (σ : ↥(GK K)))
    (fun g h β => by
      change AI.actWCbHom ((g : ↥(GK K)) * (h : ↥(GK K))) β = _
      rw [map_mul]; rfl)
    (fun g h x => Subtype.ext (by
      change T.ρ ((g : ↥(GK K)) * (h : ↥(GK K))) x = _
      rw [map_mul]; rfl))
    (exists_trace AI K ((GK K).subtype.comp H.subtype)
      (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal) hH)
    c' (fun g h => Subtype.ext (hcoc g h)) (fun r => by
      have h2 := lattice_nhds T.L.T T.L.fg T.L.span (l ^ r)
        (OL_nhds LL _ (pow_ne_zero r (Fact.out : l.Prime).ne_zero))
      rw [← h1] at h2
      filter_upwards [hcont.continuousAt.preimage_mem_nhds h2] with g hg
      obtain ⟨t, ht, e⟩ := hg
      exact mem_Dv.2 ⟨⟨t, ht⟩, Subtype.ext e.symm⟩)
  refine ⟨b, fun σ t ht => ?_⟩
  obtain rfl : t = c' σ := Subtype.ext ht
  exact hb σ

theorem ker_eq {P : LocPrime l} (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    ((GK K).subtype.comp W.resΓ.ker.subtype).range = Hinf K := by
  obtain ⟨-, -, hc⟩ := GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc
  have hK0 : ∀ g : ↥(GK K), (g : GQ l) ∈ (K0 K).fixingSubgroup := fun g x => g.2 ⟨x.1, x.2.1⟩
  have key : ∀ g : ↥(GK K), W.resΓ g = 1 ↔ P.χQ (g : GQ l) = 1 := by
    intro g
    have h1 := W.χΓ_res g
    rw [P.PD_χ] at h1
    constructor
    · intro hg
      rw [hg, map_one, Units.val_one, map_one] at h1
      exact Units.ext ((algebraMap ℚ_[l] ↥LL.1).injective (by rw [← h1, Units.val_one, map_one]))
    · intro hg
      rw [hg, Units.val_one, map_one] at h1
      refine W.χΓ_inj (Units.ext (Subtype.ext ?_))
      rw [map_one]
      exact h1
  ext g
  constructor
  · rintro ⟨σ, rfl⟩
    exact (hc K _ (hK0 σ)).2.2 ((key σ).1 σ.2)
  · intro hg
    have hle : K.1 ≤ Kinf K := h.2.2.1.trans (sup_le_sup_left
      (IntermediateField.adjoin.mono ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}
        {x : Om l | ∃ j : ℕ, x ^ (l ^ j) = 1} fun x hx => ⟨s, hx⟩) _)
    have hgK : g ∈ GK K := fun x => hg ⟨x.1, hle x.2⟩
    exact ⟨⟨⟨g, hgK⟩, (key ⟨g, hgK⟩).2 ((hc K g (hK0 ⟨g, hgK⟩)).2.1 hg)⟩, rfl⟩

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; FNatW S := by
  intro D HW F l _ K s LL h S E T
  obtain ⟨h1, h2⟩ := as_TW LL T
  refine ⟨fun x _ => ?_, h2, fun c => ?_⟩
  · obtain ⟨b, hb⟩ := h1 x
    exact ⟨b, Submodule.mem_top, hb⟩
  · obtain ⟨b, hb⟩ := cob_TW (D.locA l) K LL T ((HW l).W K s LL h).resΓ.ker
      (ker_eq K s LL h _) c
    exact ⟨b, Submodule.mem_top, hb⟩

end GlobalTheory.Cyc.FontW
