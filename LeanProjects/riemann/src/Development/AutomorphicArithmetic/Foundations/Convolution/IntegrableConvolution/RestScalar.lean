import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory

namespace UpperTheory.ConvolutionTheory.L1

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem finAt_eq (y : AdelicGLn.FiniteAdelicGL K n) (v : Pl K) :
    finAt v (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y v := by
  show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n y)).2) v = _
  rw [prodEquiv_finEmb]

private def tr (T : Finset (Pl K)) (h : AdelicGLn.FiniteAdelicGL K n) : AdelicGLn.FiniteAdelicGL K n :=
  (AdelicGLn.finiteRestrictedEquiv K n).symm (AdelicGLn.truncate T (AdelicGLn.finiteRestrictedEquiv K n h))

open Classical in
private theorem tr_insert {T : Finset (Pl K)} {b : Pl K} (hb : b ∉ T) (h : AdelicGLn.FiniteAdelicGL K n) :
    tr (insert b T) h = tr T h * AdelicGLn.localEmbedding b (AdelicGLn.finiteRestrictedEquiv K n h b) := by
  unfold tr
  rw [AdelicGLn.truncate_insert hb, map_mul]
  rfl

open Classical in
private theorem tr_comm {T : Finset (Pl K)} {b : Pl K} (hb : b ∉ T) (h : AdelicGLn.FiniteAdelicGL K n)
    (g : GL (Fin n) (b.adicCompletion K)) :
    tr T h * AdelicGLn.localEmbedding b g = AdelicGLn.localEmbedding b g * tr T h := by
  unfold tr AdelicGLn.localEmbedding
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← map_mul, ← map_mul]
  congr 1
  refine RestrictedProduct.ext _ _ fun w => ?_
  rw [RestrictedProduct.mul_apply, RestrictedProduct.mul_apply, AdelicGLn.truncate_apply,
    RestrictedProduct.coe_mulSingle_apply]
  by_cases hw : w = b
  · subst hw
    simp [hb]
  · simp [hw]

private theorem exists_tr_mem (g : AdelicGLn.FiniteAdelicGL K n) {U : Set (AdelicGLn.FiniteAdelicGL K n)}
    (hU : U ∈ 𝓝 g) (B : Finset (Pl K)) : ∃ T, B ⊆ T ∧ tr T g ∈ U := by
  classical
  set Φ := AdelicGLn.finiteRestrictedEquiv K n
  set y := Φ g
  have hopen : ∀ v : Pl K,
      IsOpen (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) :=
    fun v => GLnLocal.isOpen_integralGL (v.adicCompletion K) n
  have hV : Φ.symm ⁻¹' U ∈ 𝓝 y :=
    Φ.symm.continuous.continuousAt.preimage_mem_nhds
      (by convert hU using 2; exact Φ.symm_apply_apply g)
  have : Fact (∀ v : Pl K,
      IsOpen (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))) :=
    ⟨hopen⟩
  have hW : (fun w => y * w) ⁻¹' (Φ.symm ⁻¹' U) ∈ 𝓝 (1 : AdelicGLn.FiniteRestrictedGL K n) :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hV)
  have h1 : (1 : AdelicGLn.FiniteRestrictedGL K n) =
      RestrictedProduct.structureMap _ (fun v : Pl K => (GLnLocal.integralGL (v.adicCompletion K) n :
        Set (GL (Fin n) (v.adicCompletion K)))) cofinite 1 := rfl
  rw [h1, RestrictedProduct.nhds_eq_map_structureMap hopen, Filter.mem_map, nhds_pi,
    Filter.mem_pi] at hW
  obtain ⟨I, hI, t, ht, hsub⟩ := hW
  have hbad : {v | y v ∉ GLnLocal.integralGL (v.adicCompletion K) n}.Finite :=
    Filter.eventually_cofinite.1 y.2
  set S : Finset (Pl K) := (hI.toFinset ∪ hbad.toFinset) ∪ B
  have hmem : ∀ v, (y⁻¹ * AdelicGLn.truncate S y) v ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
    intro v
    rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, AdelicGLn.truncate_apply]
    split_ifs with hv
    · rw [inv_mul_cancel]
      exact one_mem _
    · have : y v ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
        by_contra h
        exact hv (Finset.mem_union_left _ (Finset.mem_union_right _ (hbad.mem_toFinset.2 h)))
      rw [mul_one]
      exact inv_mem this
  let w' : Π v : Pl K,
      (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) :=
    fun v => ⟨(y⁻¹ * AdelicGLn.truncate S y) v, hmem v⟩
  have hw' : RestrictedProduct.structureMap _ _ cofinite w' = y⁻¹ * AdelicGLn.truncate S y :=
    RestrictedProduct.ext _ _ fun v => rfl
  have hw'I : w' ∈ I.pi t := by
    intro v hv
    have hvS : v ∈ S := Finset.mem_union_left _ (Finset.mem_union_left _ (hI.mem_toFinset.2 hv))
    have : w' v = 1 := Subtype.ext <| by
      change (y⁻¹ * AdelicGLn.truncate S y) v = 1
      rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, AdelicGLn.truncate_apply, if_pos hvS,
        inv_mul_cancel]
    rw [this]
    exact mem_of_mem_nhds (ht v)
  have hU' := hsub hw'I
  simp only [Set.mem_preimage, hw', mul_inv_cancel_left] at hU'
  exact ⟨S, Finset.subset_union_right, hU'⟩

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem rhoF_mul (a b : AdelicGLn.FiniteAdelicGL K n) (x : LL μ) :
    rhoF μ (a * b) x = rhoF μ a (rhoF μ b x) := by
  unfold rhoF
  rw [map_mul, UnitaryRep.map_mul_apply]

private theorem rhoF_one (x : LL μ) : rhoF μ (1 : AdelicGLn.FiniteAdelicGL K n) x = x := by
  unfold rhoF
  rw [map_one, UnitaryRep.map_one_apply]

private theorem continuous_rhoF (x : LL μ) : Continuous fun g : AdelicGLn.FiniteAdelicGL K n => rhoF μ g x :=
  (UnitaryRep.continuous_orbit _ x).comp MultiplicityOne.continuous_finProj

private theorem mem_eigL {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} {x : LL μ} :
    x ∈ eigL μ w J χ ↔ ∀ g ∈ J, rhoL μ w g x = χ g • x := by
  simp [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem prj_prj_of_le {A B : Submodule ℂ (LL μ)} (hAB : A ≤ B) (x : LL μ) :
    prj A (prj B x) = prj A x := by
  have hle : A.topologicalClosure ≤ B.topologicalClosure := Submodule.topologicalClosure_mono hAB
  exact congrArg (fun T : LL μ →L[ℂ] LL μ => T x) (Submodule.starProjection_comp_starProjection_of_le hle)

private theorem scalar_tr (V : Submodule ℂ (LL μ))
    (hinv : ∀ (g : AdelicGLn.FiniteAdelicGL K n), ∀ v ∈ V, rhoF μ g v ∈ V)
    (J : ∀ w : Pl K, Subgroup (Gw n w)) (χ : ∀ w : Pl K, Gw n w → ℂ) (P : Set (Pl K))
    (hr : ∀ w ∉ P, RankOne μ V w (J w) (χ w)) (h : AdelicGLn.FiniteAdelicGL K n)
    (hP : ∀ w ∈ P, AdelicGLn.finiteRestrictedEquiv K n h w = 1) (T : Finset (Pl K)) :
    ∃ c : ℂ, ∀ v ∈ V ⊓ ⨅ w ∉ P, eigL μ w (J w) (χ w),
      prj (⨅ w ∉ P, eigL μ w (J w) (χ w)) (rhoF μ (tr T h) v) = c • v := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨1, fun v hv => ?_⟩
    have e : tr (∅ : Finset (Pl K)) h = 1 := by
      unfold tr
      have : AdelicGLn.truncate ∅ (AdelicGLn.finiteRestrictedEquiv K n h) = 1 :=
        RestrictedProduct.ext _ _ fun w => by simp [AdelicGLn.truncate_apply]
      rw [this, map_one]
    rw [e, rhoF_one, one_smul]
    exact Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv.2)
  | insert b T hb ih =>
    obtain ⟨c', hc'⟩ := ih
    by_cases hbP : b ∈ P
    · refine ⟨c', fun v hv => ?_⟩
      rw [tr_insert hb, hP b hbP, map_one, mul_one]
      exact hc' v hv
    · obtain ⟨c, hc⟩ := hr b hbP (AdelicGLn.finiteRestrictedEquiv K n h b)
      refine ⟨c * c', fun v hv => ?_⟩
      have hle : (⨅ w ∉ P, eigL μ w (J w) (χ w)) ≤ eigL μ b (J b) (χ b) :=
        (iInf_le _ b).trans (iInf_le _ hbP)
      have hvb : v ∈ eigL μ b (J b) (χ b) := hle (Submodule.mem_inf.1 hv).2
      have hx : rhoF μ (tr T h) v ∈ V ⊓ eigL μ b (J b) (χ b) := by
        refine ⟨hinv _ _ hv.1, (mem_eigL μ).2 fun g hg => ?_⟩
        have := (mem_eigL μ).1 hvb g hg
        show rhoF μ _ _ = _
        rw [← rhoF_mul, ← tr_comm hb, rhoF_mul]
        change rhoF μ (tr T h) (rhoL μ b g v) = _
        rw [this, map_smul]
      rw [tr_insert hb, tr_comm hb, rhoF_mul, ← prj_prj_of_le μ hle]
      change prj _ (prj _ (rhoL μ b _ _)) = _
      rw [hc _ hx, map_smul, hc' v hv, smul_smul]

end

theorem restScalar : RestScalar := by
  intro K _ _ n μ _ V hV J χ hJ hcof P hr h hP
  classical
  have hinv : ∀ (g : AdelicGLn.FiniteAdelicGL K n), ∀ v ∈ V, rhoF μ g v ∈ V := fun g v hv => hV.inv _ v hv
  have hP' : ∀ w ∈ P, AdelicGLn.finiteRestrictedEquiv K n h w = 1 := fun w hw => by
    rw [← finAt_eq]; exact hP w hw
  have hb1 := Filter.eventually_cofinite.1 hcof
  have hb2 : {v | AdelicGLn.finiteRestrictedEquiv K n h v ∉ GLnLocal.integralGL (v.adicCompletion K) n}.Finite :=
    Filter.eventually_cofinite.1 (AdelicGLn.finiteRestrictedEquiv K n h).2
  set B : Finset (Pl K) := hb1.toFinset ∪ hb2.toFinset with hB
  obtain ⟨c, hc⟩ := scalar_tr μ V hinv J χ P hr h hP' B
  refine ⟨c, fun v hv => ?_⟩
  have hloc : ∀ b ∉ B, rhoL μ b (AdelicGLn.finiteRestrictedEquiv K n h b) v = v := by
    intro b hb
    by_cases hbP : b ∈ P
    · rw [hP' b hbP]
      show rhoF μ (AdelicGLn.localEmbedding b 1) v = v
      rw [map_one, rhoF_one]
    · have h1 : b ∉ hb1.toFinset := fun H => hb (Finset.mem_union_left _ H)
      have h2 : b ∉ hb2.toFinset := fun H => hb (Finset.mem_union_right _ H)
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at h1 h2
      have hvb : v ∈ eigL μ b (J b) (χ b) :=
        ((iInf_le _ b).trans (iInf_le _ hbP) : (⨅ w ∉ P, eigL μ w (J w) (χ w)) ≤ eigL μ b (J b) (χ b))
          (Submodule.mem_inf.1 hv).2
      have := (mem_eigL μ).1 hvb (AdelicGLn.finiteRestrictedEquiv K n h b) (by rw [h1.1]; exact h2)
      rw [this, h1.2]
      simp
  have hfix : ∀ D : Finset (Pl K), Disjoint D B → rhoF μ (tr (D ∪ B) h) v = rhoF μ (tr B h) v := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro _; rw [Finset.empty_union]
    | insert b D hb ih =>
      intro hd
      have hbB : b ∉ B := (Finset.disjoint_insert_left.1 hd).1
      have hbD : b ∉ D ∪ B := by simp [hb, hbB]
      rw [Finset.insert_union, tr_insert hbD, rhoF_mul]
      change rhoF μ _ (rhoL μ b _ v) = _
      rw [hloc b hbB]
      exact ih (Finset.disjoint_insert_left.1 hd).2
  have key : rhoF μ h v = rhoF μ (tr B h) v := by
    have hcl : IsClosed {g : AdelicGLn.FiniteAdelicGL K n | rhoF μ g v = rhoF μ (tr B h) v} :=
      isClosed_eq (continuous_rhoF μ v) continuous_const
    refine hcl.closure_subset_iff.2 subset_rfl (mem_closure_iff_nhds.2 fun U hU => ?_)
    obtain ⟨T, hT, hTU⟩ := exists_tr_mem h hU B
    refine ⟨_, hTU, ?_⟩
    have := hfix (T \ B) Finset.sdiff_disjoint
    rwa [Finset.sdiff_union_of_subset hT] at this
  rw [key]
  exact hc v hv

end UpperTheory.ConvolutionTheory.L1
