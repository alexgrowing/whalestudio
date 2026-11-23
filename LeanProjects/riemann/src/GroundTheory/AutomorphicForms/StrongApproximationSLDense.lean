import Mathlib
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.AutomorphicForms.StrongApproximationSLElementary
import GroundTheory.GlobalFields.Adele.Approximation
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

namespace AdelicGLn

variable (K : Type*) [Field K] [NumberField K]

theorem denseRange_algebraMap_finiteAdeleRing :
    DenseRange (algebraMap K (FiniteAdeleRing (𝓞 K) K)) := by
  intro a
  refine mem_closure_iff_nhds.2 fun U hU => ?_
  have hW : (fun y => a + y) ⁻¹' U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  set c : K := algebraMap (𝓞 K) K d
  have hc : c ≠ 0 := by
    simpa [c] using hd0
  set x := algebraMap K (FiniteAdeleRing (𝓞 K) K)
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 K) (K := K)
    (x c⁻¹ * a)
  have hmem := hd _ (neg_mem hk)
  have hcc : x c * x c⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  refine ⟨x (c * k), ?_, c * k, rfl⟩
  have heq : a + x c * -(x c⁻¹ * a - x k) = x (c * k) := by
    rw [map_mul]
    linear_combination (-a) * hcc
  rw [← heq]
  exact hmem

variable (n : ℕ)

def finiteDiagonal : GL (Fin n) K →* FiniteAdelicGL K n :=
  Matrix.GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing (𝓞 K) K))

@[simp]
theorem finiteDiagonal_apply (γ : GL (Fin n) K) (a b : Fin n) :
    finiteDiagonal K n γ a b = algebraMap K (FiniteAdeleRing (𝓞 K) K) (γ a b) :=
  rfl

theorem det_finiteDiagonal (γ : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.det (finiteDiagonal K n γ) =
      FiniteAdeleRing.unitEmbedding (𝓞 K) K (Matrix.GeneralLinearGroup.det γ) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, FiniteAdeleRing.unitEmbedding_apply]
  rw [RingHom.map_det]
  rfl

def finiteSL : Subgroup (FiniteAdelicGL K n) :=
  (Matrix.GeneralLinearGroup.det : FiniteAdelicGL K n →* (FiniteAdeleRing (𝓞 K) K)ˣ).ker

theorem mem_finiteSL {g : FiniteAdelicGL K n} :
    g ∈ finiteSL K n ↔ Matrix.GeneralLinearGroup.det g = 1 :=
  MonoidHom.mem_ker

def rationalFiniteSL : Subgroup (FiniteAdelicGL K n) :=
  (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker.map (finiteDiagonal K n)

theorem rationalFiniteSL_le_finiteSL : rationalFiniteSL K n ≤ finiteSL K n := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [mem_finiteSL, det_finiteDiagonal, MonoidHom.mem_ker.1 hγ, map_one]

theorem continuous_transvectionGL {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (i j : Fin n) (h : i ≠ j) :
    Continuous fun c : R => transvectionGL (Fin n) R ⟨i, j, h, c⟩ := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun c : R => transvection i j c
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · show Continuous fun c : R => transvection i j (-c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

theorem transvectionGL_mem_topologicalClosure (t : TransvectionStruct (Fin n) (FiniteAdeleRing (𝓞 K) K)) :
    transvectionGL (Fin n) _ t ∈ (rationalFiniteSL K n).topologicalClosure := by
  obtain ⟨i, j, h, c⟩ := t
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
  refine map_mem_closure
    (f := fun c : FiniteAdeleRing (𝓞 K) K => transvectionGL (Fin n) _ ⟨i, j, h, c⟩)
    (continuous_transvectionGL n i j h)
    (denseRange_algebraMap_finiteAdeleRing K c) ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨transvectionGL (Fin n) K ⟨i, j, h, k⟩,
    elementarySubgroup_le_ker_det (transvectionGL_mem_elementarySubgroup _), ?_⟩
  ext a b
  simp only [finiteDiagonal_apply, coe_transvectionGL, TransvectionStruct.toMatrix_mk, transvection,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem elementarySubgroup_le_topologicalClosure :
    elementarySubgroup (Fin n) (FiniteAdeleRing (𝓞 K) K) ≤
      (rationalFiniteSL K n).topologicalClosure := by
  rw [elementarySubgroup, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  exact transvectionGL_mem_topologicalClosure K n t

variable {K n}

abbrev FiniteRestrictedGL (K : Type*) [Field K] [NumberField K] (n : ℕ) : Type _ :=
  Πʳ v : HeightOneSpectrum (𝓞 K),
    [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n]

theorem finiteAdele_add_apply (x y : FiniteAdeleRing (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    (x + y) v = x v + y v :=
  rfl

theorem finiteAdele_one_apply (v : HeightOneSpectrum (𝓞 K)) :
    (1 : FiniteAdeleRing (𝓞 K) K) v = 1 :=
  rfl

theorem finiteAdele_zero_apply (v : HeightOneSpectrum (𝓞 K)) :
    (0 : FiniteAdeleRing (𝓞 K) K) v = 0 :=
  rfl

open Classical in

def finiteAdeleSingleAdd (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) :
    FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v c

open Classical in
theorem finiteAdeleSingleAdd_apply (v w : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) :
    finiteAdeleSingleAdd v c w = Pi.single (M := fun u : HeightOneSpectrum (𝓞 K) =>
      u.adicCompletion K) v c w :=
  rfl

open Classical in

def localEmbedding (v : HeightOneSpectrum (𝓞 K)) : GL (Fin n) (v.adicCompletion K) →* FiniteAdelicGL K n where
  toFun x := (finiteRestrictedEquiv K n).symm
    (RestrictedProduct.mulSingle (fun w => GLnLocal.integralGL (w.adicCompletion K) n) v x)
  map_one' := by simp
  map_mul' x y := by rw [RestrictedProduct.mulSingle_mul, map_mul]

theorem finiteRestrictedEquiv_symm_apply (y : FiniteRestrictedGL K n) (w : HeightOneSpectrum (𝓞 K))
    (a b : Fin n) :
    ((finiteRestrictedEquiv K n).symm y : FiniteAdelicGL K n) a b w =
      (y w : GL (Fin n) (w.adicCompletion K)) a b := by
  rw [← finiteRestrictedEquiv_apply, ContinuousMulEquiv.apply_symm_apply]

open Classical in

theorem localEmbedding_transvectionGL (v : HeightOneSpectrum (𝓞 K))
    (t : TransvectionStruct (Fin n) (v.adicCompletion K)) :
    localEmbedding v (transvectionGL _ _ t) = transvectionGL (Fin n) (FiniteAdeleRing (𝓞 K) K)
      ⟨t.i, t.j, t.hij, finiteAdeleSingleAdd v t.c⟩ := by
  refine Units.ext <| Matrix.ext fun a b => FiniteAdeleRing.ext K fun w => ?_
  change ((finiteRestrictedEquiv K n).symm _ : FiniteAdelicGL K n) a b w = _
  rw [finiteRestrictedEquiv_symm_apply]
  simp only [coe_transvectionGL, TransvectionStruct.toMatrix, transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply, RestrictedProduct.coe_mulSingle_apply]
  by_cases hw : w = v
  · subst hw
    simp only [Pi.mulSingle_eq_same, coe_transvectionGL, TransvectionStruct.toMatrix, transvection,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : finiteAdeleSingleAdd w t.c w = t.c := by
      rw [finiteAdeleSingleAdd_apply, Pi.single_eq_same]
    split_ifs <;>
      simp only [finiteAdele_add_apply, finiteAdele_one_apply, finiteAdele_zero_apply, h1, add_zero,
        zero_add]
  · have h0 : finiteAdeleSingleAdd v t.c w = 0 := by
      rw [finiteAdeleSingleAdd_apply, Pi.single_eq_of_ne hw]
    rw [Pi.mulSingle_eq_of_ne hw, Units.val_one, Matrix.one_apply]
    split_ifs <;>
      simp only [finiteAdele_add_apply, finiteAdele_one_apply, finiteAdele_zero_apply, h0, add_zero]

theorem localEmbedding_mem_elementarySubgroup (v : HeightOneSpectrum (𝓞 K))
    {x : GL (Fin n) (v.adicCompletion K)} (hx : Matrix.GeneralLinearGroup.det x = 1) :
    localEmbedding v x ∈ elementarySubgroup (Fin n) (FiniteAdeleRing (𝓞 K) K) := by
  have hle : (elementarySubgroup (Fin n) (v.adicCompletion K)).map (localEmbedding v) ≤
      elementarySubgroup (Fin n) (FiniteAdeleRing (𝓞 K) K) := by
    rw [elementarySubgroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    rw [localEmbedding_transvectionGL]
    exact transvectionGL_mem_elementarySubgroup _
  exact hle ⟨x, mem_elementarySubgroup_of_det_eq_one hx, rfl⟩

def evalFinite (v : HeightOneSpectrum (𝓞 K)) : FiniteAdeleRing (𝓞 K) K →+* v.adicCompletion K where
  toFun x := x v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem det_finiteRestrictedEquiv_apply (g : FiniteAdelicGL K n) (v : HeightOneSpectrum (𝓞 K)) :
    (Matrix.GeneralLinearGroup.det (finiteRestrictedEquiv K n g v : GL (Fin n) (v.adicCompletion K)) :
      v.adicCompletion K) = (Matrix.GeneralLinearGroup.det g : FiniteAdeleRing (𝓞 K) K) v := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  change _ = evalFinite v _
  rw [RingHom.map_det]
  rfl

open Classical in

def truncate (S : Finset (HeightOneSpectrum (𝓞 K))) (y : FiniteRestrictedGL K n) :
    FiniteRestrictedGL K n where
  val v := if v ∈ S then y v else 1
  property := by
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
    rw [if_neg (by simpa using hv)]
    exact one_mem (GLnLocal.integralGL (v.adicCompletion K) n)

open Classical in
theorem truncate_apply (S : Finset (HeightOneSpectrum (𝓞 K))) (y : FiniteRestrictedGL K n)
    (v : HeightOneSpectrum (𝓞 K)) : truncate S y v = if v ∈ S then y v else 1 :=
  rfl

open Classical in
theorem truncate_insert {S : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ S) (y : FiniteRestrictedGL K n) :
    truncate (insert v S) y = truncate S y *
      RestrictedProduct.mulSingle (fun w => GLnLocal.integralGL (w.adicCompletion K) n) v (y v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  rw [RestrictedProduct.mul_apply, truncate_apply, truncate_apply,
    RestrictedProduct.coe_mulSingle_apply]
  by_cases hw : w = v
  · subst hw
    simp [hv]
  · simp [hw]

theorem finiteRestrictedEquiv_symm_truncate_mem {g : FiniteAdelicGL K n}
    (hg : Matrix.GeneralLinearGroup.det g = 1) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (finiteRestrictedEquiv K n).symm (truncate S (finiteRestrictedEquiv K n g)) ∈
      elementarySubgroup (Fin n) (FiniteAdeleRing (𝓞 K) K) := by
  classical
  have hdet : ∀ v, Matrix.GeneralLinearGroup.det
      (finiteRestrictedEquiv K n g v : GL (Fin n) (v.adicCompletion K)) = 1 := fun v => by
    ext
    rw [det_finiteRestrictedEquiv_apply, hg]
    rfl
  induction S using Finset.induction_on with
  | empty =>
    have : truncate ∅ (finiteRestrictedEquiv K n g) = 1 :=
      RestrictedProduct.ext _ _ fun w => by simp [truncate_apply]
    rw [this, map_one]
    exact one_mem _
  | insert v S hv ih =>
    rw [truncate_insert hv, map_mul]
    exact mul_mem ih (localEmbedding_mem_elementarySubgroup v (hdet v))

theorem mem_closure_elementarySubgroup {g : FiniteAdelicGL K n}
    (hg : Matrix.GeneralLinearGroup.det g = 1) :
    g ∈ closure (elementarySubgroup (Fin n) (FiniteAdeleRing (𝓞 K) K) : Set (FiniteAdelicGL K n)) := by
  classical
  set Φ := finiteRestrictedEquiv K n
  set y := Φ g
  have hopen : ∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) :=
    fun v => GLnLocal.isOpen_integralGL (v.adicCompletion K) n
  rw [mem_closure_iff_nhds]
  intro U hU
  have hV : Φ.symm ⁻¹' U ∈ 𝓝 y :=
    Φ.symm.continuous.continuousAt.preimage_mem_nhds
      (by convert hU using 2; exact Φ.symm_apply_apply g)
  have : Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))) :=
    ⟨hopen⟩
  have hW : (fun w => y * w) ⁻¹' (Φ.symm ⁻¹' U) ∈ 𝓝 (1 : FiniteRestrictedGL K n) :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hV)
  have h1 : (1 : FiniteRestrictedGL K n) =
      RestrictedProduct.structureMap _ (fun v : HeightOneSpectrum (𝓞 K) => (GLnLocal.integralGL (v.adicCompletion K) n :
        Set (GL (Fin n) (v.adicCompletion K)))) cofinite 1 := rfl
  rw [h1, RestrictedProduct.nhds_eq_map_structureMap hopen, Filter.mem_map, nhds_pi,
    Filter.mem_pi] at hW
  obtain ⟨I, hI, t, ht, hsub⟩ := hW
  have hbad : {v | y v ∉ GLnLocal.integralGL (v.adicCompletion K) n}.Finite :=
    Filter.eventually_cofinite.1 y.2
  set S : Finset (HeightOneSpectrum (𝓞 K)) := hI.toFinset ∪ hbad.toFinset
  have hmem : ∀ v, (y⁻¹ * truncate S y) v ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
    intro v
    rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, truncate_apply]
    split_ifs with hv
    · rw [inv_mul_cancel]
      exact one_mem _
    · have : y v ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
        by_contra h
        exact hv (Finset.mem_union_right _ (hbad.mem_toFinset.2 h))
      rw [mul_one]
      exact inv_mem this
  let w' : Π v : HeightOneSpectrum (𝓞 K),
      (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) :=
    fun v => ⟨(y⁻¹ * truncate S y) v, hmem v⟩
  have hw' : RestrictedProduct.structureMap _ _ cofinite w' = y⁻¹ * truncate S y :=
    RestrictedProduct.ext _ _ fun v => rfl
  have hw'I : w' ∈ I.pi t := by
    intro v hv
    have hvS : v ∈ S := Finset.mem_union_left _ (hI.mem_toFinset.2 hv)
    have : w' v = 1 := Subtype.ext <| by
      change (y⁻¹ * truncate S y) v = 1
      rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, truncate_apply, if_pos hvS,
        inv_mul_cancel]
    rw [this]
    exact mem_of_mem_nhds (ht v)
  have hU' := hsub hw'I
  simp only [Set.mem_preimage, hw', mul_inv_cancel_left] at hU'
  exact ⟨_, hU', finiteRestrictedEquiv_symm_truncate_mem hg S⟩

variable (K n)

theorem finiteSL_le_topologicalClosure :
    finiteSL K n ≤ (rationalFiniteSL K n).topologicalClosure := fun _ hg =>
  closure_minimal (elementarySubgroup_le_topologicalClosure K n)
    (Subgroup.isClosed_topologicalClosure _) (mem_closure_elementarySubgroup ((mem_finiteSL K n).1 hg))

theorem dense_rationalFiniteSL :
    Dense (((rationalFiniteSL K n).subgroupOf (finiteSL K n) : Subgroup (finiteSL K n)) :
      Set (finiteSL K n)) := by
  rw [Topology.IsInducing.subtypeVal.dense_iff]
  intro x
  have hx := finiteSL_le_topologicalClosure K n x.2
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hx
  refine closure_mono (fun g hg => ?_) hx
  exact ⟨⟨g, rationalFiniteSL_le_finiteSL K n hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩

theorem exists_finiteDiagonal_mem_nhds {g : FiniteAdelicGL K n}
    (hg : Matrix.GeneralLinearGroup.det g = 1) {U : Set (FiniteAdelicGL K n)} (hU : U ∈ 𝓝 g) :
    ∃ γ : GL (Fin n) K, Matrix.GeneralLinearGroup.det γ = 1 ∧ finiteDiagonal K n γ ∈ U := by
  have h := finiteSL_le_topologicalClosure K n ((mem_finiteSL K n).2 hg)
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, mem_closure_iff_nhds] at h
  obtain ⟨_, hxU, γ, hγ, rfl⟩ := h U hU
  exact ⟨γ, MonoidHom.mem_ker.1 hγ, hxU⟩

end AdelicGLn

end

end GroundTheory.Automorphic
