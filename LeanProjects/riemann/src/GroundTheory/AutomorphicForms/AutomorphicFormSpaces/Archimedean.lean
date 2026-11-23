import Mathlib
import GroundTheory.AutomorphicForms.GKModules.GKModule
import GroundTheory.AutomorphicForms.GKModules.Garding
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.Reduction
import GroundTheory.GlobalFields.Adele.IntegersLattice

open NumberField NumberField.mixedEmbedding IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

def ArchMatrix : Type _ := Matrix (Fin n) (Fin n) (mixedSpace K)

open scoped Classical in
instance : NormedRing (ArchMatrix K n) := Matrix.linftyOpNormedRing

open scoped Classical in
instance : NormedAlgebra ℝ (ArchMatrix K n) := Matrix.linftyOpNormedAlgebra

instance : FiniteDimensional ℝ (ArchMatrix K n) := by
  change FiniteDimensional ℝ (Matrix (Fin n) (Fin n) (mixedSpace K)); infer_instance

instance : CompleteSpace (ArchMatrix K n) := FiniteDimensional.complete ℝ _

abbrev archGroup : Subgroup (ArchMatrix K n)ˣ := ⊤

abbrev archLie : Submodule ℝ (ArchMatrix K n) := ⊤

instance : NormedAddCommGroup (archLie K n) := Submodule.normedAddCommGroup _

instance : NormedSpace ℝ (archLie K n) := Submodule.normedSpace _

theorem isExpLieAlgebra : IsExpLieAlgebra (archGroup K n) (archLie K n) where
  expUnit_mem _ _ := Subgroup.mem_top _
  exists_nhds := ⟨(expPartialHomeomorph ℝ (ArchMatrix K n)).source,
    (expPartialHomeomorph ℝ (ArchMatrix K n)).open_source,
    zero_mem_expPartialHomeomorph_source ℝ _, subset_rfl, fun _ _ _ => Submodule.mem_top⟩

def archMatrixEquiv : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ≃+* ArchMatrix K n :=
  RingEquiv.mapMatrix (m := Fin n) (InfiniteAdeleRing.ringEquiv_mixedSpace K)

theorem archMatrixEquiv_apply (M : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) (a b : Fin n) :
    (archMatrixEquiv K n M : Matrix (Fin n) (Fin n) (mixedSpace K)) a b =
      InfiniteAdeleRing.ringEquiv_mixedSpace K (M a b) :=
  rfl

theorem continuous_archMatrixEquiv : Continuous (archMatrixEquiv K n) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) =>
    M.map (GroundTheory.Global.homeomorphMixedSpace K)
  exact continuous_id.matrix_map (GroundTheory.Global.homeomorphMixedSpace K).continuous

theorem continuous_archMatrixEquiv_symm : Continuous (archMatrixEquiv K n).symm := by
  have he : ⇑(GroundTheory.Global.homeomorphMixedSpace K).symm =
      ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
    funext x
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [RingEquiv.apply_symm_apply, ← GroundTheory.Global.homeomorphMixedSpace_apply,
      Homeomorph.apply_symm_apply]
  change Continuous fun M : Matrix (Fin n) (Fin n) (mixedSpace K) =>
    M.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
  rw [← he]
  exact continuous_id.matrix_map (GroundTheory.Global.homeomorphMixedSpace K).symm.continuous

def archEquiv : AdelicGLn.InfiniteAdelicGL K n ≃ₜ* archGroup K n :=
  (unitsCongr (archMatrixEquiv K n).toMulEquiv (continuous_archMatrixEquiv K n)
    (continuous_archMatrixEquiv_symm K n)).trans
    { toMulEquiv := Subgroup.topEquiv.symm
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }

def infEmb : archGroup K n →* AdelicGLn.AdelicGL K n :=
  (AdelicGLn.prodEquiv K n).symm.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp (archEquiv K n).symm.toMonoidHom)

def finEmb : AdelicGLn.FiniteAdelicGL K n →* AdelicGLn.AdelicGL K n :=
  (AdelicGLn.prodEquiv K n).symm.toMonoidHom.comp (MonoidHom.inr _ _)

variable {K n}

theorem continuous_infEmb : Continuous (infEmb K n) :=
  (AdelicGLn.prodEquiv K n).symm.continuous.comp
    ((continuous_id.prodMk continuous_const).comp (archEquiv K n).symm.continuous)

theorem continuous_finEmb : Continuous (finEmb K n) :=
  (AdelicGLn.prodEquiv K n).symm.continuous.comp (continuous_const.prodMk continuous_id)

theorem prodEquiv_infEmb (x : archGroup K n) :
    AdelicGLn.prodEquiv K n (infEmb K n x) = ((archEquiv K n).symm x, 1) :=
  (AdelicGLn.prodEquiv K n).apply_symm_apply _

theorem prodEquiv_finEmb (y : AdelicGLn.FiniteAdelicGL K n) :
    AdelicGLn.prodEquiv K n (finEmb K n y) = (1, y) :=
  (AdelicGLn.prodEquiv K n).apply_symm_apply _

theorem infEmb_mul_finEmb_comm (x : archGroup K n) (y : AdelicGLn.FiniteAdelicGL K n) :
    infEmb K n x * finEmb K n y = finEmb K n y * infEmb K n x := by
  apply (AdelicGLn.prodEquiv K n).injective
  simp only [map_mul, prodEquiv_infEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]

theorem infEmb_mul_finEmb (g : AdelicGLn.AdelicGL K n) :
    infEmb K n (archEquiv K n (AdelicGLn.prodEquiv K n g).1) *
      finEmb K n (AdelicGLn.prodEquiv K n g).2 = g := by
  apply (AdelicGLn.prodEquiv K n).injective
  simp only [map_mul, prodEquiv_infEmb, prodEquiv_finEmb, ContinuousMulEquiv.symm_apply_apply,
    Prod.mk_mul_mk, mul_one, one_mul]

theorem infEmb_injective : Function.Injective (infEmb K n) := by
  intro x y hxy
  have := congrArg (fun g => (AdelicGLn.prodEquiv K n g).1) hxy
  simpa [prodEquiv_infEmb] using this

theorem finEmb_injective : Function.Injective (finEmb K n) := by
  intro x y hxy
  have := congrArg (fun g => (AdelicGLn.prodEquiv K n g).2) hxy
  simpa [prodEquiv_finEmb] using this

variable (K n)

def archCompact : Subgroup (archGroup K n) := (Reduction.maxCompact (K := K) (n := n)).comap (infEmb K n)

end AutomorphicForm

end

end GroundTheory.Automorphic
