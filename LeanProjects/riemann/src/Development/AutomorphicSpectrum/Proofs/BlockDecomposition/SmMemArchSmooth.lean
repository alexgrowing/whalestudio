import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable

set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open IsDedekindDomain
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.ArchSmooth

open AutomorphicForm

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

def cMap : mixedEmbedding.mixedSpace E →ₗ[ℝ] Cinf E where
  toFun z := fun w => z.2 ⟨w, IsTotallyComplex.isComplex w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cMap_ringEquiv (x : InfiniteAdeleRing E) :
    cMap E (InfiniteAdeleRing.ringEquiv_mixedSpace E x) = (infEq E).symm x := by
  funext w
  change (InfiniteAdeleRing.ringEquiv_mixedSpace E x).2 ⟨w, IsTotallyComplex.isComplex w⟩ = _
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  rfl

def mMap : ArchMatrix E a →ₗ[ℝ] Lie E a where
  toFun x := fun i j => cMap E ((x : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) i j)
  map_add' x y := by
    funext i j
    exact map_add (cMap E) _ _
  map_smul' c x := by
    funext i j
    exact map_smul (cMap E) c _

def toGL (u : archGroup E a) : GL (Fin a) (Cinf E) :=
  Matrix.GeneralLinearGroup.map (infEq E).symm.toRingHom ((archEquiv E a).symm u)

theorem toL_toGL (u : archGroup E a) :
    toL (toGL E a u).val = mMap E a ((u : (ArchMatrix E a)ˣ) : ArchMatrix E a) := by
  obtain ⟨b, rfl⟩ := (archEquiv E a).surjective u
  funext i j
  simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
  exact (cMap_ringEquiv E (b i j)).symm

theorem infEmb_eq (u : archGroup E a) : infEmb E a u = infGL E a (toGL E a u) := by
  apply ga_ext
  · rw [pInf_infGL]
    ext i j : 2
    have h := congrArg (fun p => (p.1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j) (prodEquiv_infEmb u)
    exact congrArg (infEq E).symm h
  · rw [pFin_infGL]
    ext i j : 2
    exact congrArg (fun p => (p.2 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i j) (prodEquiv_infEmb u)

theorem archSlice_eq (φ : GA E a → ℂ) (g : GA E a) (u : archGroup E a) :
    archSlice φ g u = chart φ g (mMap E a ((u : (ArchMatrix E a)ˣ) : ArchMatrix E a)) := by
  rw [← toL_toGL, chart_val, archSlice_apply, infEmb_eq]

theorem sm_mem_archSmooth (φ : Sm E a) : φ.1 ∈ AutomorphicForm.archSmooth E a := by
  intro g
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g'
  let L : ArchMatrix E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap (mMap E a)
  let c : ArchMatrix E a := ((g' : (ArchMatrix E a)ˣ) : ArchMatrix E a)
  let F : archLie E a → ArchMatrix E a := fun Y => c * NormedSpace.exp (Y : ArchMatrix E a)
  have hF : ContDiff ℝ ∞ F :=
    contDiff_const.mul ((contDiff_exp ℝ (ArchMatrix E a)).comp (archLie E a).subtypeL.contDiff)
  have hs : ContDiff ℝ ∞ fun Y => L (F Y) := L.contDiff.comp hF
  have hmem : ∀ Y, L (F Y) ∈ invSet E a := fun Y => by
    have : L (F Y) = toL (toGL E a (g' * (isExpLieAlgebra E a).expG Y)).val := (toL_toGL E a (g' * (isExpLieAlgebra E a).expG Y)).symm
    rw [this]
    exact val_mem_invSet _
  have hc := (φ.2 g).comp_contDiff hs hmem
  have e : (fun Y : archLie E a => archSlice φ.1 g (g' * (isExpLieAlgebra E a).expG Y)) =
      chart φ.1 g ∘ fun Y => L (F Y) :=
    funext fun Y => archSlice_eq E a φ.1 g _
  change ContDiff ℝ ∞ (fun Y : archLie E a => archSlice φ.1 g (g' * (isExpLieAlgebra E a).expG Y))
  rw [e]
  exact hc

end GlobalTheory.CompanionTheory.ArchSmooth
