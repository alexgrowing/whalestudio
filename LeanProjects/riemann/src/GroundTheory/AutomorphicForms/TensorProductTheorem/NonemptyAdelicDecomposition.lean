import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.GKMain
import GroundTheory.AutomorphicForms.TensorProductTheorem.GeneralLinearIntegers
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable

noncomputable section

universe u

namespace GroundTheory.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Set Module Filter IsDedekindDomain NumberField GKTensor RestrictedTensor

section Restrict

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G}
  {V : Type*} [AddCommGroup V] [Module ℂ V]

def IsExpLieAlgebra.GKModule.restrictρ (M : h.GKModule K V) (U : Submodule ℂ V)
    (hρ : ∀ X, ∀ u ∈ U, M.ρ X u ∈ U) : h.lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ U where
  toFun X := (M.ρ X).restrict (hρ X)
  map_add' X Y := LinearMap.ext fun u => Subtype.ext (by simp)
  map_smul' r X := LinearMap.ext fun u => Subtype.ext (by simp)
  map_lie' {X Y} := LinearMap.ext fun u => Subtype.ext (by
    simp [LieHom.map_lie, LieRing.of_associative_ring_bracket])

def IsExpLieAlgebra.GKModule.restrictσ (M : h.GKModule K V) (U : Submodule ℂ V)
    (hσ : ∀ k, ∀ u ∈ U, M.σ k u ∈ U) : Representation ℂ K U where
  toFun k := (M.σ k).restrict (hσ k)
  map_one' := LinearMap.ext fun u => Subtype.ext (by simp)
  map_mul' k₁ k₂ := LinearMap.ext fun u => Subtype.ext (by simp)

def IsExpLieAlgebra.GKModule.restrict (M : h.GKModule K V) (U : Submodule ℂ V)
    (hρ : ∀ X, ∀ u ∈ U, M.ρ X u ∈ U) (hσ : ∀ k, ∀ u ∈ U, M.σ k u ∈ U) : h.GKModule K U :=
  IsExpLieAlgebra.GKModule.comap h M U.subtype U.injective_subtype (M.restrictρ U hρ)
    (M.restrictσ U hσ) (fun _ _ => rfl) (fun _ _ => rfl)

end Restrict

namespace AutomorphicForm

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

instance compactSpace_archCompact : CompactSpace (archCompact K n) :=
  isCompact_iff_compactSpace.1 (isCompact_archCompact K n)

abbrev AdelicGKModule (V : Type*) [AddCommGroup V] [Module ℂ V] :=
  GKLModule (isExpLieAlgebra K n) (archCompact K n) (AdelicGLn.FiniteAdelicGL K n) V

variable {K n}

structure AdelicDecomposition {V : Type u} [AddCommGroup V] [Module ℂ V]
    (Mx : AdelicGKModule K n V) where

  toDecomposition : Mx.Decomposition

  finite : AdelicGLn.TensorDecomposition K n toDecomposition.π₂

theorem nonempty_adelicDecomposition {V : Type u} [AddCommGroup V] [Module ℂ V]
    (Mx : AdelicGKModule K n V) (hirr : Mx.IsIrreducible) (hadm : Mx.IsAdmissible) :
    Nonempty (AdelicDecomposition Mx) := by
  obtain ⟨D⟩ := Mx.nonempty_decomposition hirr hadm
  obtain ⟨T⟩ := AdelicGLn.nonempty_tensorDecomposition D.isAdmissible₂ D.isIrreducible₂
  exact ⟨⟨D, T⟩⟩

def _root_.GroundTheory.Automorphic.AdelicGLn.TensorDecomposition.transport {V V' : Type u}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) V}
    {ρ' : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) V'} (E : ρ.Equiv ρ')
    (T : AdelicGLn.TensorDecomposition K n ρ') : AdelicGLn.TensorDecomposition K n ρ :=
  { T with equiv := E.trans T.equiv }

namespace AdelicDecomposition

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {Mx : AdelicGKModule K n V}

theorem nonempty_equiv_arch (D D' : AdelicDecomposition Mx) :
    Nonempty (D.toDecomposition.π₁.rep.Equiv D'.toDecomposition.π₁.rep) :=
  GKLModule.Decomposition.nonempty_equiv_arch _ _

theorem nonempty_equiv_local (D D' : AdelicDecomposition Mx) (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty ((D.finite.π v).Equiv (D'.finite.π v)) := by
  obtain ⟨E⟩ := GKLModule.Decomposition.nonempty_equiv_fin D.toDecomposition D'.toDecomposition
  exact AdelicGLn.TensorDecomposition.nonempty_equiv D.finite (D'.finite.transport E) v

end AdelicDecomposition

variable (K n) in

def cuspSubmodule (U : Submodule ℂ (cuspForms K n))
    (hρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp K n).ρ X φ ∈ U)
    (hσ : ∀ k, ∀ φ ∈ U, (gkModuleCusp K n).σ k φ ∈ U)
    (hτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U) : AdelicGKModule K n U where
  gk := (gkModuleCusp K n).restrict U hρ hσ
  τ := (⟨U, hτ⟩ : Subrepresentation (finRepCusp K n)).toRepresentation
  comm_ρ X g := LinearMap.ext fun φ => Subtype.ext
    (gkModuleCusp_ρ_finRepCusp X g φ)
  comm_σ k g := LinearMap.ext fun φ => Subtype.ext
    (gkModuleCusp_σ_finRepCusp k g φ)

variable (K n) in

structure CuspidalAutomorphicRep where

  carrier : Submodule ℂ (cuspForms K n)
  stable_ρ : ∀ X, ∀ φ ∈ carrier, (gkModuleCusp K n).ρ X φ ∈ carrier
  stable_σ : ∀ k, ∀ φ ∈ carrier, (gkModuleCusp K n).σ k φ ∈ carrier
  stable_τ : ∀ g, ∀ φ ∈ carrier, finRepCusp K n g φ ∈ carrier
  isIrreducible : (cuspSubmodule K n carrier stable_ρ stable_σ stable_τ).IsIrreducible
  exists_compl : ∃ C : Submodule ℂ (cuspForms K n), IsCompl carrier C ∧
    (∀ X, ∀ φ ∈ C, (gkModuleCusp K n).ρ X φ ∈ C) ∧ (∀ k, ∀ φ ∈ C, (gkModuleCusp K n).σ k φ ∈ C) ∧
    ∀ g, ∀ φ ∈ C, finRepCusp K n g φ ∈ C

namespace CuspidalAutomorphicRep

abbrev toModule (π : CuspidalAutomorphicRep K n) : AdelicGKModule K n π.carrier :=
  cuspSubmodule K n π.carrier π.stable_ρ π.stable_σ π.stable_τ

theorem nonempty_adelicDecomposition (π : CuspidalAutomorphicRep K n)
    (hadm : π.toModule.IsAdmissible) : Nonempty (AdelicDecomposition π.toModule) :=
  AutomorphicForm.nonempty_adelicDecomposition π.toModule π.isIrreducible hadm

end CuspidalAutomorphicRep

end AutomorphicForm

end GroundTheory.Automorphic
