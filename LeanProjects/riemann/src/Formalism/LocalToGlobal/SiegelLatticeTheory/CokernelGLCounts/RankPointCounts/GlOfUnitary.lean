import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FmatMulInv

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {D : D7} (X : HidaSetting D)

def matOf (γ : (VS D).V →ₗ[D.host.E] (VS D).V) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  (LinearMap.toMatrix X.bas X.bas γ).map X.ιE.symm

theorem matOf_comp (γ δ : (VS D).V →ₗ[D.host.E] (VS D).V) : matOf X (γ ∘ₗ δ) = matOf X γ * matOf X δ := by
  unfold matOf
  rw [LinearMap.toMatrix_comp X.bas X.bas X.bas]
  simpa using map_mul X.ιE.symm.mapMatrix (LinearMap.toMatrix X.bas X.bas γ) (LinearMap.toMatrix X.bas X.bas δ)

theorem matOf_id : matOf X LinearMap.id = 1 := by
  unfold matOf
  rw [LinearMap.toMatrix_id]
  simp

theorem crd_apply (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    X.crd (γ y) = matOf X γ *ᵥ X.crd y := by
  funext i
  show X.ιE.symm (X.bas.repr (γ y) i) = _
  rw [← LinearMap.toMatrix_mulVec_repr X.bas X.bas γ y]
  exact RingHom.map_mulVec (X.ιE.symm : D.host.E →+* X.B.I.E) _ _ i

theorem crd_inj : Function.Injective (X.crd) := fun _ _ h =>
  X.bas.repr.injective (Finsupp.ext fun i => X.ιE.symm.injective (congrFun h i))

def glOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : GL (Fin X.B.I.n) X.B.I.E where
  val := matOf X γ.toLinearMap
  inv := matOf X γ.symm.toLinearMap
  val_inv := by
    rw [← matOf_comp, ← matOf_id X]
    congr 1
    exact LinearMap.ext fun x => by simp
  inv_val := by
    rw [← matOf_comp, ← matOf_id X]
    congr 1
    exact LinearMap.ext fun x => by simp

theorem matE_glOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : matE X (glOf X γ) = γ := by
  apply LinearEquiv.ext
  intro y
  apply crd_inj X
  rw [matE_crd]
  exact (crd_apply X γ.toLinearMap y).symm

theorem matE_inj {M M' : GL (Fin X.B.I.n) X.B.I.E} (h : matE X M = matE X M') : M = M' := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← LatDictK.crd_vOf X x, ← matE_crd, ← matE_crd, h]

theorem hT_coord (x y : (VS D).V) :
    (VS D).hT x y = star (X.bas.equivFun x) ⬝ᵥ (mapM X X.B.I.J *ᵥ X.bas.equivFun y) := by
  rw [hT_expand X x y]
  simp only [← X.J_eq]
  rw [qform]

theorem form_ext {m : Type} [Fintype m] [DecidableEq m] {P Q : Matrix m m D.host.E}
    (h : ∀ a c : m → D.host.E, star a ⬝ᵥ (P *ᵥ c) = star a ⬝ᵥ (Q *ᵥ c)) : P = Q := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  have hs : star (Pi.single i (1 : D.host.E) : m → D.host.E) = Pi.single i 1 := by
    ext k
    by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  rw [hs] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem mapM_cT (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    mapM X (Formalism.UG.cT (starRingEnd X.B.I.E) M) = (mapM X M)ᴴ := by
  ext i j
  simp only [mapM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply, Formalism.UG.cT,
    Matrix.transpose_apply, starRingEnd_apply, RingEquiv.coe_toRingHom, X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]

theorem glOf_unitary (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    glOf X γ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
  set A := mapM X ((glOf X γ : GL _ _) : Matrix _ _ _) with hA
  have hrep : ∀ y, X.bas.equivFun (γ y) = A *ᵥ X.bas.equivFun y := by
    intro y
    rw [hA, ← matE_repr, matE_glOf]
  have key : Aᴴ * mapM X X.B.I.J * A = mapM X X.B.I.J := by
    apply form_ext
    intro a c
    have h1 := hγ (X.bas.equivFun.symm a) (X.bas.equivFun.symm c)
    rw [hT_coord, hT_coord, hrep, hrep, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    rw [← h1, Matrix.star_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  show Formalism.UG.cT (starRingEnd X.B.I.E) ((glOf X γ : GL _ _) : Matrix _ _ _) * X.B.I.J * ((glOf X γ : GL _ _) : Matrix _ _ _) =
    X.B.I.J
  apply Matrix.map_injective X.ιE.injective
  show mapM X _ = mapM X _
  rw [map_mul, map_mul, mapM_cT]
  exact key

end Mat

section UJ

theorem uj_bc {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m]
    (φ : A →+* B) (σA : A →+* A) (σB : B →+* B) (hσ : ∀ a, φ (σA a) = σB (φ a)) (JA : Matrix m m A)
    (g : GL m A) (hg : g ∈ Formalism.UG.UJ σA JA) : Formalism.UG.bc φ g ∈ Formalism.UG.UJ σB (JA.map φ) := by
  have hg' : Formalism.UG.cT σA (g : Matrix m m A) * JA * (g : Matrix m m A) = JA := hg
  show Formalism.UG.cT σB ((g : Matrix m m A).map φ) * JA.map φ * (g : Matrix m m A).map φ = JA.map φ
  have hc : Formalism.UG.cT σB ((g : Matrix m m A).map φ) = (Formalism.UG.cT σA (g : Matrix m m A)).map φ := by
    ext i j
    simp [Formalism.UG.cT, hσ]
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']

end UJ

section AH

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def AH (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {γ | γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, γ (X.eX a) = X.eX a) ∧ (∀ a, γ (X.fY a) = X.fY a) ∧
    γ (X.zu u) = X.zu u ∧ Formalism.HermitianLatticesTheory.gmap γ Λ = Λ}

theorem crd_fix_of (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (he : ∀ a, γ (X.eX a) = X.eX a)
    (hf : ∀ a, γ (X.fY a) = X.fY a) (hz : γ (X.zu u) = X.zu u) (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    (glOf X γ : Matrix _ _ _) *ᵥ y = y := by
  have hc : ∀ v, γ v = v → (glOf X γ : Matrix _ _ _) *ᵥ X.crd v = X.crd v := fun v hv => by
    rw [← matE_crd, matE_glOf, hv]
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz'
  · exact hc _ (he a)
  · exact hc _ (hf a)
  · rw [Set.mem_singleton_iff] at hz'
    rw [hz']
    exact hc _ hz

def gOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (he : ∀ a, γ (X.eX a) = X.eX a) (hf : ∀ a, γ (X.fY a) = X.fY a) (hz : γ (X.zu u) = X.zu u) : Hfin X u :=
  ⟨⟨Formalism.UG.bc (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (glOf X γ),
    uj_bc _ _ _ (fun a => by simp [Formalism.UG.sigR, Formalism.UG.inclE]; rfl) X.B.I.J _ (glOf_unitary X γ hγ)⟩,
    fun y hy => by
      show ((glOf X γ : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F))) *ᵥ incl X.B.I y =
        incl X.B.I y
      funext i
      have := (RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (glOf X γ : Matrix _ _ _) y i).symm
      rw [crd_fix_of X u γ he hf hz y hy] at this
      exact this⟩

theorem fmat_gOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (he : ∀ a, γ (X.eX a) = X.eX a) (hf : ∀ a, γ (X.fY a) = X.fY a) (hz : γ (X.zu u) = X.zu u) :
    X.B.I.fmat ((gOf X u γ hγ he hf hz : Hfin X u) : X.B.I.Gf) =
      (glOf X γ : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) := rfl

end AH

end Formalism.L2.SG.RhoPf
