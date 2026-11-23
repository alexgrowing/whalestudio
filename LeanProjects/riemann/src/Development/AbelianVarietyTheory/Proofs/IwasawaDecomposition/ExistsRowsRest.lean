import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerProductPositiveDefinite

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.SmallRows

def RamSp {B : Base} (C : Cols B) (u : B.Word) : Type := (C.mem u).A.Mram

instance {B : Base} (C : Cols B) (u : B.Word) : AddCommGroup (RamSp C u) :=
  inferInstanceAs (AddCommGroup (C.mem u).A.Mram)
instance {B : Base} (C : Cols B) (u : B.Word) : Module ℂ (RamSp C u) :=
  inferInstanceAs (Module ℂ (C.mem u).A.Mram)
instance {B : Base} (C : Cols B) (u : B.Word) : FiniteDimensional ℂ (RamSp C u) :=
  haveI := (C.mem u).A.Mu0_fd
  Submodule.finiteDimensional_of_le (S₁ := (C.mem u).A.Mram) (S₂ := (C.mem u).A.Mu0) inf_le_left

def ramEq {B : Base} (C : Cols B) (u : B.Word) : RamSp C u ≃ₗ[ℂ] (C.mem u).A.Mram := LinearEquiv.refl ℂ _

@[reducible] def core {B : Base} (C : Cols B) (u : B.Word)
    (hs : ∀ φ ψ : (C.mem u).A.Mu0, (C.fm u).ipC 0 ψ φ = star ((C.fm u).ipC 0 φ ψ))
    (hp : ∀ φ : (C.mem u).A.Mu0, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re) :
    InnerProductSpace.Core ℂ (RamSp C u) where
  inner x y := (C.fm u).ipC 0 (ramEq C u x).1 (ramEq C u y).1
  conj_inner_symm x y :=
    (hs ⟨(ramEq C u y).1, (ramEq C u y).2.1⟩ ⟨(ramEq C u x).1, (ramEq C u x).2.1⟩).symm
  re_inner_nonneg x := by
    by_cases hx : (ramEq C u x).1 = 0
    · simp [hx, MemberForms.ipC]
    · exact (hp ⟨(ramEq C u x).1, (ramEq C u x).2.1⟩ (fun h => hx (congrArg Subtype.val h))).le
  add_left x y z := by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [MemberForms.ipC, map_smul, Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  definite x hx := by
    by_contra h0
    have h1 : (ramEq C u x).1 ≠ 0 := fun h1 => h0 ((ramEq C u).injective (Subtype.ext (by simpa using h1)))
    have := hp ⟨(ramEq C u x).1, (ramEq C u x).2.1⟩ (fun h => h1 (congrArg Subtype.val h))
    rw [show (C.fm u).ipC 0 (ramEq C u x).1 (ramEq C u x).1 = 0 from hx] at this
    simp at this

def stdCongr {a b : ℕ} (h : a = b) : EuclideanSpace ℂ (Fin a) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin b) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr h)

def stdLat (O : Type) [CommRing O] (φ : O →+* ℂ) (a : ℕ) : Rows.OLat O φ (EuclideanSpace ℂ (Fin a)) where
  gen := by classical exact Finset.univ.image (EuclideanSpace.basisFun (Fin a) ℂ).toBasis
  span_top := by
    classical
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact (EuclideanSpace.basisFun (Fin a) ℂ).toBasis.span_eq

end GlobalTheory.Mem.SmallRows

end
