import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSpMapOfSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfDerHomEq
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.InvForm

section Alg
variable {R C E : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing E] [Algebra R E]

theorem dVal_smul_left (φ : C →ₐ[R] DualNumber E) (c : C) (x : Ω[C⁄R]) :
    dVal φ (c • x) = (φ c).fst * dVal φ x := by
  letI : Algebra C E := (redHom φ).toAlgebra
  haveI : IsScalarTower R C E := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.coe_restrictScalars]
  rw [LinearMap.map_smul]
  rfl

def semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    C →ₐ[R] DualNumber E where
  toFun c := TrivSqZeroExt.inl (σ c) + TrivSqZeroExt.inr (θ (KaehlerDifferential.D R C c))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [hθ, MulOpposite.smul_eq_mul_unop]; ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x)
    (c : C) : (semiDerHom σ θ hθ c).fst = σ c := by simp [semiDerHom]

theorem dVal_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    dVal (semiDerHom σ θ hθ) = θ := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using GlobalTheory.CechDR.ind1 with
  | h b c =>
    rw [dVal_smul_left, dVal_D, hθ, fst_semiDerHom]
    simp [semiDerHom]
  | h0 => simp
  | ha x y hx hy => rw [map_add, map_add, hx, hy]

end Alg
end GlobalTheory.InvForm

namespace GlobalTheory.InvForm

theorem exists_transl_val : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U V : AffOp A.left)
    (θ : Ω[Sec A.hom V.unop.1⁄R] →ₗ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
    (∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) →
    ∃ ψ : Sec A.hom U.unop.1 →ₐ[R] DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
      (∀ b, (ψ b).fst = b ⊗ₜ 1) ∧
      ∀ w : GlobalTheory.InvForm.InvForm A, θ (evForm A.hom V w.1) = GlobalTheory.InvForm.dVal ψ (evForm A.hom U w.1) := by
  intro R _ A _ U V θ hθ
  let σ : Sec A.hom V.unop.1 →ₐ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1 := Algebra.TensorProduct.includeRight
  have hθ' : ∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = σ c * θ x := hθ
  let φ := semiDerHom σ θ hθ'
  let aV : GlobalTheory.PDiv.SpAlg R (Sec A.hom V.unop.1) ⟶ A := Over.homMk (affPt A.hom V.unop) (affPt_w A.hom V.unop)
  let aU : GlobalTheory.PDiv.SpAlg R (Sec A.hom U.unop.1) ⟶ A := Over.homMk (affPt A.hom U.unop) (affPt_w A.hom U.unop)
  let p : Over.mk (spMap (algebraMap R (DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)))) ⟶ A :=
    GlobalTheory.DeRham.spOver φ ≫ aV
  let x₀ : Over.mk (spMap (algebraMap R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1))) ⟶ A :=
    GlobalTheory.DeRham.spOver (Algebra.TensorProduct.includeLeft : Sec A.hom U.unop.1 →ₐ[R] _) ≫
      aU
  let y₀ : Over.mk (spMap (algebraMap R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1))) ⟶ A :=
    GlobalTheory.DeRham.spOver σ ≫ aV
  let q' := y₀⁻¹ * x₀
  let q := GlobalTheory.DeRham.spOver (TrivSqZeroExt.inlAlgHom R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)
    (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)) ≫ q'
  let red := GlobalTheory.DeRham.spOver (TrivSqZeroExt.fstHom R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)
    (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1))
  have h1 : red ≫ p = y₀ := by
    simp only [red, p, y₀, ← Category.assoc, GlobalTheory.DeRham.spOver_comp]
    congr 2
  have h2 : red ≫ q = q' := by
    simp only [red, q, ← Category.assoc, GlobalTheory.DeRham.spOver_comp]
    have : (TrivSqZeroExt.fstHom R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)
        (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)).comp (TrivSqZeroExt.inlAlgHom R _ _) = AlgHom.id R _ := AlgHom.ext fun x ↦ by simp
    rw [this, GlobalTheory.PDiv.spOver_id, Category.id_comp]
  have h3 : red ≫ (p * q) = x₀ := by
    rw [MonObj.comp_mul, h1, h2, mul_inv_cancel_left]
  have htop : ⊤ ≤ (p * q).left ⁻¹ᵁ U.unop.1 := by
    apply GlobalTheory.PtExt.pt_dual_le_of_fst R A _ (p * q) U.unop.1
    change ⊤ ≤ (red ≫ (p * q)).left ⁻¹ᵁ U.unop.1
    rw [h3]
    intro t _
    change (U.unop.2.fromSpec).base ((spMap _).base t) ∈ U.unop.1
    have k := IsAffineOpen.range_fromSpec U.unop.2
    rw [Set.ext_iff] at k
    exact (k _).1 ⟨_, rfl⟩
  have hs : (p * q).left ≫ A.hom = spMap (algebraMap R (DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1))) :=
    Over.w (p * q)
  let ψ := GlobalTheory.CechKS.FormLocal.valHom (s := A.hom) (U := U.unop.1) (p * q).left htop hs
  have hψ : spMap (ψ : Sec A.hom U.unop.1 →+* DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)) ≫
      affPt A.hom U.unop = (p * q).left :=
    GlobalTheory.CechKS.FormLocal.valHom_pt U.unop.2 _ htop hs
  have hfst : (TrivSqZeroExt.fstHom R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)
      (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)).toRingHom.comp
      (ψ : Sec A.hom U.unop.1 →+* DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)) =
      ((Algebra.TensorProduct.includeLeft : Sec A.hom U.unop.1 →ₐ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1) :
        Sec A.hom U.unop.1 →+* Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1) := by
    apply GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := A.hom) U.unop.2
    change spMap _ ≫ affPt A.hom U.unop = spMap _ ≫ affPt A.hom U.unop
    rw [Cris.spMap_comp, Category.assoc, hψ]
    exact congrArg CommaMorphism.left h3
  refine ⟨ψ, fun b ↦ RingHom.congr_fun hfst b, fun w ↦ ?_⟩
  have key := w.2 (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1) V.unop U.unop φ ψ p q q'.left rfl rfl hψ.symm
  rw [dVal_semiDerHom] at key
  exact key

end GlobalTheory.InvForm
