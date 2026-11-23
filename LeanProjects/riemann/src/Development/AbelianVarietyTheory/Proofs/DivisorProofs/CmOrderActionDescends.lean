import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem exists_lie_end_diagonal_of_tensor : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left)
    (c : Ideal (OF E)) (cm : OAct (orderC c) X₀.A),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ cd : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ v, ∃ v' : X.Lie, Obj.LieCorr R.subtype p v v' ∧ U.u.IsDiff (cd v) v'.hom) →
      (∀ v (v' : X.Lie) W, Obj.LieCorr R.subtype p v v' → U.u.IsDiff W v'.hom → W = cd v) →
    ∀ t : orderC c ⊗[ℤ] R, ∃ T : X₀.Lie →ₗ[R] X₀.Lie, ∀ v j, cd (T v) j =
      Algebra.TensorProduct.productMap ((φ (U.e j)).comp (orderC c).subtype).toIntAlgHom
        (algebraMap R ℂ).toIntAlgHom t * cd v j := by
  intro E _ _ I _ 𝔠 φ L R X₀ X U p c cm hcm cd hcd1 hcd2 t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, fun v j ↦ by simp⟩
  | add s t hs ht =>
    obtain ⟨S, hS⟩ := hs
    obtain ⟨T, hT⟩ := ht
    exact ⟨S + T, fun v j ↦ by
      rw [LinearMap.add_apply, map_add, Pi.add_apply, hS, hT, map_add, add_mul]⟩
  | tmul a x =>
    have := cm.hom a
    obtain ⟨α, hα, hp, hex⟩ := hcm a
    refine ⟨x • GlobalTheory.Serre.Lie.map X₀.rm X₀.rm (cm.act a), fun v j ↦ ?_⟩
    obtain ⟨v', hc, hd⟩ := hcd1 v
    let F : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      LinearMap.pi fun j ↦ φ (U.e j) (a : E) • LinearMap.proj j
    have hd' := GlobalTheory.HomLinear.isDiff_comp U.u U.u α F (fun w ↦ hex w) v'.isTangent hd
    have hc' : Obj.LieCorr R.subtype p (GlobalTheory.Serre.Lie.map X₀.rm X₀.rm (cm.act a) v)
        (GlobalTheory.Serre.Lie.map X.rm X.rm α v') := by
      unfold Obj.LieCorr at hc ⊢
      rw [GlobalTheory.Serre.Lie.hom_map, GlobalTheory.Serre.Lie.hom_map, Over.comp_left, Over.comp_left,
        Category.assoc, hp, ← Category.assoc, hc, Category.assoc]
    have h := congrFun (hcd2 _ _ _ hc' hd') j
    rw [LinearMap.smul_apply, map_smul, Pi.smul_apply, ← h,
      Algebra.TensorProduct.productMap_apply_tmul]
    change (x : ℂ) * (φ (U.e j) (a : E) * cd v j) = φ (U.e j) (a : E) * (x : ℂ) * cd v j
    ring

end GlobalTheory.LatModel
