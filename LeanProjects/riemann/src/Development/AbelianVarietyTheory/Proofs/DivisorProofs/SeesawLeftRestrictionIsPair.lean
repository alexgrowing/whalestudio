import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompAlt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorOrderFiniteIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmUniformizationAlgebraicModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEndomorphismPlaceIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackChainCompatStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem exists_obj_of_isogenous_model : GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.Published.AbelianDeRham →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ → IsPlaceOver l lam k₀ R₀ →
    (∀ x ∈ R₀, x ∈ k₀) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (p₀ : X.A.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
      IsAbelianScheme G₀ → IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ → IsMonHom Ψ₀ → IsFinite Ψ₀.left →
      Flat Ψ₀.left → Surjective Ψ₀.left →
      Eventually l lam fun R ↦ ∃ (X₀ : Obj (FR E) 𝔠 (Sp R)) (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A),
        X.IsPullBy X₀ (spMap R.subtype) p ∧
        (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) ∧
        (∀ (a : orderC c) (α : X.A ⟶ X.A), IsMonHom α →
          (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α.left ≫ p = p ≫ (cm.act a).left) ∧
        ∀ (v₀ : epsR R₀ ⟶ G₀) (v' : X.Lie), IsTangent v₀ →
          v'.hom.left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left → ∃ v : X₀.Lie, Obj.LieCorr R.subtype p v v' := by
  intro HD HR E _ _ _ I _ φ hφ c y hc l _ lam 𝔠 X U hα k₀ R₀ hk₀ hR₀ hR₀k G₀ _ p₀ P₀ Ψ₀ hG₀ hp₀ hΨ hfin hfl hsurj
  let σ : R₀ →+* Qb :=
    { toFun := fun x ↦ ⟨x, (hR₀.2.1 x x.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  obtain ⟨XQ, pQ, gQ, cmQ, hQ, hgQ, epQ, hrmQ, hαQ⟩ :=
    GlobalTheory.T.cm_uniformization_algebraic_model HD E I φ c (lattice c y) 𝔠 X U hα R₀ σ (fun _ ↦ rfl) G₀ p₀ hG₀ hp₀
  obtain ⟨k, hk, H⟩ := GlobalTheory.T.cm_endomorphism_place_integral HD HR (FR E) 𝔠 (orderC c) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c) l lam k₀ R₀ (GlobalTheory.T.conductor_order_finite_integers E c) hk₀ hR₀
    hR₀k σ (fun _ ↦ rfl) G₀ P₀ Ψ₀ hG₀ hΨ hfin hfl hsurj XQ gQ cmQ hgQ hrmQ
  refine ⟨k ⊔ k₀, inferInstance, fun R hR ↦ ?_⟩
  have hle : R₀ ≤ R := fun x hx ↦ (hR.mono le_sup_right).2.2 x (hR₀k x hx) (hR₀.2.1 x hx)
  let j : R →+* Qb :=
    { toFun := fun x ↦ ⟨x, (hR.2.1 x x.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  obtain ⟨X₀, pj, g, cm, hj, hg, epj, hrm, hcm⟩ :=
    H R (hR.mono le_sup_left) (Subring.inclusion hle) j (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hspec : spMap (algebraMap Qb ℂ) ≫ spMap j = spMap R.subtype := by
    rw [GlobalTheory.HomDescent.spMap_comp]; rfl
  have hX : X.IsPullBy X₀ (spMap R.subtype) (pQ ≫ pj) := hspec ▸ Obj.IsPullBy.trans hQ hj
  refine ⟨X₀, pQ ≫ pj, cm, hX, hrm, fun a α hα' hu ↦ ?_, fun v₀ v' hv₀ hv' ↦ ?_⟩
  · rw [← Category.assoc, hαQ a α hα' hu, Category.assoc, hcm, Category.assoc]
  · obtain ⟨v, hv, ev⟩ := GlobalTheory.T.tangent_pullback_chain_compat R₀ R (Subring.inclusion hle) (fun _ ↦ rfl) G₀ X₀.A X.A g (pQ ≫ pj) hg hX.grp v₀ v'.hom
      hv₀ (by rw [Category.assoc, epj, epQ]; exact hv')
    exact ⟨Serre.Lie.mk _ v hv, ev⟩

end GlobalTheory.LatModel
