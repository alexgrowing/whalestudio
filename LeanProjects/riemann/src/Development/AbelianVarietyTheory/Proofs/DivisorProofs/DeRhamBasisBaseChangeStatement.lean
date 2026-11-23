import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamBasisBaseChange
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_basis_base_change : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (𝔠 : FracId (FR E))
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (cm : OAct (orderC c) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p → ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
    ∃ B : Module.Basis (Fin n) ℂ (HdR X.A), ∀ (a : orderC c) (α : X.A ⟶ X.A) [IsMonHom α],
      α.left ≫ p = p ≫ (cm.act a).left → ∀ i, push (dp0 ℂ) (𝟙 _) α (B i) =
        ∑ k, (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) k : R) : ℂ) • B k := by
  first | exact @GlobalTheory.DRLine.exists_basis_push_eq_sum | exact GlobalTheory.DRLine.exists_basis_push_eq_sum | (intros; apply GlobalTheory.DRLine.exists_basis_push_eq_sum <;> assumption)
