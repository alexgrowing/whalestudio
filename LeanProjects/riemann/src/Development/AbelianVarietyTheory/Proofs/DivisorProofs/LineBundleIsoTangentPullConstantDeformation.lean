import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfSymmetric
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TangentConstLB

theorem symIso_of_comm {S₀ S₁ : Scheme.{0}} {X : Over S₀} {A' : Over S₁} [GrpObj X] [GrpObj A']
    {L : LB X.left} (hL : L.IsLB)
    (hS : LBIso L (L.pull (GrpObj.inv : X ⟶ X).left)) (f : A'.left ⟶ X.left)
    (hf : (GrpObj.inv : A' ⟶ A').left ≫ f = f ≫ (GrpObj.inv : X ⟶ X).left) :
    LBIso ((L.pull f).pull (GrpObj.inv : A' ⟶ A').left) (L.pull f) := by
  have h1 := GlobalTheory.FamRep.lbIso_pull_pull hL f (GrpObj.inv : A' ⟶ A').left
  rw [hf] at h1
  have h2 := (GlobalTheory.FamRep.lbIso_pull_pull hL (GrpObj.inv : X ⟶ X).left f).symm
  have h3 := GlobalTheory.FamRep.lbIso_pull hS.symm f
  have hinv := pull_isLB hL (GrpObj.inv : X ⟶ X).left
  exact LBIso.trans (pull_isLB (pull_isLB hL f) _) (pull_isLB hL _) (pull_isLB hL f) h1
    (LBIso.trans (pull_isLB hL _) (pull_isLB hinv f) (pull_isLB hL f) h2 h3)

theorem lbIso_tangent_const :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x₀ : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G x₀ π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) := by
  intro E _ _ _ H Dw l Xo c K _ _ x₀ x' A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hAbG : IsAbelianScheme Xo.univ.t.G := by
    haveI := Xo.univ.proper
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ Xo.univ.t.semi
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAbG hπ
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨-, w, hw, -⟩ := Xo.univ.t.sym
  have hS : LBIso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left) := ⟨w, hw⟩
  have c1 : (GrpObj.inv : A' ⟶ A').left ≫ π' = π' ≫ (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left :=
    GlobalTheory.PolBaseChange.inv_comm hπ'
  have c2 : (GrpObj.inv : A' ⟶ A').left ≫ (q ≫ π) = (q ≫ π) ≫ (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left := by
    rw [← Category.assoc, GlobalTheory.PolBaseChange.inv_comm hq, Category.assoc, GlobalTheory.PolBaseChange.inv_comm hπ,
      Category.assoc]
  have f1 := GlobalTheory.FamRep.lbIso_pull_pull hL π' i
  rw [hiπ] at f1
  have f2 := GlobalTheory.FamRep.lbIso_pull_pull hL (q ≫ π) i
  rw [← Category.assoc, hiq, Category.id_comp] at f2
  exact GlobalTheory.SymFirstOrder.lbIso_of_symmetric K A A' i q hA hi hq hiq _ _ (pull_isLB hL π') (pull_isLB hL (q ≫ π))
    (symIso_of_comm hL hS π' c1) (symIso_of_comm hL hS (q ≫ π) c2)
    (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) f1 f2.symm)

end GlobalTheory.TangentConstLB
