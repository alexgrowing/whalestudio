import Development.EtaleCohomology.EtaleSheaves.PullInjOfIso
import Development.EtaleCohomology.EtaleSheaves.LeafKillCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafOneHighPf

open LateralTheory.E.E4

instance disc_pres : PreservesLimitsOfShape WalkingCospan (disc : PSh ⥤ Spc) := by
  unfold disc SimplicialObject.const
  infer_instance

instance sch_pres : PreservesLimitsOfShape WalkingCospan sch := by
  show PreservesLimitsOfShape WalkingCospan (yoneda ⋙ disc)
  infer_instance

def DedAff (Ω : Type) [Field Ω] (Y : Scheme.{0}) : Prop :=
  ∃ (B : Type) (_ : CommRing B) (_ : IsDedekindDomain B) (_ : Algebra Ω B) (_ : Algebra.FiniteType Ω B), Nonempty (Y ≅ Sp B)

def LeafTwoAff : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∃ (U V : Scheme.{0}) (u : U ⟶ C) (v : V ⟶ C), IsOpenImmersion u ∧ IsOpenImmersion v ∧
    Set.range u.base ∪ Set.range v.base = Set.univ ∧ DedAff Ω U ∧ DedAff Ω V ∧ DedAff Ω (pullback u v)

def LeafOpenCover : Prop := ∀ (R : Type) [CommRing R] {U V X : Scheme.{0}} (u : U ⟶ X) (v : V ⟶ X),
  IsOpenImmersion u → IsOpenImmersion v → Set.range u.base ∪ Set.range v.base = Set.univ →
  ∀ n, Epi (biprod.desc ((free R).map ((sch.map u).app n)) ((free R).map ((sch.map v).app n)))

def LeafMV : Prop := LateralTheory.E.MVPf.MVSpc

end LateralTheory.E.LeafOneHighPf
