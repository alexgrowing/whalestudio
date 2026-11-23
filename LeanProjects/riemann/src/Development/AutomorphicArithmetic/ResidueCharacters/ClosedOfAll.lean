import Development.AutomorphicArithmetic.ResidueCharacters.FamilyBoundAtTwoThreeOfLocalBounds
import Development.AutomorphicArithmetic.ResidueCharacters.RowTwo
import Development.AutomorphicArithmetic.ResidueCharacters.RowThree
import Development.AutomorphicArithmetic.ResidueCharacters.ThreeHost
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

theorem boundAtTwoThree_family_of_prints (hP : Hypotheses₂) {eps : ℝ} (Fm : FamP eps) : BoundAtTwoAndThreeForFamily Fm :=
  family_bound_at_two_three_of_local_bounds three_ne_q (rowTwo hP) (rowThree hP) Fm

theorem closed_of_all (𝒞 : FamClass) {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), P Fm CH) :
    Closed 𝒞 P :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => h Fm CH⟩⟩

theorem rowN_of_all (h : ∀ {eps : ℝ} (Fm : FamP eps), BoundAtTwoAndThreeForFamily Fm) {hL : GlobalTheory.Published.LocalLanglandsGL} (p : GlobalTheory.Mem.Top.Bl.Prm hL) :
    GlobalTheory.Fc.RL.At p (fun Q L => GlobalTheory.Fc.R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) :=
  GlobalTheory.Fc.RL.At.of_row (GlobalTheory.Fc.Row.of_sel fun _ _ _ => closed_of_all _ fun Fm _ => h Fm)

theorem boundAtTwoThree_at_prm_of_prints (hP : Hypotheses₂) {hL : GlobalTheory.Published.LocalLanglandsGL} (p : GlobalTheory.Mem.Top.Bl.Prm hL) :
    GlobalTheory.Fc.RL.At p (fun Q L => GlobalTheory.Fc.R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) :=
  rowN_of_all (fun Fm => boundAtTwoThree_family_of_prints hP Fm) p

end UpperTheory.N
