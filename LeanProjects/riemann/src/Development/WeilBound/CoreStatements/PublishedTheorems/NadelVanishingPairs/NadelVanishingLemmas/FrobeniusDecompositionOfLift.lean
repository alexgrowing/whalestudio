import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLogFormsFrobeniusLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChartStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogSectionsDifferentialClosedStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierOperatorLogSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem mem_inter_iff {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens) (s : Finset ι) (y : X) :
    y ∈ inter U s ↔ ∀ i ∈ s, y ∈ U i := by
  classical
  unfold inter
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    rw [← ih]
    exact Iff.rfl

theorem decomp_of_isLifted (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p]
    {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι)
    (hn : n < p) (hL : IsLifted p (suppAll E) 𝒜.U 𝒜.x) : Decomp p 𝒜 := by
  intro G r hr a b hH
  exact GlobalTheory.T.cech_log_forms_frobenius_lift p (suppAll E) 𝒜.U 𝒜.x (inter 𝒜.U) G (p • G + ∑ c, r c • E c) hn 𝒜.gen
    (fun i => ((𝒜.chart i).chart _ (𝒜.gen i)).coord)
    (fun s _ y => mem_inter_iff 𝒜.U s y) hL
    (GlobalTheory.T.roundedTwist_localEquation_chart p 𝒜 G r hr).1
    (fun q s η hη => GlobalTheory.T.log_sections_differential_closed p 𝒜 G r hr q (inter 𝒜.U s) η hη)
    (fun s j hj γ hγ => GlobalTheory.T.cartier_operator_log_sections p 𝒜 G r hr s j hj γ hγ)
    a b hH

end GlobalTheory.LogDR
