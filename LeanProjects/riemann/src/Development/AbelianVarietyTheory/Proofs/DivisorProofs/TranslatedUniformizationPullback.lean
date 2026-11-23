import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundleStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory
namespace TorusPullFrame

open GlobalTheory.PullHermitian

variable {X Y : Scheme.{0}}

lemma chart_pull_iff (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (j : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull f).U j ↔ ⊤ ≤ (x ≫ f) ⁻¹ᵁ L.U (j PUnit.unit) :=
  ⟨fun h _ hp => Set.mem_iInter.1 (h hp) PUnit.unit, fun h _ hp => Set.mem_iInter.2 fun _ => h hp⟩

lemma le_left {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ U :=
  h.trans (fun _ hp => And.left hp)

lemma le_right {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ V :=
  h.trans (fun _ hp => And.right hp)

lemma valAt'_pull_g (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (i j : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull f).U i ⊓ (L.pull f).U j)) :
    valAt' x ((L.pull f).U i ⊓ (L.pull f).U j) ((L.pull f).g i j).val =
      valAt' (x ≫ f) (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
        (L.g (i PUnit.unit) (j PUnit.unit)).val := by
  have hi := (chart_pull_iff x L f i).1 (le_left h)
  have hj := (chart_pull_iff x L f j).1 (le_right h)
  rw [valAt'_eq_unitVal x h, valAt'_eq_unitVal _ (inf_of _ hi hj)]
  have := unitVal_linComb x L f 1 (i PUnit.unit) (j PUnit.unit) h (inf_of _ hi hj)
  exact congrArg Units.val (this.trans (zpow_one _))

lemma differentiable_append {g : ℕ} (x₀ : Fin g → ℂ) :
    Differentiable ℂ (fun z : Fin g → ℂ => (Fin.append z x₀ : Fin (g + g) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [Fin.append_left]; exact differentiable_apply a
  · simp only [Fin.append_right]; exact differentiable_const _

theorem exists_holUnif_pull_right : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L₀ : LB A.left) (g : ℕ) (u : HolUnif A L₀ g)
    (L : LB (A ⊗ A).left) (U : HolUnif (A ⊗ A) L (g + g)),
    (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → ∀ x₀ : Fin g → ℂ,
    ∃ u' : HolUnif A (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left) g, u'.ex = u.ex ∧
      (∀ j z, (⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left).U j ↔
        ⊤ ≤ (U.ex (Fin.append z x₀)).left ⁻¹ᵁ L.U (j PUnit.unit))) ∧
      ∀ j z, u'.fr j z = U.fr (j PUnit.unit) (Fin.append z x₀) := by
  intro A _ L₀ g u L U hU x₀
  have key : ∀ z, u.ex z ≫ lift (𝟙 A) (toUnit A ≫ u.ex x₀) = U.ex (Fin.append z x₀) := by
    intro z
    rw [hU, comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _), Category.id_comp]
  have keyl : ∀ z, (u.ex z).left ≫ (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left =
      (U.ex (Fin.append z x₀)).left := fun z => by rw [← Over.comp_left, key]
  have hch : ∀ j z, (⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left).U j ↔
      ⊤ ≤ (U.ex (Fin.append z x₀)).left ⁻¹ᵁ L.U (j PUnit.unit)) := fun j z =>
    (chart_pull_iff _ L _ j).trans (iff_of_eq (by rw [keyl z]))
  refine ⟨⟨u.ex, u.ex_add, u.ex_onto, u.Λ, u.ker, u.discrete, u.full, u.hol,
      fun j z => U.fr (j PUnit.unit) (Fin.append z x₀),
      fun j => (U.fr_hol (j PUnit.unit)).comp (differentiable_append x₀).differentiableOn
        (fun z hz => (hch j z).1 hz),
      fun j z hz => U.fr_ne _ _ ((hch j z).1 hz),
      fun i j z h => by
        have hi := (hch i z).1 (le_left h)
        have hj := (hch j z).1 (le_right h)
        show U.fr (i PUnit.unit) (Fin.append z x₀) = _ * U.fr (j PUnit.unit) (Fin.append z x₀)
        rw [valAt'_pull_g _ L _ i j h, keyl z]
        exact U.fr_compat _ _ _ (inf_of _ hi hj)⟩, rfl, hch, fun _ _ => rfl⟩

end TorusPullFrame
end GlobalTheory
