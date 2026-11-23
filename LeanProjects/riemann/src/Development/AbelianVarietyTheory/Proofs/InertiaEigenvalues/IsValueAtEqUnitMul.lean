import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntegralSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueSecEqMulGen
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ModelMetric
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ValueTwoGen

def genSec {Y : Scheme.{0}} {M : LB Y} (t : LB.Gen M) (ht : t.IsGen) : LB.Sec M where
  f := fun j => (t.s j).val
  compat := fun i j => congrArg Units.val (ht i j)

theorem exists_unit_gen {Y : Scheme.{0}} (M : LB Y) (hc : ⨆ j, M.U j = ⊤)
    (t t' : LB.Gen M) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, (t'.s j).val =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom (w : Γ(Y, ⊤)) * (t.s j).val := by
  obtain ⟨w, hw, -⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t' ht') t ht
  obtain ⟨w', hw', -⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t ht) t' ht'
  obtain ⟨_, -, hu⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t ht) t ht
  have h1 : (1 : Γ(Y, ⊤)) = w' * w := by
    have a := hu 1 (fun j => by simp [genSec])
    have b := hu (w' * w) (fun j => by
      have e1 := hw' j
      have e2 := hw j
      simp only [genSec] at e1 e2 ⊢
      rw [map_mul, _root_.mul_assoc, ← e2, ← e1])
    exact a.trans b.symm
  exact ⟨⟨w, w', by rw [_root_.mul_comm]; exact h1.symm, h1.symm⟩, fun j => hw j⟩

end GlobalTheory.ValueTwoGen
