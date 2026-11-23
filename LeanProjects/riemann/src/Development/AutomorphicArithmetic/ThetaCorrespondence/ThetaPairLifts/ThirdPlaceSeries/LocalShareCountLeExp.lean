import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LocalShareNumberBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.LocShareNum
open Formalism.MainNotions.ArithmeticCylinders (admLq TieAdmG eUk eJk locShare goodAt VecAt IsLabel)
open Formalism.L2.GlobalTheoryTheory.ConcN (Wg SizesRec SizesAt weight_numbers_bound)
open Formalism.L2.GlobalTheoryTheory.ConcNWeight (RangeW host_facts sum_wtOf eUk_coeff_one_re_pos eJk_coeff_one_re_pos wtOf_eq_zero_of_not_label rangeW_of_sizes)
local instance {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
local instance {D : D7} (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
end GlobalTheory.CovTop.LocShareNum
namespace GlobalTheory.CovTop.LocShareNum
open Formalism.MainNotions.ArithmeticCylinders (admLq TieAdmG eUk eJk locShare goodAt VecAt IsLabel)
open Formalism.L2.GlobalTheoryTheory.ConcN (Wg SizesRec SizesAt weight_numbers_bound)
open Formalism.L2.GlobalTheoryTheory.ConcNWeight (RangeW rangeW_of_sizes)
theorem local_share_count_le_exp_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι _ _ _ _ => ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod ((Fm.D x ι).host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧ ∀ S : ∀ k : Fin 2, Finset (Formalism.MainNotions.ArithmeticCylinders.Tup (Fm.D x ι) k), (∀ k, ∀ t ∈ S k, ¬ Formalism.MainNotions.ArithmeticCylinders.goodAt (Fm.D x ι) k t) → Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 0 (S 0) + Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 1 (S 1) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  intro _hP hG
  refine ⟨1 / 52, by norm_num, fun eps he he1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, le_rfl, ?_⟩⟩⟩
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  have hez1 : Fm.ez ≤ 1 := le_trans (div_le_self he.le Fm.toFamCore.one_le_J) (by linarith)
  obtain ⟨a, ha⟩ := wg_sum_le Fm.ez hez hez1
  refine ⟨max (max a (Fm.x1 + 1)) (max 4 ((3 / 2 : ℝ) ^ (1 / Fm.ez))), fun x hx hle ι p hp _ => ?_⟩
  have hx4 : 4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have hxa : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hx1 : (3 / 2 : ℝ) ^ (1 / Fm.ez) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle
  have hxe : 3 / 2 ≤ x ^ Fm.ez := by
    have hpos : 0 ≤ (3 / 2 : ℝ) ^ (1 / Fm.ez) := by positivity
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (1 / Fm.ez)) ^ Fm.ez := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hez.ne', Real.rpow_one]
      _ ≤ x ^ Fm.ez := Real.rpow_le_rpow hpos hx1 hez.le
  have hS := sizesRec_at_point Fm hx hx4 ι (le_refl (6 : ℝ))
  have hR := rangeW_of_sizes hS hxe
  have hL := GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation hG _ hp.2.2
  dsimp only
  rw [Fm.L_x x ι hx, Fm.toFamCore.L_ez x ι]
  have hψ := stdAddChar_ne_one (Fm.D x ι)
  refine ⟨fun k => @ZMod.stdAddChar _ ⟨((Fm.D x ι).host.g_prime k).ne_zero⟩, hψ, fun S hS' => ?_⟩
  have h0 := locShare_eUk_le_Wg hL (tieAdmG_rec _) hR _ hψ 0 (S 0) (hS' 0)
  have h1 := locShare_eUk_le_Wg hL (tieAdmG_rec _) hR _ hψ 1 (S 1) (hS' 1)
  have h2 := ha x hxa _ hS
  linarith
end GlobalTheory.CovTop.LocShareNum
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_share_number_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι _ _ _ _ => ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod ((Fm.D x ι).host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧ ∀ S : ∀ k : Fin 2, Finset (Formalism.MainNotions.ArithmeticCylinders.Tup (Fm.D x ι) k), (∀ k, ∀ t ∈ S k, ¬ Formalism.MainNotions.ArithmeticCylinders.goodAt (Fm.D x ι) k t) → Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 0 (S 0) + Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 1 (S 1) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  first | exact @_root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp_alt | exact _root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp_alt | (intros; apply _root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp_alt <;> assumption)
end
end
