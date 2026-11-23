import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionComponentsProportionalShiftMultipleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaAlgClosureWithExpansions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiMulPsiOfAdditionFirstVariable
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiMulPsiOfAdditionSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUnivStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultPsiEvenOverExtensionField

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psiEven_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → D.PsiEven) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ hψ
  have hG : GlobalFnsSt := hL.globalFns
  obtain ⟨th, hth, -⟩ := GlobalTheory.UU.PullSec.existsUnique_pullG U (Kbar V) (toUnit _) 1 θ
  obtain ⟨s₀, hs₀, -⟩ := GlobalTheory.UU.PullSec.existsUnique_pullB D (Kbar V) (toUnit _) 1 f
  obtain ⟨r, n, t, t', s, s', hr, hE, -, hB⟩ := GlobalTheory.AddClosure.main hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  have hP : PsiRel D (TF (R := V) (Kbar V)) s₀ := GlobalTheory.psiRel_of_pullB V D (Kbar V) f s₀ hs₀ hψ
  have hsupp := GlobalTheory.T.thetaSection_support_eq_univ hL hL2 V hV D A G U θ f hθ
  have h0 : ∃ j, (s₀ 0).f j ≠ 0 := (GlobalTheory.pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ 0).2 (hsupp.1 0)
  rw [← (GlobalTheory.TauValues.main V D (Kbar V)).2]
  intro z J hJ m
  obtain ⟨⟨u, hu, -⟩, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := D) (F := Kbar V) hG 2 m 0
  obtain ⟨a, ha⟩ := GlobalTheory.T.expansionComponents_proportional_shift_multiple hL hL2 V hV D A G U 2 (by norm_num) 0 m u hu (hsupp.2 0)
  have e1 := GlobalTheory.psi_mul_psi_of_addition_first_variable V D (Kbar V) s₀ r n s s' hr hB hP h0 0 0 m 0
    (add_zero 0).symm a u (fun i z J hJ => ha _ _ (hE i).1 z J hJ) z J hJ
  have e2 := GlobalTheory.T.psi_mul_psi_addition_second_variable V D (Kbar V) s₀ r n s s' hr hB hP h0 m 0 rfl a u
    (fun i z J hJ => ha _ _ (hE i).2 z J hJ) z J hJ
  have hc0 : cT D (TF (R := V) (Kbar V)) 0 = 1 := by
    have h := GlobalTheory.FirstSlot.cT_add D (TF (R := V) (Kbar V)) 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hcub : cubV D.cub z J (cT D (TF (R := V) (Kbar V)) 0) (cT D (TF (R := V) (Kbar V)) 0)
      (cT D (TF (R := V) (Kbar V)) m) = 1 := by
    rw [hc0]
    exact (isCub_cubV D.cub hJ).face _ _
  simp only [hcub, _root_.mul_one] at e1
  have e4 := Units.ext (e1.trans e2.symm)
  rw [_root_.mul_assoc] at e4
  erw [_root_.zero_add] at e4
  exact (mul_left_cancel e4).symm

end GlobalTheory
