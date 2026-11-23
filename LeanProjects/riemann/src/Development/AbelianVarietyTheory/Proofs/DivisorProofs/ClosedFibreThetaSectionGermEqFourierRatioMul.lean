import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTerm
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLiftImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mum.FibreGerm.secGerm_eq_secRatio_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (ψ : Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0) ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ _ ψ) → ∀ (k N : ℕ) (α : Fin N → D.toPre.X) (b : ∀ j, D.toPre.SecB k (α j)) (τ : Fin N → SecK D.toPre.P.L Y.q.left k) (F : Fin N → IntFam (maximalIdeal R) D.toPre k) (s : Fin N → H0 U.LG.L k), (∀ j, IsTermOf Y (b j) (τ j)) → (∀ j, (F j).Lead (α j) (b j)) → (∀ j, U.ExpandsAt 0 k (s j) (F j).f) → ∀ (z : (thickObj R (maximalIdeal R) 0 G).left) (j : Fin N) (i : Fin 1 → U.LG.L.ι), ψ.left z ∈ nonzeroLocus (τ j) → (fstG (maximalIdeal R) 0 G).left z ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s l) i = gs (Y := (thickObj R (maximalIdeal R) 0 G).left) ψ.left z (nonzeroLocus (τ j)) (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i := by
  intro R _ _ _ D A G _ _ U Y ψ hP k N α b τ F s hT hL hE z j i hτz hi
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.toPre.P.isLB z
  obtain ⟨c, hc⟩ := GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term R D A G U Y _ (𝟙 _) ψ hP k z J J' hJ hJ'
  have hv : ∀ l, secGerm (fstG (maximalIdeal R) 0 G).left z (s l)
      (fun _ => J ((fstG (maximalIdeal R) 0 G).left ≫ 𝟙 _)) = c.val * sval (τ l) ψ.left z J' := by
    intro l
    have := hc (α l) (b l) (τ l) (F l) (s l) (hT l) (hL l) (hE l)
    rw [Category.id_comp] at this
    exact this
  obtain ⟨a, ha⟩ := exists_unit_secGerm k (fstG (maximalIdeal R) 0 G).left z hi
    (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (fstG (maximalIdeal R) 0 G).left)
  let jt : Fin 1 → D.toPre.P.L.ι := fun _ => J' (ψ.left ≫ Y.q.left)
  have hzt : ψ.left z ∈ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt :=
    hJ'.mem (fun _ : Fin 1 => Y.q.left) ψ.left
  have hzW : ψ.left z ∈ nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt := ⟨hτz, hzt⟩
  have hk : nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt ≤
      (LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ))).U jt := inf_le_right
  have ha' : nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt ≤ nonzeroLocus (τ j) :=
    inf_le_left
  have hu : ∀ l, sval (τ l) ψ.left z J' =
      gs ψ.left z (nonzeroLocus (τ j)) (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) * sval (τ j) ψ.left z J' := by
    intro l
    have e := congrArg (gs ψ.left z _) (GlobalTheory.ProjSpace.secRatio_on (τ j) (τ l) jt ha' hk)
    rw [sval_of (τ l) ψ.left z J' jt (fun _ => rfl), sval_of (τ j) ψ.left z J' jt (fun _ => rfl)]
    exact ((gs_res _ _ hk hzW _).symm.trans e).trans ((gs_mul _ _ _ hzW _ _).trans
      (congrArg₂ (· * ·) (gs_res _ _ ha' hzW _) (gs_res _ _ hk hzW _)))
  have hunit : IsUnit (sval (τ j) ψ.left z J') := by
    obtain ⟨w, hw⟩ := GlobalTheory.ProjSpace.isUnit_resG_sec (τ j) jt ha' hk
    rw [sval_of (τ j) ψ.left z J' jt (fun _ => rfl)]
    have e : gs ψ.left z _ ((τ j).f jt) = (gm ψ.left z _ w).val :=
      (gs_res _ _ hk hzW _).symm.trans ((congrArg (gs ψ.left z _) hw.symm).trans (gs_unit _ _ _ hzW w))
    exact e ▸ Units.isUnit _
  refine ⟨?_, fun l => ?_⟩
  · rw [ha, hv j]
    exact a.isUnit.mul (c.isUnit.mul hunit)
  · rw [ha, ha, hv, hv, hu l]
    ring
