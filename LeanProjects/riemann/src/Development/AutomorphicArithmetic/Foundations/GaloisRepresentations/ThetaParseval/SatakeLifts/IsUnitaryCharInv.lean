import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftGeneralLinear
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.BernAll
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.ProvedMore
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL

namespace UpperTheory.Gal.TP.Loc

theorem isUnitaryChar_mul {G : Type} [Group G] {a b : G →* ℂˣ} (ha : IsUnitaryChar a) (hb : IsUnitaryChar b) :
    IsUnitaryChar (a * b) := fun g => by
  simp [MonoidHom.mul_apply, ha g, hb g]

theorem isUnitaryChar_inv {G : Type} [Group G] {a : G →* ℂˣ} (ha : IsUnitaryChar a) : IsUnitaryChar a⁻¹ := fun g => by
  simp [ha g]

theorem liftIso_of (hP : PairOfLift) (hS : SrcGood) (hI : ContraIrr) (hU : ContraUnit) : LiftIso := by
  intro k _ _ _ _ n t ν b V _ _ W _ _ σ π hnt sν uν sb ub hs hi hu hs' hi' hL
  obtain ⟨a1, a2, a3⟩ := hS k n (ν * b) V σ (sν.mul sb) (isUnitaryChar_mul uν ub) hs hi hu
  exact GlobalTheory.T.theta_lift_general_linear PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible
    k n t b⁻¹ _ _ (contra (src (ν * b) σ)) (contra π) hnt sb.inv (isUnitaryChar_inv ub) (isSmooth_contra _)
    (hI k n V _ a1 a2).1 (hU k n V _ a1 a2 a3).1 (isSmooth_contra _) (hI k _ W π hs' hi').1
    (hP k n (n + t) ν b V W σ π sν sb hs' hL)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem liftSat_of (hL : LiftIso) (hS : SrcGood) (hI : ContraIrr) (hU : ContraUnit) (hC : SatContra) (hT : SatTwist)
    (hV : SatInvT) (hD : SatDet) (hP : SatProd) (hG : SegInv) : LiftSat := by
  intro K _ _ w n d ν b V _ _ W _ _ σ π hd nν uν nb ub hs hi hu hs' hi' hl ϖ hϖ B hB
  obtain ⟨t, rfl⟩ : ∃ t, d = n + t := ⟨d - n, by omega⟩
  have sν := isSmoothChar_of_isUnram nν
  have sb := isSmoothChar_of_isUnram nb
  obtain ⟨e⟩ := hL _ n t ν b V W σ π (by omega) sν uν sb ub hs hi hu hs' hi' hl
  obtain ⟨a1, a2, a3⟩ := hS _ n (ν * b) V σ (sν.mul sb) (isUnitaryChar_mul uν ub) hs hi hu
  have nm : IsUnram (ν * b) := fun x hx => by rw [MonoidHom.mul_apply, nν x hx, nb x hx, one_mul]
  have ni : IsUnram b⁻¹ := fun x hx => by rw [MonoidHom.inv_apply, nb x hx, inv_one]
  have s1 : GlobalTheory.LFun.HasSatGL w (src (ν * b) σ) ((B.map (·⁻¹)).map (· * (ν * b) ϖ)) :=
    hT K w n (ν * b) V _ nm ϖ hϖ _ (hV K w n V σ B hB)
  have s2 := hC K w n V _ a1 a2 a3 _ s1
  have s3 := hD K w t b⁻¹ ni ϖ hϖ
  have ud : IsUnitarisable (detRep (Fin t) b⁻¹) := (isUnitarisable_ofChar_iff _).2 fun _ => isUnitaryChar_inv ub _
  have s4 := hP K w n t _ _ _ _ (isSmooth_contra _) (hI _ n V _ a1 a2).1
    ((isSmooth_ofChar_iff _).2 sb.inv.detChar) (isIrreducible_ofChar _) _ _ s2 s3
  have s5 := GlobalTheory.PrinSat.hasSatGL_of_equiv e s4
  have u5 : IsUnitarisable (contra π) :=
    GlobalTheory.GenericUnitary.isUnitarisable_of_equiv e.symm (GlobalTheory.SmGL.UnitInd.isUnitarisable_prod₂ (hU _ n V _ a1 a2 a3).1 ud)
  have s6 := hC K w (n + t) _ _ (isSmooth_contra π) (hI _ _ W π hs' hi').1 u5 _ s5
  obtain ⟨e'⟩ := (hI _ _ W π hs' hi').2
  have s7 := GlobalTheory.PrinSat.hasSatGL_of_equiv e' s6
  rw [Multiset.map_add, hG] at s7
  simpa [Multiset.map_map, mul_comm] using s7

end UpperTheory.Gal.TP.Loc

end
