import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyScalarNe

theorem polAVSectionInverseImage_ne_zero {K : Type} [Field K] (P : PolAV (Sp K)) (T : Over (Sp K)) (t₀ : T.left) (s : P.L.Sec)
    (hs : ∃ p, p ∈ nonzeroLocus s) (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (h : IsPolAVSectionInverseImage P T s t) :
    t ≠ 0 := by
  rintro rfl
  obtain ⟨z, hz⟩ := hs
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  have hpb : IsPullback (fst T P.A).left (snd T P.A).left T.hom P.A.hom := by
    rw [Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback _ _
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback hpb t₀ z (Subsingleton.elim _ _)
  have hle : (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k) ≤ (snd T P.A).left ⁻¹ᵁ P.L.U k :=
    LB.wchart_le P.L _ (fun _ : Fin 1 => k) 0
  have hyU : y ∈ (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k) := by
    show y ∈ LB.wchart P.L _ _
    refine Set.mem_iInter.2 fun _ => ?_
    show (snd T P.A).left y ∈ (P.L.U k : Set P.A.left)
    rw [hy]; exact hk
  subst hy
  have e := congrArg (gs (𝟙 _) y _) (h k hle)
  rw [gs_appLE _ _ _ hle (𝟙 _) y hyU, Category.id_comp, gs_stalkMap (snd T P.A).left y _ hk] at e
  have u' := u.map ((snd T P.A).left.stalkMap y).hom
  rw [← e] at u'
  have h0 : gs (𝟙 _) y ((LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k)) ((0 : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)).f (fun _ => k)) = 0 := by
    have z0 : (0 : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)).f (fun _ => k) = 0 := rfl
    rw [z0, gs_eq _ y _ hyU, map_zero, map_zero]
  rw [h0] at u'
  exact not_isUnit_zero u'

end GlobalTheory.KeyScalarNe

theorem GlobalTheory.KeyScalarNe.scalar_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre), GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N) (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → c ≠ 0 := by
  intro V _ _ _ _ _ D x G _ _ _ U w₀ hw C _ _ _ _ _ _ _ N ν th ϑ c hon hex hv
  rintro rfl
  rw [zero_smul] at hv
  have h0 : ν.FamV (0 : Fam D.toPre C 1) 0 := by
    have := GlobalTheory.WeilValues.famV_smul ν hv 0
    rwa [zero_smul, zero_smul] at this
  have hϑ : ϑ = 0 := GlobalTheory.Ex.FamVal.famV_inj ν hv h0
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF GlobalTheory.allSixLaws.1.globalFns U C (k := 1) le_rfl w₀ hw.1
  have ht : th = 0 := by
    have h1 := (he th ϑ).1 hex
    rw [hϑ] at h1
    exact e.map_eq_zero_iff.1 h1
  obtain ⟨z, -, hz⟩ := x.th_ne (IsLocalRing.closedPoint _)
  exact GlobalTheory.KeyScalarNe.polAVSectionInverseImage_ne_zero x.P (TFK (R := V) C) (IsLocalRing.closedPoint C) x.th ⟨z, hz⟩ th hon ht
