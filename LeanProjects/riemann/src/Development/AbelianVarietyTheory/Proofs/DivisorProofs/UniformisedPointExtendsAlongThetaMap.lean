import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpacePointOfUnitCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapCoordsOfSymmetricThetaIsomorphicFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSymmetricFunctionValuesInGroundFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonvanishingClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsIntegralUnitNormalLocalDoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesSectionsOfThetaSymmetricFunctionsNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ExtP

theorem genericFibre_polAV : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c) (t : SAB H (Sp R)), GenOf Xo c y t → ∃ (P : PolAV (Sp (FractionRing R))) (α : P.A.left ⟶ Xo.univ.t.G.left) (α' : P.A.left ⟶ t.G.left), P.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) ∧ IsGrpPullback P.A Xo.univ.t.G (y ≫ pullback.fst _ _) α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α) ∧ IsGrpPullback P.A t.G (jK R) α' ∧ LBIso P.L (t.PP.L.pull α') := by
  intro E _ _ _ H Dw l Xo c R _ _ y t hy
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hy
  have hw₁ : LBIso tK.PP.L (t.PP.L.pull m₁.cm.F) := by
    obtain ⟨w, hw, -⟩ := m₁.lin; exact ⟨w, hw⟩
  have hw₂ : LBIso tK.PP.L (Xo.univ.t.PP.L.pull m₂.cm.F) := by
    obtain ⟨w, hw, -⟩ := m₂.lin; exact ⟨w, hw⟩
  have hd := GlobalTheory.UMin.polFib_univ E H Dw l Xo c (FractionRing R) (𝟙 _ ≫ y ≫ pullback.fst _ _)
  obtain ⟨P, α₀, hgP, hpb₀, hL₀⟩ := ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ Xo.univ.t.G Xo.univ.t.PP.L tK.G tK.PP.L
    (y ≫ pullback.fst _ _) m₂.cm.F Xo.univ.t.PP.isLB tK.PP.isLB m₂.cart hw₂ _ (FractionRing R) (𝟙 _)).1).2 hd
  refine ⟨P, α₀ ≫ m₂.cm.F, α₀ ≫ m₁.cm.F, hgP, ?_, ?_, ?_, ?_⟩
  · have h := hpb₀.comp m₂.cart
    rwa [Category.id_comp] at h
  · exact LBIso.trans P.isLB (pull_isLB tK.PP.isLB α₀) (pull_isLB Xo.univ.t.PP.isLB _) hL₀
      (GlobalTheory.Ex.GenericFibre.lbIso_pull hw₂ α₀ rfl)
  · have h := hpb₀.comp m₁.cart
    rwa [Category.id_comp] at h
  · exact LBIso.trans P.isLB (pull_isLB tK.PP.isLB α₀) (pull_isLB t.PP.isLB _) hL₀
      (GlobalTheory.Ex.GenericFibre.lbIso_pull hw₁ α₀ rfl)

theorem extend_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ b : o →+* c.F, f ≫ PSpace.str o n = pullback.snd _ _ ≫ spMap b → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t → ∀ σ : Sp R ⟶ Sp o, jK R ≫ σ = y ≫ pullback.snd _ _ ≫ spMap b → ∃ ξ : Sp R ⟶ PSpace o n, jK R ≫ ξ = y ≫ f ∧ ξ ≫ PSpace.str o n = σ := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm h3 hmu hn hTh b hb R _ _ _ hR t hP y hy σ hσ
  haveI : IsNoetherianRing R := hR.1.1
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hgdef
  obtain ⟨σ₀, hnz⟩ := GlobalTheory.T.exists_polarisation_section_nonvanishing_closed_fibre E H R hR t hP
  obtain ⟨P, α, α', hg, hpb, hL, hpb', hL'⟩ := genericFibre_polAV E H Dw l Xo c R y t hy
  have hpb₁ : IsGrpPullback P.A t.G (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) α' := by
    rw [Category.comp_id]; exact hpb'
  have hpf : PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) := ⟨P, α', hg, hpb₁, hL'⟩
  let θ := SecAt.pull t.G t.PP.L σ₀ (algebraMap R (FractionRing R))
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field (Sp R) t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m (n + 1) (FractionRing R)
    (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) θ hm hn hpf
  let β : o →+* R := (Spec.preimage σ).hom
  have hβ : spMap β = σ := Spec.map_preimage σ
  have hmR : IsUnit (m : R) := by simpa [β] using hmu.map β
  obtain ⟨e', he', j, hj⟩ := GlobalTheory.T.thetaSymmetricFunctions_integral_unit_normalLocalDomain E H (Sp R) t g m (n + 1) R (𝟙 _) σ₀ e hm h3 hmR hn hpf hnz he
  have hne : ∃ j, e j ≠ 0 := ⟨j, fun h0 => hj.ne_zero (IsFractionRing.injective R (FractionRing R)
    ((he' j).trans (h0.trans (map_zero _).symm)))⟩
  have hgen := GlobalTheory.T.generates_sections_of_thetaSymmetricFunctions_ne_zero (Sp R) t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m (n + 1) (FractionRing R) _ θ e hm hn hpf he hne
  have hcrd : PCrd (y ≫ f) e := GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB
    Xo.univ.t.PP.rigGen g m n o (Xo.XF c) (pullback.fst _ _) f (Sp R) t.G t.PP.L t.PP.rig (FractionRing R) y
    (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) P α α' θ e hm hn hTh t.PP.isLB t.PP.rigGen hg hpb hL hpb₁ hL'
    hgen he
  obtain ⟨ξ, hξ1, hξ2⟩ := GlobalTheory.T.exists_projectiveSpace_point_of_unit_coordinate o R n β e' ⟨j, hj⟩
  refine ⟨ξ, ?_, hξ1.trans hβ⟩
  have hc1 : PCrd (jK R ≫ ξ) e := by
    have := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties).1 o R (FractionRing R) n ξ e' (algebraMap R (FractionRing R)) hξ2
    have ee : (fun j => algebraMap R (FractionRing R) (e' j)) = e := funext he'
    rw [ee] at this; exact this
  refine (GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend).1 o (FractionRing R) n (jK R ≫ ξ) (y ≫ f) e ?_ hc1 hcrd
  rw [Category.assoc, hξ1, hβ, Category.assoc, hb]; exact hσ

end GlobalTheory.UMin.ExtP
