import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfSmallTraits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHasDivOfGenericPointProjectiveCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMapOfModelHasDivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCoordinatesO1FactorialPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelSemiAbelianRelDimCotangentVectorBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCoordinatesSectionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivOfHasDivThetaSymmetricFunctionsDegreeFactoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesianStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

section Moves

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}

theorem hasTh_of_sabMap (mm : SABMap t' t f) (m : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S') {N : ℕ}
    (c : Fin N → K) :
    HasTh t'.G t'.PP.L t'.PP.rig m x c ↔ HasTh t.G t.PP.L t.PP.rig m (x ≫ f) c := by
  rw [hasTh_iff, hasTh_iff]
  exact GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen S' t'.G t'.PP.L t'.PP.rig f mm.φ t'.PP.isLB
    t'.PP.rigGen mm.cart (GlobalTheory.ModelSum.lbIso_of_map mm) m m N N K x c c

theorem polFib_of_sabMap (mm : SABMap t' t f) (g : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ S') :
    PolFib t'.G t'.PP.L g x ↔ PolFib t.G t.PP.L g (x ≫ f) :=
  (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S' t.G t.PP.L t'.G t'.PP.L f mm.φ t.PP.isLB t'.PP.isLB mm.cart
    (GlobalTheory.ModelSum.lbIso_of_map mm) g R x).1

end Moves

end GlobalTheory.UMin

namespace GlobalTheory.UMin

open GlobalTheory.CechPic in

theorem key_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (π : M.Z ⟶ Y.X) (y : Sp Ω ⟶ Xo.XF c) (d : Fin (n + 1) → Ω), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ π = y ≫ Y.j → HasTh Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (y ≫ pullback.fst _ _) d → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) 8).pull π) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial)).pull π) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf Y g hYg Ω _ _ _ M π y d hZ hpt hth
  obtain ⟨t, ⟨mt⟩⟩ := GlobalTheory.ModelSum.exists_pull π Y.t
  have hP : PCrd (M.pt ≫ (π ≫ g)) (symTup d) := by
    have h1 : M.pt ≫ (π ≫ g) = y ≫ f := by rw [← Category.assoc, hpt, Category.assoc, hYg]
    rw [h1]; exact hf Ω y d hth
  have hD : M.HasDiv d :=
    GlobalTheory.T.hasDiv_of_hasDiv_thetaSymmetricFunctionsDegreeFactorial c.F Ω M (n + 1) d hZ (GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords c.F Ω o M n (π ≫ g) (symTup d) hP)
  obtain ⟨h, -, hhP⟩ := GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv c.F Ω M n d hD
  have hsym := GlobalTheory.T.symmetric_coordinates_O1_factorial_power c.F Ω o M n h (π ≫ g) d hhP hP
  have hThO : HasTh Y.oF.t.G Y.oF.t.PP.L Y.oF.t.PP.rig m y d := (hasTh_of_sabMap Y.m0.toSABMap m y d).2 hth
  have hThY : HasTh Y.t.G Y.t.PP.L Y.t.PP.rig m (M.pt ≫ π) d := by
    rw [hpt]; exact (hasTh_of_sabMap Y.m m y d).1 hThO
  have hTh : HasTh t.G t.PP.L t.PP.rig m M.pt d := (hasTh_of_sabMap mt m M.pt d).2 hThY
  have hPolO : PolFib Y.oF.t.G Y.oF.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) y :=
    (polFib_of_sabMap Y.m0.toSABMap _ y).2 (GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c Ω _)
  have hPolY : PolFib Y.t.G Y.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (M.pt ≫ π) := by
    rw [hpt]; exact (polFib_of_sabMap Y.m _ y).1 hPolO
  have hPol : PolFib t.G t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) M.pt := (polFib_of_sabMap mt _ M.pt).2 hPolY
  have hmk : IsUnit (m : c.F) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (by omega))
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.theta_coordinates_section_exists E H c.F Ω M t _ m n d h hZ hm hm3 hmk hPol hTh hhP
  obtain ⟨hab, hop, hamp⟩ := GlobalTheory.T.abelianLocus_eq_preimage_moduli_and_principal E H Dw l Xo c Y M.Z π t ⟨mt⟩
  obtain ⟨hsmY, hvY⟩ := GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y
  have hsm : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback mt.cart.1 hsmY
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have hne : ((⊤ : M.Z.Opens) : Set M.Z).Nonempty := ⟨M.pt (IsLocalRing.closedPoint Ω), trivial⟩
  haveI : CharZero Γ(M.Z, ⊤) := (M.res ⊤ hne).charZero
  have hne2 : (abLocus t.G).Nonempty := by
    refine ⟨M.pt (IsLocalRing.closedPoint Ω), ?_⟩
    rw [hab]
    show π (M.pt (IsLocalRing.closedPoint Ω)) ∈ Set.range Y.j
    have hq := congrArg (fun φ : Sp Ω ⟶ Y.X => φ (IsLocalRing.closedPoint Ω)) hpt
    exact ⟨y (IsLocalRing.closedPoint Ω), hq.symm⟩
  have hδ : ((ProjSpace.O1 c.F n).pull h).IsLB := pull_isLB (ProjSpace.O1_isLB c.F n) h
  have := Y.t.semi.separated
  have hHY := hvY.isLB_det
  have hHt := (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback mt.cart hvY).isLB_det
  have hkey : LBIso (lbPow ((ProjSpace.O1 c.F n).pull h) 8)
      (lbPow (GlobalTheory.SiegelTor.hodge t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) 4) := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) with h0 | h0
    · have hn0 : n = 0 := by
        rw [h0] at hn
        simpa using hn
      subst hn0
      refine (cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hHt 4)).1 ?_
      have hz : cls _ hHt = 0 := by
        revert hHt
        rw [h0]
        exact fun hHt => KeySmall.cls_det_zero _ hHt
      rw [cls_lbPow hδ, cls_lbPow hHt, hz, cls_pull (ProjSpace.O1_isLB c.F 0), KeySmall.cls_O1_zero, map_zero,
        nsmul_zero, nsmul_zero]
    · refine KeySmall.key_sab M.Z t _ _ σ h0 hZ inferInstance inferInstance (fun A _ ξ hξ => ?_) hsm hne2 hop hδ hamp
        (KeySmall.nzFib_of_geom σ hσ)
      exact KeySmall.mk_le_of_lft ((Cardinal.mk_le_of_injective (f := fun a : c.F => (a : ℂ)) Subtype.val_injective).trans_eq
        Cardinal.mk_complex) (ξ ≫ M.s)
  have hO := ProjSpace.O1_isLB o n
  have e1 := (cls_eq_iff (pull_isLB hO (π ≫ g)) (isLB_lbPow hδ _)).2 hsym
  have e2 := (cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hHt 4)).2 hkey
  have e3 := (cls_eq_iff (pull_isLB hHY π) hHt).2 (GlobalTheory.HodgeGenDesc.lbIso_hodge_pull mt.cart hvY)
  rw [cls_pull hO, pull_comp, cls_lbPow hδ] at e1
  rw [cls_lbPow hδ, cls_lbPow hHt] at e2
  rw [cls_pull hHY] at e3
  refine (cls_eq_iff (pull_isLB (isLB_lbPow (pull_isLB hO g) 8) π) (pull_isLB (isLB_lbPow hHY _) π)).1 ?_
  rw [cls_pull (isLB_lbPow (pull_isLB hO g) 8), cls_pull (isLB_lbPow hHY _), cls_lbPow (pull_isLB hO g),
    cls_lbPow hHY, map_nsmul, map_nsmul, cls_pull hO, e1, e3, smul_smul, mul_comm 8, ← smul_smul, e2, smul_smul,
    mul_comm]

end GlobalTheory.UMin

end
