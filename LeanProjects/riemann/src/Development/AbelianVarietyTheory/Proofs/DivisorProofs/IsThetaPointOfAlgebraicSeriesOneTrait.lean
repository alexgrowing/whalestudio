import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricValuesIsoOfIdentificationDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisationGeneratingSectionPullbackLocalBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsCoordsRelabelledTwistedDataSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.OneTraitTheta

open GlobalTheory GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport GlobalTheory.ValuesPullIso GlobalTheory.LabTrans
open GlobalTheory.PsiEvenPull (proj)

theorem exists_values_iso (hL : Laws) {R R' : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F]
    [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (hF : Compat φ F) {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') : ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧
      ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' →
        IsPullGtF φ hD F g g' → I.Rel c' c := by
  let z : Sp F := IsLocalRing.closedPoint F
  obtain ⟨th', h₁, h₂⟩ := GeneratorPull.exists_generator_pull hL R R' φ D.P D'.P _ hD.w (pull_grp hD) hD.w_gen ν.th ν.th_gen
  obtain ⟨c, hc⟩ := ν'.th_gen th'
  obtain ⟨c', hc'⟩ := h₁ ν'.th
  have key : ∀ x : TF (R := R') F ⟶ D'.P.A, sval (Z := Sp F) ν.th (x.left ≫ proj hD) z ν.J =
      (om hD.w z ν.J ν'.J x.left).val * sval (Z := Sp F) th' x.left z ν'.J := fun x =>
    h₂ (Sp F) x.left z ν.J ν'.J (good ν z) (good ν' z)
  have k₁ := fun x : TF (R := R') F ⟶ D'.P.A =>
    IndivisibleSection.sval_of_secIsMul (p := D'.P.A.hom) hc (show Sp F ⟶ _ from x.left) z (good ν' z)
  have k₂ := fun x : TF (R := R') F ⟶ D'.P.A =>
    IndivisibleSection.sval_of_secIsMul (p := D'.P.A.hom) hc' (show Sp F ⟶ _ from x.left) z (good ν' z)
  by_cases h : c = 0
  · subst h
    refine exists_iso_of_th hD hL.globalFns hF ν ν' z 1 fun x => ?_
    have e₁ := k₁ x
    rw [GenSecField.cst_zero', zero_mul] at e₁
    have e₂ := k₂ x
    rw [e₁, mul_zero] at e₂
    exact ((key x).trans ((congrArg _ e₁).trans (mul_zero _))).trans ((congrArg _ e₂).trans (mul_zero _)).symm
  · let u : (FractionRing R')ˣ := Units.mk0 (algebraMap R' _ c) fun e =>
      h (IsFractionRing.injective R' (FractionRing R') (e.trans (map_zero _).symm))
    refine exists_iso_of_th hD hL.globalFns hF ν ν' z (TauTwist.unitAt (Z := Sp F) (jFK (R := R') F) z u) fun x => ?_
    refine ((key x).trans (congrArg _ (k₁ x))).trans ((_root_.mul_assoc _ _ _).symm.trans (congrArg₂ (· * ·) ?_ rfl))
    rw [Units.val_mul, TauTwist.unitAt_val]
    refine (_root_.mul_comm _ _).trans (congrArg₂ (· * ·) ?_ rfl)
    exact (congrArg (fun q => cst (Z := Sp F) q z c) (Over.w x)).trans
      (cst_comp (Z := Sp F) (jFK (R := R') F) (algebraMap R' (FractionRing R')) z c)

theorem exists_scalar {K C I : Type} [Field K] [Field C] (f : K →+* C) {v t : I → K} (s : Cˣ)
    (h : ∀ i, f (v i) = s * f (t i)) : ∃ c : K, c ≠ 0 ∧ ∀ i, v i = c * t i := by
  by_cases h₀ : ∀ i, t i = 0
  · exact ⟨1, one_ne_zero, fun i => f.injective (by rw [h, h₀]; simp)⟩
  · obtain ⟨i, hi⟩ := not_forall.1 h₀
    have hi' : f (t i) ≠ 0 := (map_ne_zero f).2 hi
    have e : f (v i / t i) = s := by rw [map_div₀, h, mul_div_cancel_right₀ _ hi']
    exact ⟨v i / t i, fun h₁ => s.ne_zero (by rw [← e, h₁, map_zero]), fun l => f.injective (by rw [map_mul, e, h])⟩

theorem isThetaPt_descend (hL : Laws) (hL₂ : Laws2) {S S' : Scheme.{0}} [IsLocallyNoetherian S] [IsLocallyNoetherian S']
    {P : PolAV S} {P' : PolAV S'} {f : S' ⟶ S} {a : P'.A.left ⟶ P.A.left} (hp : IsGrpPullback P'.A P.A f a)
    (hw : LBIso P'.L (P.L.pull a)) {K C : Type} [Field K] [Field C] [IsAlgClosed C] (em : K →+* C) (s : Sp K ⟶ S)
    (s' : Sp C ⟶ S') (hs : spMap em ≫ s = s' ≫ f) {m : ℕ} (hm : Odd m) (hmK : (m : K) ≠ 0) {I : Type}
    (x : I → (Over.mk s ⟶ P.A)) (x' : I → (Over.mk s' ⟶ P'.A)) (hx : ∀ i, (x' i).left ≫ a = spMap em ≫ (x i).left)
    (hk : ∀ i, x' i ^ m ^ 2 = 1) {w : I → C} (hw' : IsThetaPt P' m x' fun i => fnOf (w i)) {v : I → K} (c : Cˣ)
    (hv : ∀ i, em (v i) = c * w i) : IsThetaPt P m x fun i => fnOf (v i) := by
  have hmC : (m : C) ≠ 0 := by rw [← map_natCast em]; exact (map_ne_zero em).2 hmK
  let U : Over.mk (s' ≫ f) ⟶ Over.mk s := Over.homMk (spMap em) hs
  obtain ⟨e, he⟩ : ∃ e : (Over.mk s' ⟶ P'.A) ≃* (Over.mk (s' ≫ f) ⟶ P.A), ∀ y, (e y).left = y.left ≫ a :=
    LiePull.exists_pushEquiv hp (Over.mk s') _ rfl
  have hU : ∀ i, U ≫ x i = e (x' i) := fun i => Over.OverMorphism.ext ((hx i).symm.trans (he _).symm)
  have hkU : ∀ i, (U ≫ x i) ^ m ^ 2 = 1 := fun i => by rw [hU, ← map_pow, hk, map_one]
  have hkx : ∀ i, x i ^ m ^ 2 = 1 := fun i => by
    letI := em.toAlgebra
    haveI : Flat (spMap em) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat K C)
    haveI : Surjective (spMap em) := ⟨fun p => ⟨(⊥ : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
    haveI : Epi (spMap em) := Flat.epi_of_flat_of_surjective (spMap em)
    have E : U ≫ (x i ^ m ^ 2) = U ≫ 1 := by rw [MonObj.comp_pow, hkU, MonObj.comp_one]
    exact Over.OverMorphism.ext ((cancel_epi (spMap em)).1 (congrArg (fun q => q.left) E))
  obtain ⟨t, ht⟩ := Specialise.exists_isThetaPt_local hL hL₂ P s hm (IsUnit.mk0 _ hmK) x hkx
  have T₁ := Specialise.isThetaPt_map hL₂ P em hs ht
  have T₂ := ((CoordSep.coord_exists_unique_separate hL C _ P (s' ≫ f) m hm hmC I (fun i => U ≫ x i) hkU).2.2.1
    fun i => em (t i)).1 T₁
  let τ : (Over.mk s').left ⟶ (Over.mk (s' ≫ f)).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have T₃ : IsCoordPt P' m x' 1 fun i => fnOf (em (t i)) :=
    FullExtend.isCoordPt_move τ hp hw τ (𝟙 _) (Category.comp_id _) (Category.id_comp _) (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id P.A P.isLB 1 (SecM.ofSec P.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      (fun i => (Category.id_comp _).trans (hx i).symm) hk (z := 1)
      ((Category.id_comp _).trans (by rw [← he, map_one])) T₂
  obtain ⟨-, h₂, h₃, -⟩ := CoordSep.coord_exists_unique_separate hL C _ P' s' m hm hmC I x' hk
  obtain ⟨d, hd⟩ := (h₂ 1 _ w T₃).1 ((h₃ w).1 hw')
  obtain ⟨c', hc', hv'⟩ := exists_scalar em (v := v) (t := t) (c * d) fun i => by
    rw [hv, hd, Units.val_mul, _root_.mul_assoc]; rfl
  rw [show v = fun i => c' * t i from funext hv']
  exact Specialise.isThetaPt_mul P ht hc'

theorem isThetaPt_of_series : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → ∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) := by
  intro R _ _ _ hR D A lab n hn ho _ hT j v hv
  obtain ⟨W, _, _, _, φ, G, _, _, D', A', U', hD, a, _, em₀, hW, iφ, lφ, hG, ⟨ga, hga, gp, lb⟩, c₀, H₀⟩ := hT
  have hV := GlobalTheory.lawsAndExpansions
  have hL : Laws := hV.1.1
  have hL₂ : Laws2 := hV.1.2.1
  have hGF := hL.globalFns
  have := hR.2
  have := hR.1.1
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have b₀ : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hm : Odd (n ^ j) := ho.pow
  have hk : 1 ≤ (n ^ j) ^ 2 := pow_pos hm.pos 2
  generalize n ^ j = m at *
  obtain ⟨C, _, _, _, _, _, gam, hgam, hC⟩ := exists_complete_isAlgClosed_cExt W (Kb W)
  have : CharZero C := (RingHom.charZero_iff (algebraMap (FractionRing W) C).injective).1 inferInstance
  letI : Algebra (FractionRing R) C := ((algebraMap (FractionRing W) C).comp ga).toAlgebra
  have cC : Compat φ C := fun r => congrArg (algebraMap (FractionRing W) C) (hga r)
  have a₀K : algebraMap (FractionRing R) (Kb W) = (algebraMap (FractionRing W) (Kb W)).comp ga :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
      (congrArg (algebraMap (FractionRing W) (Kb W)) (hga r).symm))
  let jW : Kb W →ₐ[FractionRing W] C := ⟨gam, hgam⟩
  let jR : Kb W →ₐ[FractionRing R] C := ⟨gam, fun t => by rw [a₀K]; exact hgam (ga t)⟩
  have hCR : CExt R (maximalIdeal R) C :=
    ⟨fun r => (cC r).symm ▸ hC.1 _, fun r hr => (cC r).symm ▸ hC.2 _ (map_nonunit φ r hr)⟩
  obtain ⟨N, ν, -⟩ := ValuesExist.exists_integral_values hL R D.toPre D.psi_even hB C ⊤ fun _ => trivial
  obtain ⟨N', ν', -⟩ := ValuesExist.exists_integral_values hL W D'.toPre D'.psi_even D'.tau_bimult C ⊤ fun _ => trivial
  obtain ⟨J, hJX, hJ⟩ := exists_values_iso hL hD cC ν ν'
  obtain ⟨f, hf, hf'⟩ := GlobalTheory.TorsionIso.torsion_clause W _ b₀ D' A' G hG U' C (m ^ 2) hk
  have ex : ∀ i : QkPt D.toPre (Kb R) (m ^ 2), ∃ (p₁ : QkPt D.toPre C (m ^ 2)) (p' : QkPt D'.toPre C (m ^ 2))
      (x' : TFK (R := W) C ⟶ A'.A), QkExt (jR.comp em₀).toRingHom i p₁ ∧ p'.y = hD.xe.symm p₁.y ∧
      IsPullGtF φ hD C p₁.g p'.g ∧ x'.left ≫ a = spMap (jR.comp em₀).toRingHom ≫ (lab _ i).left ∧
      QkToAkU U'.toUnifPre C (m ^ 2) p' x' := fun i => by
    obtain ⟨q₁, hq₁⟩ := exists_ext hB em₀ i
    obtain ⟨r, hr⟩ := exists_ext hB jR q₁
    let q₀ := pullQk hD hGF c₀ hB D'.tau_bimult q₁
    obtain ⟨x₀, hx₀⟩ := exists_lift_pt gp.1 em₀.toRingHom (em₀.comp_algebraMap.trans a₀K) (lab _ i)
    have t₀ := H₀ _ hk i q₁ q₀ x₀ hq₁ rfl (isPullGtF_pullGt hD hGF c₀ _) hx₀
    obtain ⟨⟨q₀', hq₀'⟩, hx, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W _ b₀ D' A' G hG U' _ C jW _ hk q₀
    obtain ⟨x₀', hx₀'⟩ := hx x₀
    refine ⟨r, q₀', x₀', qkExt_trans hq₁ hr, ?_,
      isPullGtF_ext hD cC jW.toRingHom jW.comp_algebraMap (isPullGtF_pullGt hD hGF c₀ _) hr hq₀', ?_,
      (hgal q₀' x₀ x₀' hq₀' hx₀').1 t₀⟩
    · rw [hq₀'.1, hr.1]; rfl
    · rw [hx₀', Category.assoc, hx₀, ← Category.assoc, ← Geo.Tor.spMap_comp]; rfl
  choose p₁ p' x' e₁ e₂ e₃ e₄ e₅ using ex
  have hGt := GlobalTheory.T.torus_torsion_points_correspond_values
  choose q hq using fun i => (((hGt R D.toPre D.psi_even hB C N ν).2.2.2.2 _).1 (p₁ i)).exists
  choose q' hq' using fun i => (((hGt W D'.toPre D'.psi_even D'.tau_bimult C N' ν').2.2.2.2 _).1 (p' i)).exists
  obtain ⟨s, hs⟩ := hv C hCR (jR.comp em₀) N ν p₁ q e₁ hq
  have Q := GlobalTheory.T.theta_constants_eq_degeneration_series hV hGt (GlobalTheory.T.families_values_correspond hL hL₂) W _ hW rfl D' A' G hG U' C hC N' ν' m hm _ p' q' x' e₅ hq'
  have : CharZero (Kb R) := (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  refine isThetaPt_descend hL hL₂ gp lb (jR.comp em₀).toRingHom (jFK (R := R) (Kb R)) (jFK (R := W) C) ?_ hm
    (Nat.cast_ne_zero.2 hm.pos.ne') (lab _) x' e₄ (fun i => ?_) Q (s * J.lam) fun i => ?_
  · exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap (jR.comp em₀).comp_algebraMap).trans (Geo.Tor.spMap_comp _ _))
  · rw [(hf.1 _ _).1 (e₅ i)]; exact hf' _
  · have e := (RelabelCoords.series_iso J hm (p := q' i) (p' := q i) (ν.eX.injective (by
      rw [hJX, (hq i).1, (hq' i).1, e₂, AddEquiv.apply_symm_apply])) (hJ _ _ _ _ (hq i).2 (hq' i).2 (e₃ i))).1
    rw [e, Units.val_mul, _root_.mul_assoc, Units.mul_inv_cancel_left]
    exact hs i

end GlobalTheory.Mum.OneTraitTheta

end
