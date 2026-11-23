import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsMemNormalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantLevelSquareNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.MapAff

theorem theta_map_aff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o R : Type) [CommRing o] [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (β : o →+* R) (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → 3 ≤ m → IsUnit (m : R) → n + 1 = m ^ (4 * g) → PolFib G L g x → (∀ (K : Type) [Field K] (i : R →+* K), IsGenSec G L _ (SecAt.pull G L θ i)) → ∃ f : Sp R ⟶ PSpace o n, f ≫ PSpace.str o n = spMap β ∧ ThMap G L ρ m x f := by
  intro S G _ _ L ρ hL hρ g m n o R _ _ _ _ _ _ β x θ hm hm3 hmu hn hpol hgen
  obtain ⟨e, he⟩ := GlobalTheory.T.thetaSymmetricFunctions_mem_normalDomain S G L ρ hL hρ g m (n + 1) R x θ hm hmu hn hpol
  have hpolK : ∀ (K : Type) [Field K] (i : R →+* K), PolFib G L g (spMap i ≫ x) := fun K _ i =>
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S G L G L (𝟙 S) (𝟙 G.left) hL hL (GlobalTheory.SiegLower.isGrpPullback_id G)
      (GlobalTheory.SiegLower.lbIso_pull_id hL) g R x).2 K i hpol
  have hspan : Ideal.span (Set.range e) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    letI := Ideal.Quotient.field M
    let i : R →+* AlgebraicClosure (R ⧸ M) := (algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).comp (Ideal.Quotient.mk M)
    have hmK : ((m : ℕ) : AlgebraicClosure (R ⧸ M)) ≠ 0 := by
      have := hmu.map i
      rw [map_natCast] at this
      exact this.ne_zero
    have hpK := hpolK _ i
    obtain ⟨pt, c, hl⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m (n + 1) _ (spMap i ≫ x) (SecAt.pull G L θ i) hm hmK hn hpK
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_thetaConstant_levelSquare_ne_zero S G L ρ hL hρ g m (n + 1) _ (spMap i ≫ x) c hm hm3 hmK hpK ⟨_, pt, hgen _ i, hl⟩
    obtain ⟨j, hj⟩ := GlobalTheory.UMin.symTup_basic.2.2.2 _ (n + 1) c ⟨a, ha⟩
    apply hj
    rw [← he _ i pt c hl j]
    have hM' : e j ∈ M := hle (Ideal.subset_span ⟨j, rfl⟩)
    simp [i, Ideal.Quotient.eq_zero_iff_mem.2 hM']
  have hstr := GlobalTheory.ProjSpace.pt_str β e hspan
  have hf : PCrd (GlobalTheory.ProjSpace.pt β e hspan) e := (GlobalTheory.UMin.CrdUniq.pCrd_iff _ β hstr e).2 ⟨hspan, rfl⟩
  refine ⟨GlobalTheory.ProjSpace.pt β e hspan, hstr, ?_⟩
  intro K _ x' c ⟨θ', pt, hθ', hl⟩
  obtain ⟨i, rfl⟩ := GlobalTheory.UMin.CrdUniq.exists_spMap' x'
  obtain ⟨r, hr⟩ := hθ' (SecAt.pull G L θ i)
  have hsm : SecM.ofSec G (SecAt.pull G L θ i) = r • SecM.ofSec G θ' := Subtype.ext (funext hr)
  set a : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r with ha
  have hra : GlobalTheory.ZH.fn a = r := by
    simp [GlobalTheory.ZH.fn, a]
  have hl0 : ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun b => a * c b) := by
    refine ⟨hl.1, fun b => ?_, hl.2.2⟩
    have h1 := GlobalTheory.Ex.OneGen.ThG.smul hL hsm (hl.2.1 b)
    convert h1 using 1
    rw [← hra]
    exact map_mul _ _ _
  have h2 : PCrd (spMap i ≫ GlobalTheory.ProjSpace.pt β e hspan) (fun j => a ^ (n + 1).factorial * symTup c j) := by
    have := GlobalTheory.T.projectiveHomogeneousCoords_basic_properties.1 o R K n _ e i hf
    convert this using 2 with j
    rw [he K i pt _ hl0 j, GlobalTheory.UMin.symTup_basic.1]
  have ha0 : a ≠ 0 := by
    rintro h0
    obtain ⟨j, hj⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties.2.2 o K n _).2 _ h2
    apply hj
    simp [h0, Nat.factorial_ne_zero]
  have h3 := GlobalTheory.T.projectiveHomogeneousCoords_basic_properties.2.1 o K n _ _ ((a ^ (n + 1).factorial)⁻¹) (isUnit_iff_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ha0))) h2
  convert h3 using 1
  funext j
  rw [inv_mul_cancel_left₀ (pow_ne_zero _ ha0)]

end GlobalTheory.UMin.MapAff
