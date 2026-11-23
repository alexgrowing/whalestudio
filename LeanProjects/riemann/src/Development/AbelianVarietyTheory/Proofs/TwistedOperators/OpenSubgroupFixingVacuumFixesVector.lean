import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelUnitaryHeckeCharacterTrivialCongruencStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFrameCongruenceUnitaryAdelicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardPairFirstInvariantCongruenceOneStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.RowTest

theorem IsBottomTri.exists_open_fix_f : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac →
      X.ω t (1, κ) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  have h := hX.is
  have hom := h.weil t
  have hT2 : IsHeckeChar D ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) / (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))) :=
    hom.hecT
  have hx : ∀ x, ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) x =
      (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) / (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))) x)⁻¹ := fun x => by
    rw [MonoidHom.div_apply, MonoidHom.div_apply, inv_div]
  have hνH : IsHeckeChar D ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) :=
    ⟨hT2.1.inv.congr fun x => (hx x).symm, fun x => by rw [hx, hT2.2, inv_one]⟩
  obtain ⟨N₀, hN₀, hN₀'⟩ := GlobalTheory.T.exists_level_unitaryHeckeCharacter_trivial_congruence D _ hνH
  have hI : X.ideal (locPl G) t ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  set N : ℕ := N₀ * Ideal.absNorm (X.ideal (locPl G) t) * ∏ w ∈ locPl G t, Ideal.absNorm w.asIdeal with hNdef
  have hNpos : 0 < N := by
    refine Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hN₀.ne' ?_) (Finset.prod_ne_zero_iff.2 fun w _ => ?_))
    · exact fun h0 => hI (Ideal.absNorm_eq_zero_iff.1 h0)
    · exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hNI : ((N : ℕ) : 𝓞 D.host.E) ∈ X.ideal (locPl G) t := by
    rw [hNdef, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))
  have hNw : ∀ w ∈ locPl G t, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := fun w hw => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w : Formalism.L2.DIV.Pl D.host.E => Ideal.absNorm w.asIdeal) hw
    rw [hNdef, hc, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))
  have hNdiv : N₀ ∣ N := ⟨Ideal.absNorm (X.ideal (locPl G) t) * ∏ w ∈ locPl G t, Ideal.absNorm w.asIdeal, by rw [hNdef, mul_assoc]⟩
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.exists_open_frame_congruence_unitaryAdelic D WW X.rW.β N hNpos
  refine ⟨U, hUo, fun κ hκ _ hvac => ?_⟩
  obtain ⟨z, hz, hzc⟩ := hU κ hκ
  have hst : Lev.finE WW κ ∈ Formalism.L2.DIV.St X.rW.β := ⟨z, hz⟩
  have hinv := GlobalTheory.T.standardPairFirst_invariant_congruenceOne D A WW _ (X.e t) (locPl G t) (h.idem t) (X.ideal (locPl G) t) X.rA.β X.rW.β N hNpos hNI hNw
    (hN₀' N hNdiv) κ z hz hzc
  have hsdA := isSelfDualC_neg' h.rigA.1
  have hsdW := h.rigW.1
  have hsg : ∀ f, (X.ω t).toSgn true (1, κ) f = X.ω t (1, κ) f := fun f => by
    simp [GlobalTheory.Grid.WRep.toSgn]
  have key := GlobalTheory.ExportSeries.DualType.om_theta_move hom
    (fun Tm hT Ψ hΨ => GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ h.isVac.1 _ WW _ _ hsdA hsdW _
      (GlobalTheory.PlaceDatum.idemSum_mul_self (h.idem t)) (GlobalTheory.PlaceDatum.infPart_idemSum (h.idem t)) _ h.isVac.2.theta Tm hT Ψ hΨ)
    (h.fst t) (h.fst t) (g := 1) (h := κ)
    (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D _ WW _ _ _ _ hsdA hsdW h.rigA.2.1 h.rigW.2.1 1 κ (by rw [map_one]; exact one_mem _) hst)
    one_ne_zero (c' := 1) (by rw [one_smul, hsg]; exact hvac) (fun x => by rw [one_mul, hinv x])
  rw [hsg, one_mul, one_smul] at key
  exact key

end GlobalTheory.RowTest

end
