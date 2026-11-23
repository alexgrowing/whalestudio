import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoiceGoodChartsEveryStageStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnOrthonormalCoordsEqGivenStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeTrueColumnBaseLatticeEqStandardStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HServTwoSidesJoint0
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnTupleKernelsRationalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelCoefficientFieldLeCoefficientFieldStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceUnderTwistPrimeOverTupleRamifiedPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnKernelDataCompatibleStepChartsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Port.jIn_nonempty_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → ∀ (u : B.Word) (a : I.ι), Nonempty (GlobalTheory.Port.JIn t u a) := by
  intro B X I hI hP l Z l0 L hT Gi Gl K Y cX ex t C full g hTw hJets hex hpi hSK hRd hpin hSC hDt hherm hforms hchiD u a
  classical
  let Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) := (I.Q a).image (fun P => P.under (𝓞 B.host.F))
  have hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v := by
    intro v
    exact Finset.mem_image
  obtain ⟨Ch, chOf, eY, Kc, hK, hCh0, hlev0, hy0⟩ := GlobalTheory.T.trueColumnChoice_goodCharts_every_stage I hI hP l Z u (C.forms u) a Q hQ (hSC u)
  have hbad : ∀ v ∈ badQ (I.rec7 l Z) Q, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v := by
    intro v hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr ((hQ v).1 hv)
  obtain ⟨A, hpins, htie⟩ := GlobalTheory.T.trueColumn_kernelData_compatible_stepCharts I hI hP l Z L hT Gi Gl K Y cX ex t u a (badQ (I.rec7 l Z) Q) Ch chOf eY Kc
    full.1.base.dt hTw hSK hRd hpin hpi hDt hbad
    (fun i hi => ⟨(hK i hi).2.2.1.readsK, (hK i hi).2.1⟩) (fun i hi β => ((hK i hi).2.2.2 β).1)
    (fun i hi β => by
      obtain ⟨n, hn, h⟩ := ((hK i hi).2.2.2 β).2
      exact ⟨n, hn, fun κ _ => h κ⟩) (fun _ i hi c y hy => by
    obtain ⟨k, hR, hk1⟩ := (hK i hi).2.2.1
    obtain ⟨p, hp, hN⟩ := hR.k_std (chOf i hi c)
    have e := GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level B.R B.host _ _ _ _ I.SQ _ _ (k (chOf i hi c)) y
      (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1 (hR.pt c) hp.uni (hN ▸ hp.lat)
      (fun P hP => hk1 _ _ (GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P hP)) hy
    obtain ⟨b, hb⟩ := GlobalTheory.Mem.Col2.FullDt.exists_lift B.host y
    rw [e, GlobalTheory.Mem.Col2.FullDt.normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ y b hb, hDt y b hb])
  have hf : g.forms u = (C.forms u).to0 := congrFun hforms u
  refine ⟨{
      Gd := g
      Hh := full.1.base
      rel := full.1.relDet
      St := charts I l Z u a (badQ (I.rec7 l Z) Q) Ch chOf eY Kc
      A := A
      a := B.fields.conjO (X.piT u)
      pins := hpins
      tie := htie
      val := ?val
      fin := fun i hi => (hK i hi).1
      ord := fun i hi β => ((hK i hi).2.2.2 β).2
      base := ?base
      joint0 := GlobalTheory.hServTwoSidesJoint0 hT ex.cmp g C full hherm hforms u
      e0 := I.eCls0 l u a
      jointCmpEmbeddingY := Equiv.refl _
      e0Tw := ?e0Tw
      lev0 := ?lev0
      ch0 := hCh0
      y0 := ?y0
      fr0 := ?fr0
      rat := fun j hj => GlobalTheory.T.trueColumnTupleKernels_rational I hI hP l Z l0 ex.tw hJets hex u a j hj
      kin := GlobalTheory.T.kernelCoefficientField_le_coefficientField I hI hP l Z L hT Gi Gl K Y cX ex t hSK
      chiD := hchiD }⟩
  case val =>
    intro i hi
    rw [hex]
    exact GlobalTheory.Mem.Col2.TC.val_tied I hI hP l Z u a i hi _ (Ch i hi) (chOf i hi) (Kc i hi) (eY i hi)
      (hK i hi).2.2.1.readsK (hK i hi).2.1
  case base =>
    intro i hi β
    obtain ⟨k, hR, _⟩ := (hK i hi).2.2.1
    rw [GlobalTheory.T.trueColumn_orthonormalCoords_eq_given I hI hP l Z L hT Gi Gl K Y cX ex t u a _ Ch chOf eY Kc full.1.base.dt A hSK (fun i hi => (hK i hi).2.1) hpins i hi]
    exact GlobalTheory.T.companionLattice_trueColumn_baseLattice_eq_standard I hI hP l Z u i hi _ (fun x => hR.lb β x)
  case e0Tw =>
    intro φ c y
    change φ ((I.eCls0 l u a).symm (I.eCls0 l u a c)) y = φ c y
    exact congrFun (congrArg φ ((I.eCls0 l u a).symm_apply_apply c)) y
  case lev0 =>
    rw [hf]
    exact hlev0
  case y0 =>
    rw [hf]
    intro c
    obtain ⟨κ, h1, h2, h3⟩ := hy0 c
    refine ⟨κ, h1, h2, fun v hv => h3 v fun hvQ => ?_⟩
    obtain ⟨q, hq, hqv⟩ := GlobalTheory.T.placeUnderTwistPrime_over_tupleRamifiedPrime I hI hP l Z L hT Gi Gl K Y cX ex t hSK a v ((hQ v).1 hvQ)
    exact hv q hq hqv
  case fr0 =>
    rw [hf]
    intro y
    apply Subtype.ext
    exact ((hK 0 (Nat.zero_le _)).2.1 y).trans ((hSC u).eY 0 (Nat.zero_le _) (Or.inl rfl) y).symm
