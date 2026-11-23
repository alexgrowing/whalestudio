import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDefiniteFormsGivenCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseCoefficientSpacesIsometricMapsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeedAtReadingKeeping
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParabolicCharacterEqProdSuperdiagonalSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbOfRangeLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseWeightEqForcedLiftWeightStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RSideA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.RsA
open Formalism.IndefR.Mult Formalism.IndefR.Datum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def newL (L : Formalism.IndefR.Links.LevCh D T) (ΛY : type_of% L.ΛY) (ΛV : type_of% L.ΛV) (ΛW : type_of% L.ΛW) (βY : type_of% L.βY) (βW : type_of% L.βW) :
    Formalism.IndefR.Links.LevCh D T := { L with ΛY := ΛY, ΛV := ΛV, ΛW := ΛW, βY := βY, βW := βW }

def newR (R : RealDat3 D A3 Ks) (L : Formalism.IndefR.Links.LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i))
    (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : Seed.BType A3 L cX cV pl) (plI : I0 → Pl D.host.E)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT R.MX →ₗ[ℂ] ℂ) : RealDat3 D A3 Ks :=
  { toRealDat :=
    { toLevCh := L
      hv0 := R.hv0
      eG := eG
      pl := pl
      Sb := Sb
      θ := R.θ
      ψ := R.ψ
      MY := R.MY
      MX := R.MX
      MW := R.MW
      cX := cX
      cV := cV
      B := B
      prX := prX
      HX := fun _ => Seed.hZ _
      HV := fun _ _ => Seed.hZ _
      HE := Seed.hZ _
      HW := fun _ _ => Seed.hZ _
      gE := 1
      gW := fun _ _ => 1
      jX := fun _ => 0
      jV := fun _ _ => 0
      νY := fun _ _ => 0
      fdY := fun _ _ => ∅
      ν0 := 0
      fd0 := ∅
      νX := fun _ => 0
      fdX := fun _ => ∅
      νV := fun _ _ => 0
      fdV := fun _ _ => ∅
      νW := fun _ => 0
      fdW := fun _ => ∅
      ωY := fun _ _ => 1
      ωX := fun _ => 1
      ωP := fun _ _ => 1
      vac := fun _ => 0
      vacX := 0
      vacP := fun _ => 0
      vY := fun _ _ => 0
      vX := fun _ => 0
      vP := fun _ _ => 0
      ItY := fun _ => 0
      ItX := 0
      ioY := fun _ _ => 0
      ioX := fun _ => 0
      Th := fun _ => 0
      BV := fun _ _ => 0
      ioP := fun _ => 0
      thF := fun _ _ => 0
      thG := fun _ _ => 0
      nW := fun _ => 0
      FW := fun _ =>
        { WK := ⊥
          Pt := fun _ => PEmpty
          nrm := fun _ y _ => PEmpty.elim y
          nrm_nonneg := fun _ y _ => PEmpty.elim y
          nrm_zero := fun _ y => PEmpty.elim y
          nrm_add := fun _ y _ _ => PEmpty.elim y
          nrm_smul := fun _ y _ _ => PEmpty.elim y
          towKs := inferInstance
          ρ := 1
          chi := 1
          j := fun _ => 0 }
      mu := R.mu
      twPl := R.twPl
      kap := 0
      lam := fun _ _ _ _ => 0
      err0 := fun _ _ => 0 }
    plI := plI, SF := SF, lam3 := fun _ _ _ _ => 0, phs := fun _ => 1 }

theorem newR_clauses (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (ΛY : type_of% R.ΛY) (ΛV : type_of% R.ΛV) (ΛW : type_of% R.ΛW) (βY : type_of% R.βY) (βW : type_of% R.βW)
    (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i))
    (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : Seed.BType A3 (newL R.toLevCh ΛY ΛV ΛW βY βW) cX cV pl) (plI : I0 → Pl D.host.E)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT R.MX →ₗ[ℂ] ℂ)
    (hL : (newL R.toLevCh ΛY ΛV ΛW βY βW).Is A3.A.μ0) (h0 : R.toRealDat.Pre0 F.lv2) (ht : R.IsTup) (hk : Keep R.toRealDat F.lv2 cG)
    (hfr : Seed.Frm.FramesExistDiagonal D R.Pg → Seed.Frm.NormalFrameConditionsDiagonal R.Pg βY βW)
    (hcX : cX.Is) (hcV : ∀ i, (cV i).Is) (hpr : IsDualPair R.θ R.MX cX prX) (hPr : Seed.PrIso R.MX cX prX)
    (hb : Seed.BrgL A3 (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF) :
    (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF prX).toRealDat.Pre0 F.lv2 ∧
    (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF prX).IsInert ∧
    (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF prX).IsTup ∧
    (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF prX).AllPlaces ∧
    Keep (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF prX).toRealDat F.lv2 cG := by
  have hsub : R.Pg ⊆ Sb := by rw [hb.sb]; exact Finset.Subset.refl _
  refine ⟨⟨hL, hb.red_R, hb.red_L, h0.levels, h0.record, ⟨hb.tie, hsub, hb.roots, hb.pl_onto, hb.degR, hb.degL, hb.muVal,
      hb.etaVal⟩, h0.inf, h0.vpos, hcX, hcV, hpr, h0.order, h0.std⟩, ⟨hb.in_tie, hb.in_onto, hb.in_R, hb.in_L, hb.in_SF⟩,
      ⟨ht.1, ht.2, ht.3, ht.4, ht.5⟩, hb.sb, ⟨h0.std, ?_, hfr, hk.beta, hPr, hk.grp, hk.psi, hk.guard, hk.valKs, hk.frameKs, hk.levKs⟩⟩
  refine hk.grp.elim fun plg h => h.elim fun iso h => ?_
  exact GlobalTheory.SignsAtTypePrimes.signsAtG _ _ _ _ _ _ _ _ cG h0.std hk.psi ⟨plg, iso, h.1, h.2.2.1, h.2.2.2⟩

theorem vv_cast_map {K : Type} [Field K] {ι : Type} [Fintype ι] {n n' : ℕ} (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (hl : ∀ τ a, (lam τ).w a = (lam' τ).w (Fin.cast h a)) (σ : K →+* ℂ) (v : VV K lam) :
    ∃ v' : VV K lam', HEq v' v ∧ HEq (MvPolynomial.map σ v'.1) (MvPolynomial.map σ v.1) := by
  subst h
  have hlam : lam = lam' := by
    funext τ
    have h1 := hl τ
    rcases hw : lam τ with ⟨w, hw1⟩
    rcases hw' : lam' τ with ⟨w', hw1'⟩
    rw [hw, hw'] at h1
    have : w = w' := funext fun a => by simpa using h1 a
    subst this
    rfl
  subst hlam
  exact ⟨v, HEq.rfl, HEq.rfl⟩

set_option maxHeartbeats 2000000 in

theorem stage {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z' : w'.Lt} {hX' : B'.fields.Ok} {Wt' : Set B'.places.Pl}
    (hV : ∀ i, Seed.FrmC.StdLat (Vc (w'.st Z').toD7 i)) (hXl : Seed.FrmC.StdLat (w'.st Z').toD7.sp.X') (hval : ValsIn w'.I)
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd) (hK : Kept T' w' Z' hX' Wt' R cG)
    (ΛY : type_of% R.ΛY) (ΛV : type_of% R.ΛV) (ΛW : type_of% R.ΛW) (βY : type_of% R.βY) (βW : type_of% R.βW)
    (hY : ∀ j, j < (w'.st Z').toD7.R.m → IsSDFrame (Yc (w'.st Z').toD7 j) (βY j) (ΛY j) ((w'.st Z').toD7.host.g 0 * (w'.st Z').toD7.host.g 1))
    (hV' : ∀ i, IsSDFrame (Vc (w'.st Z').toD7 i) (R.βV i) (ΛV i) 1) (hW : ∀ i, IsSDFrame (Wc (w'.st Z').toD7 i) (βW i) (ΛW i) 1)
    (hfr : Seed.Frm.FramesExistDiagonal (w'.st Z').toD7 R.Pg → Seed.Frm.NormalFrameConditionsDiagonal R.Pg βY βW)
    (cV : ∀ i, CoefA (Vc (w'.st Z').toD7 i))
    (c0L : ∀ i : Fin (w'.st Z').toD7.R.m, VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[(w'.st Z').toD7.what₂.embLL] (cV i).W)
    (h1 : ∀ i, (cV i).Is) (h2 : ∀ i, Bridge.CoefMapTie (Vc (w'.st Z').toD7 i) (cV i).coef (c0L i) (rhoVr (labLL (w'.st Z').toD7) _))
    (h3 : ∀ i x y, inner ℂ (c0L i x) (c0L i y) = (w'.st Z').toD7.what₂.embLL (pairVr (labLL (w'.st Z').toD7) _
      (if (w'.st Z').toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc (w'.st Z').toD7 i).gram else (Vc (w'.st Z').toD7 i).gram) x y)) :
    ∃ (cX : _) (pl : _) (Sb : _) (Bd : _) (plI : _) (SF : _) (prX : _),
      Kept T' w' Z' hX' Wt' (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb Bd plI SF prX) cG ∧ Sb = R.Pg ∧
      ∀ (i : Fin (w'.st Z').toD7.R.m) (t : TupU w'.I (usedOf w'.I T' Wt'))
        (ok : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel t.1 ((i : ℕ) + 1)).Ok)
        (φ : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc (w'.st Z').toD7 i)),
        ∃ v', Bd.jL i t ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel t.1 ((i : ℕ) + 1)).res ok φ :))) h = c0L i v' ∧
          HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1)
            (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ.1 (LiftBrg.ptL (w'.st Z') w'.I (usedOf w'.I T' Wt') i t 1 1 h)).1) := by
  have hLev := hK.1
  have h4 := hLev.is
  have hL1 : LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') (newL R.toLevCh ΛY ΛV ΛW βY βW) :=
    ⟨⟨h4.mu0, h4.eta, h4.xi, h4.xi_inj, h4.xi_base, h4.xi_fin, h4.xi_triv, h4.xi_tame, h4.Pg, h4.Q_pl,
      h4.Q_off, h4.Q_de, h4.Q_ram, h4.chi, h4.xiR, hY, h4.βX, hV', hW⟩, hLev.C, hLev.xiH, hLev.Pg, hLev.Q, hLev.beta⟩
  have h0 := hK.2.2.2.2.2.1
  refine (GlobalTheory.T.exists_adelicReading_definiteForms_given_coefficients (w'.st Z') w'.px w'.I hX' (usedOf w'.I T' Wt') Xg tr (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG w'.ok hval hL1 hK.2.1
    hLev.beta.2 hLev.beta.1 hXl hV R.θ h0.inf R.MX cV c0L h1 h2 h3).elim fun cX h => h.elim fun pl h => h.elim fun Sb h =>
      h.elim fun Bd h => h.elim fun plI h => h.elim fun SF h => h.elim fun prX h => ?_
  have hc := newR_clauses R (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG ΛY ΛV ΛW βY βW cX cV pl Sb Bd plI SF prX hL1.is h0
    hK.2.2.2.2.2.2.2.1 hK.2.2.2.2.2.2.2.2.2.1 hfr h.1 h1 h.2.1 h.2.2.1 h.2.2.2.1
  refine ⟨cX, pl, Sb, Bd, plI, SF, prX, ⟨hL1, hK.2.1, hK.2.2.1, hK.2.2.2.1, hK.2.2.2.2.1, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2,
    h.2.2.2.2.1, h.2.2.2.2.2.1⟩, h.2.2.2.1.sb, fun i t ok φ g => ?_⟩
  refine (vv_cast_map (LiftBrg.rkEq (w'.st Z') i) (B'.wts.lamV ((i : ℕ) + 1))
      (fun τ => Bridge.lamLdef (D := (w'.st Z').toD7) (Vc (w'.st Z').toD7 i).rank ((i : ℕ) + 1) τ) (GlobalTheory.T.baseWeight_eq_forcedLiftWeight (w'.st Z') i) B'.embLL
      (φ.1 (LiftBrg.ptL (w'.st Z') w'.I (usedOf w'.I T' Wt') i t 1 1 g))).elim fun v' hv => ?_
  exact ⟨v', h.2.2.2.2.2.2 i t φ g v' hv.1, hv.2⟩

theorem decoOf_heq {E : Type} [Field E] [NumberField E] [StarRing E] {F : Type} [Field F] [NumberField F] [Algebra F E] {n : ℕ} [NeZero n]
    {S S' : Finset (HeightOneSpectrum (𝓞 E))} (h : S' = S) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    HEq (Formalism.L2.Col.decoOf ∅ S' x) (Formalism.L2.Col.decoOf ∅ S x) := by
  subst h
  rfl

set_option maxHeartbeats 2000000 in

theorem ptL_enl {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl) (hPre : B'.toPre = B.toPre) (hp : HEq w'.px w.px)
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    (↥(Bridge.Gf (Vc (w'.st Z').toD7 i')) = ↥(Bridge.Gf (Vc (w.st Z).toD7 i))) ∧
    ∀ (h' : Bridge.Gf (Vc (w'.st Z').toD7 i')) (h : Bridge.Gf (Vc (w.st Z).toD7 i)), HEq h' h →
      HEq (LiftBrg.ptL (w'.st Z') w'.I (usedOf w'.I T' Wt') i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) 1 1 h')
        (LiftBrg.ptL (w.st Z) w.I (usedOf w.I T Wt) i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) 1 1 h) := by
  have s1 := rowLevelPrimes_colTuples_eq_vGs w Wt
  have s2 := rowLevelPrimes_colTuples_eq_vGs w' Wt'
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  have hp' : w'.px = w.px := eq_of_heq hp
  have hv : ((baseOfColW w').primes w'.px).vGs = ((baseOfColW w).primes w.px).vGs := by
    rw [hp']
    rfl
  obtain ⟨i, hi0⟩ := i
  obtain ⟨i', hi1⟩ := i'
  dsimp only at hi
  subst hi
  refine ⟨(@rfl Type ↥(@Bridge.Gf (@ColW.st B f T w Z).toD7 (Vc (@ColW.st B f T w Z).toD7 (@Fin.mk (@ColW.st B f T w Z).toD7.R.m i hi0)))), fun h' h e => ?_⟩
  have e' : h' = (h) := eq_of_heq ((e))
  rw [e']
  have hs := s2.trans (hv.trans s1.symm)
  exact (by with_unfolding_all exact ((decoOf_heq (F := B.host.F) hs (((1 : GL (Fin (w.st Z).B.R.nV) (LiftBrg.EA (w.st Z)))⁻¹ * LiftBrg.castGL (LiftBrg.rkEq (w.st Z) ⟨i, hi0⟩).symm
    (Formalism.UG.bc (swapAE (w.st Z).toD7) (h : GL (Fin (Vc (w.st Z).toD7 ⟨i, hi0⟩).rank) _)) * 1 * 1))) :))

set_option maxHeartbeats 2000000 in

theorem frames_enl {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} (w' : ColW B' f' T')
    {Z : w.Lt} (Z' : w'.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl} (z : Dat (w.st Z) w.I hX T Wt)
    (hPre : B'.toPre = B.toPre) (hf : HEq f' f) (hp : HEq w'.px w.px) :
    ∃ (ΛY : ∀ j, Submodule (𝓞 (w'.st Z').toD7.host.E) (Fin (Yc (w'.st Z').toD7 j).rank → (w'.st Z').toD7.host.E))
      (ΛV : ∀ j, Submodule (𝓞 (w'.st Z').toD7.host.E) (Fin (Vc (w'.st Z').toD7 j).rank → (w'.st Z').toD7.host.E))
      (ΛW : ∀ j, Submodule (𝓞 (w'.st Z').toD7.host.E) (Fin (Wc (w'.st Z').toD7 j).rank → (w'.st Z').toD7.host.E))
      (βY : ∀ j, GL (Fin (Yc (w'.st Z').toD7 j).rank) (Datum.EAf (w'.st Z').toD7))
      (βW : ∀ j, GL (Fin (Wc (w'.st Z').toD7 j).rank) (Datum.EAf (w'.st Z').toD7)),
      (HEq ΛY z.R.ΛY ∧ HEq ΛV z.R.ΛV ∧ HEq ΛW z.R.ΛW ∧ HEq βY z.R.βY ∧ HEq βW z.R.βW) ∧
      (∀ j, j < (w'.st Z').toD7.R.m → IsSDFrame (Yc (w'.st Z').toD7 j) (βY j) (ΛY j) ((w'.st Z').toD7.host.g 0 * (w'.st Z').toD7.host.g 1)) ∧
      (∀ i, IsSDFrame (Vc (w'.st Z').toD7 i) 1 (ΛV i) 1) ∧ (∀ i, IsSDFrame (Wc (w'.st Z').toD7 i) (βW i) (ΛW i) 1) ∧
      (∀ Pg : Finset (Pl (w'.st Z').toD7.host.E), Pg = (B'.primes w'.px).vGs →
        (Seed.Frm.FramesExistDiagonal (w'.st Z').toD7 Pg → Seed.Frm.NormalFrameConditionsDiagonal Pg βY βW) ∧ HEq Pg z.R.Pg ∧ HEq Pg z.R.Sb ∧
        ∀ eG : Gc B' w'.px ≃* G0 Pg (w'.st Z').toD7.R.r, IsPlacewiseIdentity (w'.st Z') (px := w'.px) eG → HEq eG z.R.eG) ∧
      (∀ ψ, IsStdChar (w'.st Z').toD7 ψ (-1) → HEq ψ z.R.ψ) ∧ (∀ θ : InfFam (w'.st Z').toD7, IsInfFam θ → HEq θ z.R.θ) ∧
      ∀ βV : ∀ j, GL (Fin (Vc (w'.st Z').toD7 j).rank) (Datum.EAf (w'.st Z').toD7), (∀ j, βV j = 1) → HEq βV z.R.βV := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  have hV : ∀ i, IsSDFrame (Vc (w.st Z).toD7 i) 1 (z.R.ΛV i) 1 := fun i => by
    have := z.lev.is.βV i
    rw [z.lev.beta.1 i] at this
    exact this
  have hall : z.R.Sb = z.R.Pg := z.pins.char.allPl
  refine ⟨(z.R.ΛY), (z.R.ΛV), (z.R.ΛW), (z.R.βY), (z.R.βW),
    ⟨(HEq.refl z.R.ΛY), (HEq.refl z.R.ΛV), (HEq.refl z.R.ΛW), (HEq.refl z.R.βY),
      (HEq.refl z.R.βW)⟩, (z.lev.is.βY), (hV), (z.lev.is.βW), fun Pg hPg => ?_, fun ψ hψ => ?_,
      fun θ hθ => ?_, fun βV hβ => ?_⟩
  · have e : Pg = (z.R.Pg) := hPg.trans ((by with_unfolding_all exact (z.lev.Pg.symm :)))
    subst e
    refine ⟨by kexactB z.pins.keep.frames, (HEq.refl z.R.Pg), (by with_unfolding_all exact ((heq_of_eq hall.symm) :)), fun eG hG => ?_⟩
    exact (by with_unfolding_all exact ((heq_of_eq (isIdG_unique (w.st Z) (px := w.px) z.lev.Pg (eG := (by with_unfolding_all exact (eG :))) ((by with_unfolding_all exact (hG :))) z.idG)) :))
  · exact (by with_unfolding_all exact ((heq_of_eq (isStdChar_unique (D := (w.st Z).toD7) (ψ := (by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (hψ :))) z.pins.keep.std)) :))
  · exact (by with_unfolding_all exact ((heq_of_eq (isInfFam_unique (D := (w.st Z).toD7) (θ := (by with_unfolding_all exact (θ :))) ((by with_unfolding_all exact (hθ :))) z.pins.char.base.models.inf)) :))
  · have e : ((βV) : type_of% z.R.βV) = z.R.βV := funext fun j => Eq.trans ((hβ j)) (z.lev.beta.1 j).symm
    exact (by with_unfolding_all exact ((heq_of_eq e) :))

set_option maxHeartbeats 4000000 in

theorem reset_side : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std → (∀ i, Seed.FrmC.StdLat (Vc (w'.st Z').toD7 i)) → Seed.FrmC.StdLat (w'.st Z').toD7.sp.X' → ValsIn w'.I →
    ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R cG →
    ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R₁ cG₁ ∧ RSideA z Wt' R₁ := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp hS hV hXl hval Ks _ _ _ Xg tr R cG hK
  refine (GlobalTheory.T.enlargedBase_coefficientSpaces_isometric_maps (w' := w') (Z' := Z') (hX' := hX') (Wt' := Wt') z hE hf hp hS).elim fun cV h => h.elim fun c0L hc => ?_
  refine (frames_enl w' Z' z hE.1 hf hp).elim fun ΛY h => h.elim fun ΛV h => h.elim fun ΛW h => h.elim fun βY h => h.elim fun βW hF => ?_
  have hPg := hF.2.2.2.2.1 R.Pg hK.1.Pg
  refine (stage hV hXl hval R cG hK ΛY ΛV ΛW βY βW hF.2.1 (fun i => (hK.1.beta.1 i).symm ▸ hF.2.2.1 i) hF.2.2.2.1 hPg.1 cV c0L
    hc.2.1 hc.2.2.1 hc.2.2.2.1).elim fun cX h => h.elim fun pl h => h.elim fun Sb h =>
      h.elim fun Bd h => h.elim fun plI h => h.elim fun SF h => h.elim fun prX h => ?_
  refine ⟨newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb Bd plI SF prX, cG, h.1,
    hF.2.2.2.2.2.1 R.ψ hK.2.2.2.2.2.1.std, hF.2.2.2.2.2.2.1 R.θ hK.2.2.2.2.2.1.inf, hF.1.2.2.2.2, hF.1.2.2.2.1, hF.1.1,
    hF.2.2.2.2.2.2.2 R.βV hK.1.beta.1, hF.1.2.1, hF.1.2.2.1, hPg.2.1, hPg.2.2.2 R.eG hK.2.1, (heq_of_eq h.2.1).trans hPg.2.2.1,
    hc.1, fun i i' hi ok ok' φ φ' hφ => ?_⟩
  have hpt := ptL_enl w w' Z Z' Wt Wt' hE.1 hp i i' hi
  refine Function.hfunext hpt.1 fun g' g e => ?_
  refine (h.2.2 i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ok' φ' g').elim fun v' hv => ?_
  exact (heq_of_eq hv.1).trans (hc.2.2.2.2 i i' hi ok φ g v' (hv.2.trans (hφ _ _ (hpt.2 g' g e))))

end GlobalTheory.Mem.R3.RsA
end
