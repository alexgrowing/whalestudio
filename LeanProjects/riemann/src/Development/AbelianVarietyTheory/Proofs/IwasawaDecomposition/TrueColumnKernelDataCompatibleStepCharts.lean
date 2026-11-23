import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumnsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullHermitianColumnsTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalFramesNearAdelicAtBadPrimesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepGroupElementOfChartLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepNearLiftsComponentMemLocalChartGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismsNearSameAdelicCongruentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismCongruentNearFrameReadingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMiddleStepLevelInverseLiftsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGroupCharacterInverseTypeAtLiftsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruentAutomorphismsLiftStepGroupElementsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesPreimageUnderLiftStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesShapeAtBadPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTopStepLevelCongruentBlockSumOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepCharacterInverseTypeAtLiftsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartReadsAtClassGLStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeFunctionalsEqMovedLevelFunctionalsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeLatticeEqCompanionOfAdelicRepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBadPrimeOverBadPlaceOfChainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeIdealTrivialAtChainBadPrimesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConstantWeilCharacterValuesIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEqStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT

section Lev
variable {B : Base} {X : PreX B.toPre} {I : TC B X} (hOk : I.Ok) (hP : TC.Pins B X) {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {i : ℕ} {hi : i ≤ B.R.m}
  {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch} {K : Charts I l Z u a i hi bad chOf} {k : Ch → GA B (B.R.N i)}
  (hR : ReadsAt I l Z K k) (c : (I.stp u a i).Cl) {fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E} (hfb : FrNear I l Z a (k (chOf c)) fb)
  (hfin : ChiFin I l Z (K (chOf c)).lev)
  {dep : SBof I a → ℕ} {Rel : SBof I a → (Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) → B.fields.K → Prop}

include hOk hP hR hfb hfin in

theorem locLe_of (hd : ∀ P, dep P ≤ (I.cst a).D P)
    (h : ∀ κ : (I.stp u a i).G c.1, Keeps I κ ((I.stp u a i).rep c) → ∀ P, ∃ g g' z, Rel P g z ∧ LiftsInv I κ P g' ∧ CongE P.1 (dep P) g g') :
    GlobalTheory.TwU.LocLe (sm I l Z) (K (chOf c)).lev fb dep Rel := by
  intro P v hv κ hκ hU
  obtain ⟨x, hx, hxκ⟩ := GlobalTheory.T.local_group_element_eq_level_component_bad_prime I hOk l Z a (B.T u) i hi bad (K (chOf c)).lev P v hv κ hκ hU
  obtain ⟨κ', hk, -, hin⟩ := GlobalTheory.T.exists_stepGroupElement_of_chartLevel I hOk hP l Z u a i hi bad Ch chOf K k hR c fb hfb hfin ⟨x, hx⟩
  obtain ⟨g, g', z, hg, hl, hc⟩ := h κ' hk P
  exact ⟨g, z, hg, hxκ fb dep g (GlobalTheory.T.rational_automorphism_congruent_near_frame_reading I hOk l Z a i fb _ dep P x g' g hl.1 (hd P) (hin P g' hl) hc)⟩

include hOk hP hR hfb hfin in

theorem chiIs_of (hd : ∀ P, 1 ≤ dep P ∧ dep P ≤ (I.cst a).D P)
    (hex : ∀ (κ : (I.stp u a i).G c.1) P, ∃ g', LiftsInv I κ P g')
    (h : ∀ (κ : (I.stp u a i).G c.1) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, Rel P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 (dep P) (g P) (g' P)) →
      (((I.stp u a i).chr c.1 κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1) :
    GlobalTheory.TwU.ChiIs (sm I l Z) (K (chOf c)).lev fb dep Rel := by
  intro κ g z hg
  obtain ⟨κ', -, hχ, hin⟩ := GlobalTheory.T.exists_stepGroupElement_of_chartLevel I hOk hP l Z u a i hi bad Ch chOf K k hR c fb hfb hfin κ
  choose g' hg' using hex κ'
  have e := h κ' g g' z fun P => ⟨(hg P).1, hg' P,
    GlobalTheory.T.rational_automorphisms_near_same_adelic_congruent I hOk l Z a i fb _ dep P κ.1 (g' P) (g P) (hg' P).1 (hd P).1 (hd P).2 (hin P _ (hg' P)) (hg P).2⟩
  rw [hχ]
  exact (map_mul B.embLL _ _).symm.trans ((congrArg B.embLL e).trans (map_one _))

include hOk hP hR hfb hfin in

theorem lev_mid (hm : i < B.R.m) (y0 : SBof I a → Sp B.fields.E (B.R.N i))
    (hy0 : i + 1 = B.R.m → ∀ P, y0 P ∈ cosetIn ((I.stp u a i).rep c) P)
    (hRel : ∀ P g z, Rel P g z ↔ MidAt I hm c.1 P g z ∧ (i + 1 = B.R.m → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g (y0 P)) (y0 P))) :
    GlobalTheory.TwU.LocLe (sm I l Z) (K (chOf c)).lev fb (I.cst a).D Rel ∧ GlobalTheory.TwU.LocGe (sm I l Z) (K (chOf c)).lev fb (I.cst a).D Rel ∧
      GlobalTheory.TwU.ChiIs (sm I l Z) (K (chOf c)).lev fb (I.cst a).D Rel := by
  refine ⟨locLe_of hOk hP hR c hfb hfin (fun _ => le_rfl) fun κ hκ P => ?_, ?_,
    chiIs_of hOk hP hR c hfb hfin (fun P => ⟨(hOk.idx_ok a).cst_ok.D_pos P, le_rfl⟩) (fun κ P => ?_) fun κ g g' z h => ?_⟩
  · obtain ⟨g, z, hg, hl⟩ := GlobalTheory.T.exists_middleStep_level_inverse_lifts I hOk u a i hm c.1 κ P
    refine ⟨g, g, z, (hRel P g z).2 ⟨hg, fun h1 => ?_⟩, hl, congE_refl _ _ _⟩
    have h2 := (GlobalTheory.T.couplingCosetInFrames_preimage_under_lift I hOk u a i c.1 κ _ P g hκ.1 hl (y0 P)).1 (by rw [hκ.2]; exact hy0 h1 P)
    exact ((((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a i _ P).2 h1).2.2 _ (hy0 h1 P)).1 _).1 h2
  · rintro P v hv κ hκ ⟨g, z, hg, hin⟩
    obtain ⟨hg1, hg2⟩ := (hRel P g z).1 hg
    obtain ⟨hint, hc⟩ := GlobalTheory.T.congruent_automorphisms_lift_step_group_elements I hOk u a i hm c.1 P g z hg1
    refine GlobalTheory.T.stepNearLifts_component_mem_localChartGroup I hOk hP l Z u a i hi bad Ch chOf K k hR c fb hfb P v hv κ hκ g hint hin fun g' hg' hgg => ?_
    obtain ⟨κ', e1, e2, e3⟩ := hc g' hg' hgg
    refine ⟨κ', ⟨e1, funext fun P' => Set.ext fun z' => ?_⟩, e2, e3⟩
    by_cases hPP : P' = P
    · subst hPP
      rw [GlobalTheory.T.couplingCosetInFrames_preimage_under_lift I hOk u a i c.1 κ' _ P' g' e1 e2 z']
      by_cases h1 : i + 1 = B.R.m
      · exact (((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a i _ P').2 h1).2.2 _ (hy0 h1 P')).2 g g' hg' hgg (hg2 h1) z'
      · rw [(GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a i _ P').1 h1]
        exact Iff.rfl
    · exact GlobalTheory.T.couplingCosetInFrames_preimage_under_lift I hOk u a i c.1 κ' _ P' 1 e1 (e3 P' hPP) z'
  · obtain ⟨g, z, -, hl⟩ := GlobalTheory.T.exists_middleStep_level_inverse_lifts I hOk u a i hm c.1 κ P
    exact ⟨g, hl⟩
  · exact GlobalTheory.T.step_group_character_inverse_type_at_lifts I hOk u a i hm c.1 κ g g' z fun P => ⟨((hRel P _ _).1 (h P).1).1, (h P).2⟩

include hOk hP hR hfb hfin in

theorem lev_top (hm : i = B.R.m) :
    GlobalTheory.TwU.LocLe (sm I l Z) (K (chOf c)).lev fb (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a)) (GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) ∧
      GlobalTheory.TwU.ChiIs (sm I l Z) (K (chOf c)).lev fb (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a)) (GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) := by
  have hd : ∀ P, 1 ≤ GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P ∧ GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P ≤ (I.cst a).D P := fun P => by
    unfold GlobalTheory.TwU.topDep
    have h1 := (hOk.idx_ok a).cst_ok.M_pos
    split_ifs with h
    · exact ⟨le_rfl, (hOk.idx_ok a).cst_ok.D_pos P⟩
    · exact ⟨by omega, (hOk.idx_ok a).depthQ P h⟩
  refine ⟨locLe_of hOk hP hR c hfb hfin (fun P => (hd P).2) fun κ _ P => GlobalTheory.T.exists_topStep_level_congruent_blockSum_one I hOk u a i hm c.1 κ P,
    chiIs_of hOk hP hR c hfb hfin hd (fun κ P => ?_) fun κ g g' z h => GlobalTheory.T.last_step_character_inverse_type_at_lifts I hOk u a i hm c.1 κ g g' z h⟩
  obtain ⟨g, g', z, -, hl, -⟩ := GlobalTheory.T.exists_topStep_level_congruent_blockSum_one I hOk u a i hm c.1 κ P
  exact ⟨g', hl⟩

end Lev

set_option maxHeartbeats 4000000 in

theorem adTie_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi (β : Ch i hi), LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf i hi c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt), I.IsTw → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → ex.errX.piT = X.piT → I.StdDt l Z dt → (∀ v ∈ bad, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v) → (∀ i hi, I.ReadsK l Z u a i hi (chOf i hi) (Kc i hi) ∧ I.IdY l Z u a i hi (eY i hi)) → (∀ i hi β, FunKilled (Kc i hi β).lev (X.piT u)) → (∀ i hi β, ∃ n : ℕ, 0 < n ∧ ∀ κ : (Kc i hi β).lev.U, (∀ v ∈ badG (I.rec7 l Z), bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (Kc i hi β).lev.chi κ ^ n = 1) → (a ≠ I.mu0 → ∀ i hi c (y : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm), Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det ((Kc i hi (chOf i hi c)).y ⟨c, rfl⟩).1 → detPt B.host I.SQ ((I.stp u a i).rep c).1.1 = dt y) → ∃ A : GlobalTheory.TwU.AdData t u a (fun i hi => ⟨B.T u, bad, eY i hi, Ch i hi, chOf i hi, fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c), Kc i hi⟩), GlobalTheory.TwU.AdPins A dt ∧ GlobalTheory.TwU.AdTie A dt (B.fields.conjO (X.piT u)) := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t u a bad Ch chOf eY Kc dt hTw hSK hRd hPin hX hDt hbad hRK hFun hFin hDet
  have hch : t.ChTie := (GlobalTheory.T.kernelChoices_standard_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t ⟨hSK.X_eq, hSK.seam, hSK.Pr, hSK.Ch, hSK.sel, hSK.S, hSK.word, hSK.tup,
    hSK.cst, hSK.idx, hSK.m2, hSK.glob, hSK.amb, hSK.δ, hSK.O⟩ hX).1
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch', sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hXf, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hSK
  dsimp only at hXf hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hXf
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  obtain ⟨r, hr, hN, hXi⟩ := hRd u a
  obtain rfl : rd u a = r := eq_of_heq hr
  have hm : B.R.m = B.R.m - 2 + 2 := hOk.hm
  choose k hk using fun i hi => (hRK i hi).1
  choose sc hsc using fun i hi => (hk i hi).onto
  choose fb hfb using fun i hi (β : Ch i hi) => GlobalTheory.T.exists_rational_frames_near_adelic_at_bad_primes I hOk l Z a (B.R.N i) (k i hi β)
  have hm1 : B.R.m - 2 + 1 ≤ B.R.m := by omega
  choose y0 hy0 using fun (β : Ch _ hm1) (P : SBof I a) => ((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep (sc _ hm1 β)) P).2 (by omega)).1
  have hkey : ∀ i hi c, (sc i hi (chOf i hi c)).1 = c.1 ∧ cosetIn ((I.stp u a i).rep (sc i hi (chOf i hi c))) = cosetIn ((I.stp u a i).rep c) :=
    fun i hi c => ((hk i hi).key _ _).1 (hsc i hi _)
  have hm3 : B.R.m - 2 + 1 + 1 = B.R.m := by omega
  have hib : ∀ i (hi : i < B.R.m) c, Idx.get c.1 hi = Idx.get (sc i hi.le (chOf i hi.le c)).1 hi := fun i hi c => by rw [(hkey i hi.le c).1]
  have hcrd := (spaces_in_coordinates I hOk hP l Z).2.2.2
  have hdt : ∀ x, dt x = FullDt.u1Dt B.host I.SQ x := fun x => by
    obtain ⟨b, hb⟩ := FullDt.exists_lift B.host x
    exact (hDt x b hb).trans (FullDt.normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ x b hb).symm
  refine ⟨{ crd := fun _ _ => 1
            iA := RingEquiv.refl _
            q := (QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E))
            pt := fun i _ c => ((I.stp u a i).rep c).1.1
            yb := fun c => ((I.stp u a _).rep c).1.2
            ib := fun i hi β => Idx.get (sc i hi.le β).1 hi
            fb := fb
            y0 := y0 }, ?_, ?_⟩
  · refine ⟨(GlobalTheory.T.base_fields_definite_laws B).1, hOk.sel_ok, ⟨hOk.g_mem, hOk.T_mem u⟩, hch, hOk.ch_tied.mu0, GlobalTheory.T.localConstantWeilCharacter_values_isIntegral I hOk hTw a, fun _ => rfl, fun _ => Iff.rfl,
      ⟨fun y => ?_, fun k z hz => ?_⟩, fun x y hxy => ?_, fun ι hι j b x hb hx => ?_, fun h => ?_,
      fun μ _ _ => ⟨tildeQ B.host I.SQ (I.xi μ), fun x => ?_, fun u => ?_⟩, fun i hi => ?_, fun i hi y τ => ?_⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (show DtQ B.host I.SQ from y)
      exact ⟨finAf B.host.F B.host.E a, mk_eq_of_snd_eq B.host I.SQ (afIso_finAf B.host.F B.host.E a)⟩
    · have hz' : (show B.host.E from z.1) * B.host.conj (k : B.host.E) = k := hz
      show (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) (ratId B.host.F B.host.E k)) : DtQ B.host I.SQ) = e1Q B.host I.SQ z
      rw [← isUnitaryPointsMap_unitaryRationalPointsFiner B.host I.SQ k z hz']
      refine mk_eq_of_snd_eq B.host I.SQ ?_
      show afIso B.host.F B.host.E ((k : B.host.E) ⊗ₜ[B.host.F] 1) = _
      rw [afIso_tmul_one]
      rfl
    · refine (hDt y (finIdele (afIso B.host.F B.host.E) x) ?_).symm
      have e : finAf B.host.F B.host.E (finIdele (afIso B.host.F B.host.E) x) = x :=
        Units.ext ((afIso B.host.F B.host.E).injective (afIso_finAf B.host.F B.host.E _))
      unfold IsDetLift
      rw [e]
      exact hxy.symm
    · show muTilQ B.host I.SQ I.C.mu0 (j.1 + 1) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
      have e : (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x) : DtQ B.host I.SQ) = QuotientGroup.mk b :=
        mk_eq_of_snd_eq B.host I.SQ ((GlobalTheory.T.finiteAdeleFieldIdentification_eq_baseChangeRingEquiv _ _ ι hι x).symm.trans hx)
      rw [e, muTilQ_succ B.host I.SQ I.C.mu0 j, tildeQ_mk B.host I.SQ (reference_characters_factor_tame I.SQ I.C j), finPartI_eq_self hb]
      rfl
    · obtain rfl : a = I.mu0 := h
      refine ⟨I.trueColumn_tuple_trivial_eq_one, ?_⟩
      show (O u I.mu0).mt = _
      rw [hO.mt u I.mu0, l.xi0, tildeQ_one]
      funext j
      split_ifs
      · exact mul_one _
      · rfl
    · have hk : KDq B.host I.SQ ≤ ((I.xi μ).1.comp (finPartI B.host.E)).ker :=
        (KDq_anti B.host (I.Q_subset_SQ μ)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).2.2 μ).1
      show tildeQ B.host I.SQ (I.xi μ) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
      rw [tildeQ_mk B.host I.SQ hk, finPartI_eq_self fun _ => rfl]
      exact Units.ext ((hOk.xi_reads μ).apply _ x rfl)
    · exact hO.mt u μ
    · rw [(hcrd i hi).1]
      simp [cT]
    · show (O u a).frm i y τ = _
      have e1 : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (1 : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) τ = 1 :=
        Matrix.map_one _ (map_zero _) (map_one _)
      refine (congrFun ((hO.frm u a i y).trans ((hRK i hi).2 y).symm) τ).trans ?_
      exact ((congrArg (· * (eY i hi y).1 τ) e1).trans (one_mul _)).symm
  · have hmov : ∀ {n : ℕ} (y : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), GlobalTheory.TwU.ratA (I.rec7 l Z).host.F 1 * y = y := fun y => by
      rw [map_one, one_mul]
    refine ⟨⟨fun i _ c => hN i c, fun c => PtAt.mem_ybSet _ hm3, fun i hi c c' x => ?_, fun c c' x => ?_, ⟨fun c => hN _ c, fun c c' x => ?_⟩,
      fun i hi c => (hPin u a i c).2 (Or.inl (by have : i ≤ B.R.m - 2 + 1 := hi; omega)), fun c' => (hPin u a _ c').trans (or_iff_right (by show ¬ B.R.m - 2 + 1 + 1 + 1 ≤ B.R.m; omega))⟩,
      fun _ _ => rfl, fun _ _ v hv => GlobalTheory.T.exists_badPrime_over_bad_place_of_chain I hOk l Z a v (hbad v hv), fun i hi c => ?_, fun i hi c P => ?_, fun i hi β P v h hv => ?_,
      fun c y hy P => ?_, fun i hi hi2 β => ?_, fun β => ?_, fun β => ?_, fun i hi c y hy => ?_, ?_⟩
    · have hi' : i < B.R.m - 2 := hi
      refine (hXi i (by omega) c c' x).trans ?_
      rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm (Idx.some_get _ (by omega)).symm]
      exact congrArg₂ (fun al be => B.embLL (XiEntry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) i al be _ _ x)) (hib i _ c) (hib (i + 1) _ c')
    · refine (hXi (B.R.m - 2) (by omega) c c' x).trans ?_
      rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm]
      exact congrArg (fun al => B.embLL (XiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (B.R.m - 2) al _ _ _ x)) (hib (B.R.m - 2) _ c)
    · refine (hXi (B.R.m - 2 + 1) (by omega) c c' x).trans ?_
      rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega : B.R.m - 2 + 1 + 1 = B.R.m), xiOver_eq_topG]
      rfl
    · exact (seamOf_lat _ _ _ _ _ _ _ _).trans ((hN i c).trans (GlobalTheory.T.representativeLattice_eq_companion_of_adelicRep I hOk hP l Z u a i hi bad _ _ _ _ (hk i hi) c))
    · have h := GlobalTheory.T.chart_reads_at_class_GL I hOk hP l Z u a i hi bad _ _ _ _ (hk i hi) c _ (hfb i hi _) P
      rw [← hmov ((Kc i hi (chOf i hi c)).y ⟨c, rfl⟩).1] at h
      exact h
    · obtain ⟨ι, hι⟩ := GlobalTheory.T.levelPrimeFunctionals_eq_moved_level_functionals I hOk hP l Z u a i hi bad _ _ _ _ (hk i hi) β (hFun i hi β) P v h hv
      refine ⟨ι, fun c hc => ?_⟩
      have h := hι c hc
      rw [← hmov ((Kc i hi (chOf i hi c)).y ⟨c, rfl⟩).1] at h
      exact h
    · have h1 := (GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep c) P).2 (show B.R.m - 2 + 1 + 1 = B.R.m by omega)
      have h2 := hy0 (chOf _ hm1 c) P
      rw [(hkey _ hm1 c).2] at h2
      exact ((h1.2.2 _ h2).1 _).1 (h1.2.1 y hy)
    · have hi2' : i ≤ B.R.m - 2 := hi2
      obtain ⟨c, rfl⟩ := (hk i hi.le).onto β
      refine lev_mid hOk hP (hk i hi.le) c (hfb i hi.le _) (hFin i hi.le _) hi (fun _ => 0) (fun h => by omega) fun P g z => ?_
      rw [and_iff_left fun h => by omega, ← (hkey i hi.le c).1]
      exact Iff.rfl
    · obtain ⟨c, rfl⟩ := (hk _ hm1).onto β
      refine lev_mid hOk hP (hk _ hm1) c (hfb _ hm1 _) (hFin _ hm1 _) (by omega) (y0 (chOf _ hm1 c)) (fun _ P => (hkey _ hm1 c).2 ▸ hy0 _ P) fun P g z => ?_
      rw [← (hkey _ hm1 c).1]
      exact and_congr Iff.rfl ⟨fun h _ => h, fun h => h (by omega)⟩
    · have hm2 : B.R.m - 2 + 1 + 1 ≤ B.R.m := by omega
      obtain ⟨c, rfl⟩ := (hk _ hm2).onto β
      exact lev_top hOk hP (hk _ hm2) c (hfb _ hm2 _) (hFin _ hm2 _) (by omega)
    · refine (hO.dt u a i c).trans ?_
      by_cases ha : a = I.mu0
      · subst ha
        exact (FullDt.detPt_of_reads I hOk u i (hk i hi) c y hy).trans (hdt y).symm
      · exact hDet ha i hi c y hy
    · have e := eq_of_heq hamb
      have h := GlobalTheory.T.periodLatticeIdeal_trivial_at_chain_bad_primes I hOk u a χ
      rw [← e] at h
      exact h

end GlobalTheory.Mem.Col2.AdT

end
