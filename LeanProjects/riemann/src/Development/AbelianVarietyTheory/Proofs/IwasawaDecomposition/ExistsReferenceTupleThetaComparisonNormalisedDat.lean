import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoeffExtRationalFormsValuesField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawOfSquaresSelfDualSplitLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeights
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldHeckeCharacterSqrtNormValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionFramedPointsIsAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSideOfModels

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RefPins

variable {D : D7}

section Cover

open GlobalTheory.Member

set_option maxHeartbeats 1000000 in

theorem exists_unf_one {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {n r : ℕ} (d : DeltaDat Xo c n) (V : HSp D) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hio : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hA : d.l₂.A = 1) (hδ : d.cδ = 1) :
    ∃ (U₂ : Unf d.Xo₂ d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r),
      IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
      ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
        (F : FamilyUnif d.Xo₂ (((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).comp
            (IntermediateField.inclusion d.c₂.le).toRingHom)
          (fun j => relab d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
        (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
        (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
        ∀ h : GA D V, rdU U₂ d.cδ (dict₂ h).1 (dict₂ h).2 = 1 := by
  have hσ : d.c₂.F.val.toRingHom = (inC c).comp (d.eF.symm : d.c₂.F →+* c.F) := RingHom.ext fun _ => rfl
  have hg₂ : GoodEmb d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) := by
    rw [← hσ]; rfl
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D H Dw d.l₂ d.Xo₂ d.c₂ _ V r hr ι hio hpos hA hg₂).2.2 x₀ hx₀
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D V d.l₂.M).1
  obtain ⟨un, dict, mu, -, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1 ⟨continuous_const, fun _ => rfl⟩
    (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, hdu, hdl⟩ := hP.dictLaws
  refine ⟨C.unf un, dict, hP.unf, hP.modelW, g, e, F, ik, φ, th, hth, ?_, fun h => ?_⟩
  · rw [← hCι, ← hCx]
    exact hdl
  · rw [hδ]
    refine (dif_pos (hdu.2.2.2.1 h)).trans ?_
    have : _root_.IsReduced (CAt ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F))) := inferInstanceAs (_root_.IsReduced ℂ)
    exact evalAt_one (S := CAt ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F))) _ _ _
      (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange _ H Dw d.l₂ d.Xo₂ d.c₂
        (CAt ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F))) _)

end Cover

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Data

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem places_ref (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP h => (hL.Q_ram A.μ0 PP).2 (Or.inl h) ?_
  rw [hL.xi_base]
  exact fun _ _ => rfl

theorem exists_BIs (hL : R.toLevCh.Is A.μ0) (hv : Formalism.L2.Host.ValLL D R.C) (i : Fin D.R.m) (M : IntermediateField ℚ ℂ)
    (hM : ∀ y, D.what₂.embLL y ∈ M) (bad : ℕ) (hg : D.host.g 0 * D.host.g 1 ∣ bad) :
    ∃ B : Ideal (𝓞 D.host.E) → M, BIs R i M.val.toRingHom A.μ0 bad B := by
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal →
      (((R.C.mu0 i * R.xiH A.μ0 * R.C.eta⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M := by
    intro v hb
    have u1 : (R.C.mu0 i).UnrAt v := (R.C.isMu0 i).unr v fun k hk => hb (by
      have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := hk
      have hd : D.host.g k ∣ bad := by
        refine dvd_trans ?_ hg
        fin_cases k
        · exact dvd_mul_right _ _
        · exact dvd_mul_left _ _
      obtain ⟨c, rfl⟩ := hd
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hk')
    obtain ⟨y1, hy1⟩ := hv.mu0 i v u1
    obtain ⟨y3, hy3⟩ := hv.eta v (R.C.isEta.unr v)
    have h2 : (R.xiH A.μ0).valTw 0 v = 1 := by
      rw [hL.xi_base]
      have e : (1 : Formalism.L2.Host.HChar D.host.E).val v = 1 := rfl
      simp [Formalism.L2.Host.HChar.valTw, e]
    rw [GlobalTheory.Mem.BVal.val_mul_sqrt, ← hy1, h2, ← hy3]
    exact mul_mem (mul_mem (hM _) (one_mem _)) (inv_mem (hM _))
  classical
  refine ⟨fun cc => if h : cc ≠ ⊥ ∧ cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ then
    ⟨_, GlobalTheory.Mem.BVal.mem_of_primes _ M _ key cc h.1 h.2⟩ else 0, fun cc h0 h1 => ?_⟩
  simp only [dif_pos (And.intro h0 h1)]
  rfl

set_option maxHeartbeats 1000000 in

theorem exists_phi_of_empty (hL : R.toLevCh.Is A.μ0) (hvP : R.thP_vP) (i : Fin D.R.m) (hV : VStd D i) (t : T0) (hQ : R.Q t = ∅)
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (hι : LatEmb (Wc D i) ι) (M : IntermediateField ℚ ℂ)
    (hP : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (J : Ideal (𝓞 D.host.E))
    (hJ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) :
    ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M,
      PhiIs R i M.val.toRingHom t ι (J • ⊤) φ := by
  obtain ⟨M₀, -, h⟩ := GlobalTheory.LevelDatum.exists_phi D G Pl0 T0 A Ks R hL hvP i hV t La ι hι
  obtain ⟨φ, e, he, hφ⟩ := h M₀ le_rfl hP J hJ
  have hm : ∀ q, ((φ q : M₀) : ℂ) ∈ M := fun q => by
    have h1 := (hφ fun b => (q b).out).2
    have h2 : (fun b => Submodule.Quotient.mk (q b).out) = q := funext fun b => Quotient.out_eq _
    rw [h2] at h1
    rw [show ((φ q : M₀) : ℂ) = _ from h1, hQ]
    refine mul_mem ?_ ?_
    · unfold Formalism.IndefR.Datum.omegaK
      split_ifs
      exacts [one_mem _, zero_mem _]
    · unfold Formalism.IndefR.Datum.omegaQ
      split_ifs
      · exact prod_mem fun PP _ => absurd PP.2 (Finset.notMem_empty _)
      · exact zero_mem _
  exact ⟨fun q => ⟨_, hm q⟩, e, he, hφ⟩

end Data

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

theorem exists_levIs (hL : R.toLevCh.Is A.μ0) (hT : LawsJ T) (hpb : T.pb = R.C.P.pb) (i : Fin D.R.m) :
    ∃ lev, LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev := by
  have hβ := hL.βW i
  have hle : ∀ PP ∈ R.Pg, T.Q.l.Mb ≤ PP.asIdeal := by
    intro PP hP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
    rw [hT.half.2]
    refine (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ k))).trans ?_
    rw [hpb, ← show PP.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact Ideal.map_comap_le
  have hlift : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
    obtain ⟨c, hc⟩ := hβ
    refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP h PP' h' => ?_) (Finset.disjoint_empty_right _)
    rcases h' with h' | h'
    · exact GlobalTheory.LevelAction.not_isConjPl T.Q.l (hle PP h) (hle PP' h')
    · exact absurd h' (Finset.notMem_empty _)
  have hM : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  choose k hk using fun g => hlift (R.eG g)
  choose f hf using fun g => GlobalTheory.LevelAction.exists_endo (iotaW T i) (GlobalTheory.LevelAction.latEmb_iotaW T hT i) hM
    (GlobalTheory.LevelAction.finCong_of_mem_St hβ (parLev_St (hk g).2.1))
  exact ⟨f, fun g => ⟨k g, hk g, fun a _ => hf g a⟩⟩

variable (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem chiVal_of_tie (hL : R.toLevCh.Is A.μ0) (t : TieIn T R κ v₀) : ChiVal R := by
  intro i PP hPP x
  have e0 : res T D.what₂.embLL = T.σ₀ := res_embLL T t.alg t.laws.pins.2.2.1
  have hσ : GoodEmb T.Q.c (res T D.what₂.embLL) := e0 ▸ T.good_σ₀
  refine GlobalTheory.ChiDetValues.res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ hPP) _
  obtain ⟨y, hy, -⟩ := (t.chiR i D.what₂.embLL hσ).2.2.2.1 x hx
  exact ⟨_, hy.symm⟩

theorem exists_coeff_rows (ha : AlgTie T) (hp : T.Q.PinField) :
    ∃ c' : Coeff T.Q.l, c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧ T.Q.c.F ≤ c'.F := by
  have hle : T.Q.c.F ≤ D.what₂.embLL.toRatAlgHom.fieldRange := fun x hx =>
    ⟨algebraMap T.Q.c.F D.what₂.LL ⟨x, hx⟩, RingHom.congr_fun (res_embLL T ha hp) ⟨x, hx⟩⟩
  exact ⟨⟨_, LinearEquiv.finiteDimensional (D.what₂.embLL.toRatAlgHom.equivFieldRange).toLinearEquiv,
    fun τ a => hle (T.Q.c.conj τ a), hle T.Q.c.zeta_mem, T.Q.c.le.trans hle⟩, rfl, hle⟩

set_option maxHeartbeats 2000000 in

theorem exists_pins_ref (hR : PreChar R) (hv : Formalism.L2.Host.ValLL D R.C) (ht : TieIn T R κ v₀) (hpb : T.pb = R.C.P.pb)
    (hG : QGuard R) (i : Fin D.R.m) (hV : VStd D i) :
    ∃ O : OMDat T.toCore R i Unit (fun _ => A.μ0), O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) := by
  have hT := ht.laws
  have hL := hR.lev
  have hQ := places_ref R hL
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := hodd.pos
  obtain ⟨c', hF, hle⟩ := exists_coeff_rows T ht.alg hT.pins.2.2.1
  have hLL : ∀ y, D.what₂.embLL y ∈ c'.F := fun y => hF.ge ⟨y, rfl⟩
  obtain ⟨d, -, hI, hl, -, -, hδ, hlv, hnab⟩ :=
    GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) c' hpos (Vc D i).rank 1 ⊤ T.Q.l
      (T.Q.Xo ((i : ℕ) + 1)) c' rfl ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _)
      (Ideal.mul_top _).symm (top_sup_eq _)
  have hA : d.l₂.A = 1 := (congrArg (·.A) hl).trans hT.pins.2.1.2
  have hσ : GoodEmb T.Q.c (sOv T.toCore c' hle) := rfl
  obtain ⟨hio', hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  obtain ⟨U₂, dict₂, hU, hmod, g, e, F, ik, φ', th, hth, hdl, hone⟩ :=
    exists_unf_one d (Wc D i) (rank_Wc i) (iotaW T i) _ hio' hpos hx₀ hA hδ
  obtain ⟨xi, hxi, -, -, hx1⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) (R.xi A.μ0) (R.xiH A.μ0) (hL.xi _) 1 one_pos
    ((pow_one _).trans hL.xi_base) (hL.xi_triv _) (hL.xi_tame _)
  have hhalf : HalfIs R A.μ0 T.Q.l.Mb d.I := by
    obtain ⟨_, _, -, h⟩ := GlobalTheory.CoverHalf.exists_half_of_laws T.toCore R hT.toLawsM hL hpb hG A.μ0
    exact ⟨h.1, fun PP hPP => absurd (hQ ▸ hPP) (Finset.notMem_empty _), h.2.2⟩
  let jL : D.what₂.LL →+* c'.F := D.what₂.embLL.codRestrict c'.F hLL
  have hjL : (inC c').comp jL = D.what₂.embLL := RingHom.ext fun _ => rfl
  obtain ⟨gramR, c0R, c0L, htie⟩ := hR.fam.tie
  obtain ⟨c0', hc0⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R.cV i).W) jL (inC c') hjL (lamV D i) (c0L i)
  have hplace : ∀ (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i A.μ0 h c0' := fun Cl _ h =>
    GlobalTheory.RationalValues.placeEx_of_type_mem R i jL (inC c') A.μ0 h c0' hR.models.jV htie hc0
      (GlobalTheory.RationalValues.type_mem R i A.μ0 _
        (fun PP hPP x => by
          obtain ⟨y, hy⟩ := chiVal_of_tie T R κ v₀ hL ht i PP hPP x
          exact ⟨jL y, hy⟩)
        fun PP hPP => absurd (hQ ▸ hPP) (Finset.notMem_empty _))
  obtain ⟨lev, hlev⟩ := exists_levIs T R hL hT hpb i
  obtain ⟨Cl, fCl, h, J', bad, Lh, gam, vol, La, Nc, hrep, hbad, hcl⟩ :=
    GlobalTheory.SplitReps.exists_repsR_repsCov R i (hL.βV i) hV c'.F (T.Q.Xo ((i : ℕ) + 1)) c' (fun _ : Unit => A.μ0) fun _ => d
  choose B hBis using fun t => exists_BIs R hL hv i c'.F hLL (bad t) (hbad t).2.2.2.2
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => GlobalTheory.LawOfSquares.law_of_squares _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  obtain ⟨io, hw, hio⟩ := GlobalTheory.CoefMapRecord.exists_io_record D T.Q hT.pins κ ht.kap i c'
  obtain ⟨φ, hφis⟩ := exists_phi_of_empty R hL hR.thP.vP i hV A.μ0 hQ (iotaW T i) (GlobalTheory.LevelAction.latEmb_iotaW T hT i) c'.F
    hhalf.2.2 (Mfr d.l₂) fun PP hPP c hc => by
    have hM : d.l₂.Mb ≤ PP.asIdeal := by
      rw [hlv.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [hhalf.1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans (hhalf.2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth' using fun t => GlobalTheory.AdelicSide.exists_thAd_of_models D G Pl0 T0 A _ R hR.models i A.μ0 _ _ c0' _ (h t) _
    (hrep t).1.2.2.1 (hrep t).1.2.2.2.2.2.1 (v₀ i (sg0 D A))
  have hact := fun c => GlobalTheory.LevelActFromLevel.actLev_of_levIs D G Pl0 T0 A T R hL hT hpb i c lev hlev
  refine ⟨{ c' := c', hle := hle, jL := jL, hV := hT.spaceW _ (inR i) _ rfl, c0' := c0', lev := lev, dδ := fun _ => d, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := io, hw := hw, φ := fun _ => φ,
            w := fun _ _ q => d.eF.symm (phiHat d.c₂ (fun x => d.eF (φ x)) q),
            U₂ := fun _ => U₂, dict₂ := fun _ => dict₂, xi := fun _ => xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i A.μ0 (h t) c0' (jVx R i A.μ0 x₀) x }, hF,
    ⟨hjL, hV, ht.hv₀ i _, ⟨gramR, c0R, c0L, htie, hc0⟩, hlev⟩,
    fun t => ⟨⟨h t, J' t, (hrep t).1, hplace _ _, hth' t, fun _ => Iff.rfl⟩, hBis t, hxi, hφis, hhalf⟩,
    ⟨hact _, hact _⟩,
    hbad, hcl, fun t => ⟨fun _ => rfl, hepF t⟩, hio, fun t k q => AlgEquiv.apply_symm_apply _ _, fun _ => ⟨hlv, hA, hnab⟩,
    ⟨1, ⟨1, one_pos, one_pow 1⟩, fun _ => ⟨hU, hmod, g, e, F, ik, φ', th, hth, hdl, fun a γ _ => ?_⟩⟩, fun _ => hmod⟩
  have h1 := hx1 (γ * a)
  rw [pow_one] at h1
  exact (hone a).trans (by rw [h1, Units.val_one, one_mul])

theorem exists_omPins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), PreChar R → Formalism.L2.Host.ValLL D R.C → TieIn T R κ v₀ → T.pb = R.C.P.pb → QGuard R → (∀ i, VStd D i) → ∃ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), ∀ i, OMPins T R κ v₀ O i := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hR hv ht hpb hG hV
  choose O hO using fun i => exists_pins_ref T R κ v₀ hR hv ht hpb hG i (hV i)
  exact ⟨O, hO⟩

end GlobalTheory.RefPins
