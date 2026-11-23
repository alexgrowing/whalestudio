import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RawSeriesMoveDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicLinearIndependent
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GamAtOfLawsJ
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFDOfCuspFiniteClaim
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEmbeddingIdealLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LettersEqFockVarsCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoefficientMapExtremalEqPhaseSmulLettersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelOneClassEqClassicalShortSeriesStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.SerOne

open GlobalTheory.ClassScalarValue GlobalTheory.PtId

theorem guard_of_splitOffBad {D : D7} (V : HSp D) (hg : V.gram = 1) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank)
    {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) {bad : ℕ} (h2 : 2 ∣ bad) (hM : l.M ∣ bad) {h : GA D V}
    (hs : SplitOffBad V bad h) : GlobalTheory.ClassScalarCompare.Guard H bad (Bridge.hLat V (fin V h)) := by
  obtain ⟨e, e1, e2, e3, e4⟩ := (GlobalTheory.RepsCompare.suppSplitOff_iff _ _ _).1
    (GlobalTheory.RepsCompare.suppSplitOff_of_splitOffBad _ _ _ hs)
  have hs' : GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (bad * l.M) (finHom V h).1 := by
    refine ⟨e, e1, e2, fun v hv => ⟨(e3 v hv).1, fun hm => (e3 v hv).2 ?_⟩, e4⟩
    rw [Nat.cast_mul] at hm
    refine (v.isPrime.mem_or_mem hm).elim id fun h => ?_
    obtain ⟨u, rfl⟩ := hM
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  obtain ⟨-, c1, c2, -, -, c5⟩ := GlobalTheory.SplitReps.exists_conjLat V hg hL H l bad h2 h hs'
  have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := H)
    (L := (GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h))).La) ⟨c1, c2, c5⟩
  have e2 : (GlobalTheory.ClassScalarCompare.conjLat (GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h))).La).La =
    Bridge.hLat V (fin V h) := GlobalTheory.ClassScalarCompare.conjLat_conjLat _
  rwa [e2] at g

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

set_option maxHeartbeats 800000 in

theorem lattice_scalar_value (hC : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (t : Tp) (h : GA D (Vc D i)) (e : AE D)
    (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((O.bad t : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) (hs : SuppAt e (Vc D i) h) (hy : IsDetAt e (Vc D i) h y)
    (hbad : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → ((O.bad t : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (Λ : GenLat D.host.E (Vc D i).rank) (N M : ℕ)
    (hcj : Λ = GlobalTheory.ClassScalarCompare.conjLat (Bridge.hLat (Vc D i) (fin (Vc D i) h)))
    (g : GlobalTheory.ClassScalarCompare.Guard T.Q.H (O.bad t) (Bridge.hLat (Vc D i) (fin (Vc D i) h))) (r4 : Λ.LevOK N M) :
    inC O.c' (O.epF t (Bridge.hLat (Vc D i) (fin (Vc D i) h)) * ((Λ.mIdx N D.R.r : O.c'.F))⁻¹ * (Λ.zCard N D.R.r : O.c'.F)) =
      (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ *
        (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf
          Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ) := by
  have hL := hC.lev
  have hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (hT.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀).1
  have hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := exists_ideal (Vc D i) hO.lift.std.1 hO.lift.std.2 h e P y he hs hy (O.bad t) hP _ _
    (chrEq_mul_inv (hL.mu0 i) (hL.xi (tup t)) hL.eta)
    (fun Q hQ x hx => by
      have a1 : (R.C.mu0 i).UnrAt Q := (R.C.isMu0 i).unr Q fun j hj => hQ (by
        obtain ⟨u, hu⟩ := (Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans
          ((Fin.prod_univ_two D.host.g).symm ▸ (hO.bad t).2.2.2.2)
        rw [hu, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hj)
      have a2 : (R.xiH (tup t)).UnrAt Q := by
        by_contra hn
        rcases (hL.Q_ram (tup t) Q).1 hn with a | ⟨Q', a, a'⟩
        · exact hQ (hbad Q (Or.inr a))
        · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast] at hQ
          exact hQ (hbad Q' (Or.inr a))
      rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx,
        R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])
    (fun Q hQ x => by
      rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
        (R.C.isMu0 i).triv.1, (hL.xi_triv (tup t)).1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, above_eq,
        Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul])
  rw [← hbar] at c1 c3
  generalize Bridge.hLat (Vc D i) (fin (Vc D i) h) = L at *
  obtain ⟨q, q0, q1, q2⟩ := (hO.ep t).2 L cc g.1 g.2.1 g.2.2 c1 c3
  have hB := (hO.tuple t).B cc c0 c2
  have hi := GlobalTheory.ClassScalarCompare.stdIndex_conjLat L
  rw [← hcj] at hi
  rw [← hpq, ← Nat.cast_pow] at q1
  have := value_calc (x := (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)) q0
    (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0))
    (mIdx_ne_zero Λ D.R.r (fun h0 : N = 0 => by simpa [h0] using r4.1)) q1
  rw [q2, zCard_eq _ _ _ r4.2.2, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, hB, ← c4, map_ratCast,
    map_natCast, map_natCast, ← Nat.cast_pow]
  have hi' : (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      ((L ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index := hi
  rw [← hi'] at this
  exact this

set_option maxHeartbeats 2000000 in

theorem kernel_eq_shortVal (hC : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {ka : ℂ} (hka : IoAt O (v₀ i (sg0 D A)) ka)
    {δ : ℤˣ} (hδ : ClsAt R i (iotaW T i) δ) {cst : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hcc : CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
      (R.ωP i A.μ0) (R.vacP i) cst)
    (φ : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) T.Q.l) → O.c'.F)
    (hφ : PhiIs R i (inC O.c') A.μ0 (iotaW T i) (Mfr T.Q.l • ⊤) φ) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo ((i : ℕ) + 1)) O.c') (hnab : IsNab (T.Q.Xo ((i : ℕ) + 1)) O.c' nab)
    (h : GA D (Vc D i)) (La : GenLat D.host.E (Vc D i).rank) (N : ℕ) (hsp : SplitOffBad (Vc D i) (O.bad ()) h)
    (hla : ∀ v, v ∈ La.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) (hN : La.LevOK N T.Q.l.M)
    (hg : GlobalTheory.ClassScalarCompare.Guard T.Q.H (O.bad ()) (Bridge.hLat (Vc D i) (fin (Vc D i) h)))
    (w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (hw : ∀ ρ, (w ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ)
    (xs : VsV D i O.c'.F) (g' : GA D (Wc D i)) (hx : (O.dict g').2 ∈ ((unfO O).X (O.dict g').1).dom) (t : ℂ)
    (ht : letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
      ShortValAt (T.Q.Xo ((i : ℕ) + 1)) O.c' nab (phiHat O.c' φ) La 1 N (O.io xs)
        (unC (Formalism.L2.PjFree.Unf.ofPj (unfO O)) (O.dict g').1 ⟨(O.dict g').2, hx⟩) t) :
    thetaKO (R.ωP i A.μ0) h g' (R.ptP i A.μ0 (R.ioP i (PiTensorProduct.tprod ℂ w) (O.c0' xs))) =
      cmpConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * cst (O.dict g').1 * O.mu g' *
        inC O.c' (O.epF () (Bridge.hLat (Vc D i) (fin (Vc D i) h))) * t := by
  letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
  have hs : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.Q.c O.s0 := hs ▸ T.toCore.good_σ₀
  have hmod := models_at_record_core D G Pl0 T0 A T R F κ v₀ hC hT i O.s0 hs
  obtain ⟨hemb, -, -, hmk⟩ := dict_cast T hT.laws _ (inR i) O.s0 hσ (Wc D i) O.hV (rank_Wc i)
  obtain ⟨hX, hon, hinv, hp, hrk, hpq, h1, hrt, -, hbas, hD, -⟩ := hmod (O.dict g').1
  have hU : IsUnf (unfO O) := GlobalTheory.OneMapAll.isUnf_unfExt O.hle (inC O.c') (fun _ => rfl) (hT.laws.unf _ (inR i) O.s0 hσ)
  obtain ⟨hx', g, Dc, γ, mk, v, ϑ, κ', B, hat, hsd, hm, hBm, hma, hϑ, hv, hκ, hrd⟩ :=
    exists_point (unfO O) hσ hU h1 hT.laws.pins.2.1.2 R.θ (Vc D i) (Wc D i) (rank_Wc i) O.dict (iotaW T i)
      (T.x₀ ((i : ℕ) + 1) O.s0)
      (fun Wt k => hmk R.θ hC.models.inf (fun k => (hmod k).1) h1 ⟨Wt.g, Wt.e, Wt.F, Wt.ik, Wt.φ, Wt.isom, Wt.pt⟩ k)
      (wtA (κ i)) hD O.mu (R.ωP i A.μ0) (R.vacP i) cst (CcIs.unfBC _ _ _ _ O.hle _ (inC O.c') _ _ _ _ _ _ hcc) g'
  obtain ⟨hγ, hΛ, hfr⟩ := hat
  have hM : 0 < T.Q.l.M := T.Q.l.odd.pos
  obtain ⟨Y, hY⟩ := (DualMark.dual_marking _ _ _ T.Q.l _ _ _ mk _ hsd hm
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 (Vc D i).rank N hN.1.pos
  have hcj : La = GlobalTheory.ClassScalarCompare.conjLat (Bridge.hLat (Vc D i) (fin (Vc D i) h)) :=
    congrArg GenLat.mk (Submodule.ext hla)
  have hg' := GlobalTheory.ClassScalarCompare.guard_conjLat hg
  rw [← hcj] at hg'
  have hMb : T.Q.l.M ∣ O.bad () := by
    rw [level_M T.toCore hT.laws.toLawsM]
    exact (hP.bad ()).2.2.2.2
  have hTr : La.TrivAt T.Q.l.M := by
    obtain ⟨k, hk, h2⟩ := hg'.2.1
    exact ⟨k, hk.coprime_dvd_right hMb, h2⟩
  obtain ⟨-, cga, hio⟩ := hP.io
  have hH := mem_HHa_of_span _ _ _ _ _ _ (hio.2.2.1 ▸ LinearMap.mem_range_self O.io xs)
  have hgeo := GlobalTheory.Dict.shortValAt_eq_thP GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ g _ Dc.bas Dc.idx Dc.e _ _ _ B Dc.sympl hx hsd
    _ _ Dc.hr Dc.eL hrk hD.2 Dc.dir_eq nab hnab ϑ v κ' hϑ hv hκ mk hm hBm La.La
    ((GlobalTheory.Dict.GenLatCmp.genLat_vset _ _ La.La).2.1 _ N hM hg'.1 hTr hN) N hN Y hY _ _ hH _ 1 t ht
  obtain ⟨vr, hvr⟩ := exists_isVarOf (Vc D i) (Wc D i) (rank_Wc i) _ hX _ Dc.hr
  have hlt := letters_eq_fockVars_core D G Pl0 T0 A T R F κ v₀ hC hT i _ _ O hP _ g Dc vr hX hp hvr
  have hω := hC.thP.ωP i A.μ0
  have hmove : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      thetaKO (R.ωP i A.μ0) h g' f = thetaKO (R.ωP i A.μ0) h (γ * g') f := fun f hf => by
    have e1 : ((h, γ * g') : GA D (Vc D i) × GA D (Wc D i)) = (1, γ) * (h, g') := by simp
    rw [thetaKO, thetaKO, e1, map_mul]
    exact (hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ f hf)).symm
  rw [hmove _ (hC.thP.pt_theta i A.μ0 _), hka (fun ℓ => vr (Dc.eL ℓ)) hlt w hw A.μ0 xs]
  obtain ⟨hfin, e, Ps, he, hPs, hsupp⟩ := hsp
  obtain ⟨yd, hyd⟩ := exists_isDetAt he (Vc D i) h
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (inC O.c') (O.io xs))).IsHomogeneous
      (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) :=
    ((isHomogeneous_of_rowDeg _ _ _ _ hH.2.2).map _).rename_isHomogeneous
  have hQ : R.Q A.μ0 = ∅ := Finset.eq_empty_of_forall_notMem fun PP hP =>
    (hC.lev.Q_ram A.μ0 PP).2 (Or.inl hP) (by rw [hC.lev.xi_base]; exact fun _ _ => rfl)
  have hhalf : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q A.μ0 → T.Q.l.Mb ≤ PP.asIdeal ∧
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP => by
    obtain ⟨k1, -, k3⟩ := (hP.tuple ()).half
    refine ⟨?_, k3 PP hPP⟩
    rcases hPP with hPP | hPP
    · exact k1.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)
  obtain ⟨h₀, J', hR, -⟩ := (hP.tuple ()).reps
  have hcl := hδ A.μ0 T.Q.l (fun x => inC O.c' (φ x)) hφ hhalf hrt g _ _ Dc.hr Dc.bas Dc.idx _ vr hX
    Dc.sympl hon hinv (hbas _) hvr (O.bad ()) N h (γ * g') La mk e Ps yd hR.2.1 he hPs hfin hsupp hyd hla
    hTr hN hma Y (hΛ ▸ hY) v _ (hΛ ▸ hv) (hfr ▸ hrd) _ _ hhom
  have hep := lattice_scalar_value hC hT O hP () h e Ps yd he hPs hsupp hyd hR.2.1 La N _ hcj hg hN
  have hw' : hatC T.Q.l (fun x => inC O.c' (φ x)) = fun q => inC O.c' (phiHat O.c' φ q) := funext fun q =>
    (PairModel.hatC_phiHat O.c' φ q).symm
  rw [← hep, hw', hΛ, MvPolynomial.rename_rename] at hcl
  have hsm : ∀ f, thetaKO (R.ωP i A.μ0) h (γ * g') (ka • f) = ka * thetaKO (R.ωP i A.μ0) h (γ * g') f :=
    fun f => by rw [thetaKO, thetaKO, map_smul]; rfl
  rw [hsm]
  refine (congrArg (fun z => ka * z) hcl).trans ?_
  have e1 := congrArg (thP ((unfO O).X (O.dict g').1) Dc.hr Dc.bas Dc.idx (gphi ((unfO O).X (O.dict g').1) Dc.bas
    (T.Q.H.w0 : D.host.E) La.La ((unfO O).X (O.dict g').1).Λ v (fun q => inC O.c' (phiHat O.c' φ q)) Y)
    (MvPolynomial.rename Dc.eL (MvPolynomial.map (inC O.c') (O.io xs)))) hfr
  refine Eq.trans (congrArg (fun z => ka * (_ * z)) e1.symm) ?_
  refine Eq.trans ?_ (congrArg (fun z => _ * z) hgeo.symm)
  have halg : ∀ s : O.c'.F, algebraMap O.c'.F ℂ s = inC O.c' s := fun _ => rfl
  simp only [cmpConst, halg, map_mul, map_inv₀, map_natCast, map_one, inv_one, one_mul]
  have key : ∀ s c m k e a z n th : ℂ, ka * (s * (c * m * k) * (e * a * z) * n * th) =
      ka * s * c * m * e * (a * n * z * k * th) := fun s c m k e a z n th => by ring
  exact key _ _ _ _ _ _ _ _ _

end GlobalTheory.AdTh.SerOne
