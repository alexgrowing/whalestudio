import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupPropertyClosedMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroElementReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSupportSplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselAdaptedTranslateLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffTypePinnedLocalGroupsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChrMatch

variable {D : D7}

theorem suppAt_conj (e : AE D) (V : HSp D) (a n : GA D V) (hn : Formalism.L2.Theta.SuppAt e V n) :
    Formalism.L2.Theta.SuppAt e V (a * n * a⁻¹) := by
  have h1 : Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 =
      Formalism.L2.Theta.mt V a * (Formalism.L2.Theta.mt V n - 1) * Formalism.L2.Theta.mt V a⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have h2 : (e + cA D e) • (Formalism.L2.Theta.mt V n - 1) = Formalism.L2.Theta.mt V n - 1 := by
    ext i j; exact hn i j
  intro i j
  have h3 : (e + cA D e) • (Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1) = Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 := by
    rw [h1, ← Matrix.smul_mul, ← Matrix.mul_smul, h2]
  exact congrFun (congrFun h3 i) j

theorem levChi_mul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ levS V β L) (hk' : k' ∈ levS V β L) : levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have := (levChar D.sp.cm V.gram β L).map_mul ⟨finE V k, hk.2⟩ ⟨finE V k', hk'.2⟩
  unfold levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg Units.val this

theorem levChi_of_red_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (hs : L.s = 0)
    (hQ : L.Q = ∅) {k : GA D V} (hk : ∀ PP ∈ L.Pg, redFn β PP (finE V k) = 1) : levChi V β L k = 1 := by
  have h1 : rTup β L (finE V k) = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1
    rw [hk PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, hs, hQ]
  simp

theorem rowChi_conj_of_mem (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)
    (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1)
    (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hE : GlobalTheory.Core.Mi.IdE S.X) (hB : d.Base)
    (hTP : IsTypePlaces d.c.Pg) (hPG : GlobalTheory.LocMod.PinGBy G cG) (hLev : LevX (F₀ u) d h0)
    (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)) (hBl : B.lev = d.B 0 D.R.rS h0) (hAd : B.Adapted (S.tr u).wt)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = d.t 0)
    (hs : s = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * d.bot.β)) ↔
      ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset))
    (hmem : ∀ k ∈ levS (D.sp.Y 0) d.bot.β d.bot.L, s * k * s⁻¹ ∈ rowJ S.X S.inst) :
    ∀ k ∈ levS (D.sp.Y 0) d.bot.β d.bot.L, rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hemb : ∀ b, embA B.d B.o b = (embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b : GA D (d.st 0).V) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (d.st 0).V) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (d.bes 0 D.R.rS h0).d : Subgroup (GA D (d.st 0).V)) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  have hps : psiBes d.c.ψ B.d 1 (vecB B.o B.ζ) =
      (psiBes d.c.ψ (d.bes 0 D.R.rS h0).d 1 (vecB (d.bes 0 D.R.rS h0).o (d.bes 0 D.R.rS h0).ζ) : GA D (d.st 0).V → ℂ) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => psiBes d.c.ψ L.d 1 (vecB L.o L.ζ)) hBl)
  refine GlobalTheory.T.level_group_property_closed_mul D u d τ G cG h0 hB hTP hPG
    (fun k : GA D (D.sp.Y 0) => rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k) ?_ ?_ ?_ ?_
  · intro (k : GA D (D.sp.Y 0)) hk (k' : GA D (D.sp.Y 0)) hk' q q'
    show rowChi S.X S.inst (s * (k * k') * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L (k * k')
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    have q₁ : rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k := q
    have q₂ : rowChi S.X S.inst (s * k' * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k' := q'
    rw [levChi_mul (D.sp.Y 0) d.bot.β d.bot.L hk hk', ← q₁, ← q₂, e, rowChi, rowChi, rowChi, map_mul, Prod.snd_mul,
      S.Y.hK.2.2.2.1 _ (hmem k hk).2 _ (hmem k' hk').2, star_mul']
  · intro PP (n : GA D (D.sp.Y 0)) q hn hq hl hk
    have h2 := GlobalTheory.T.level_zero_element_reduction D u d τ G cG h0 hB hTP hPG PP n q hq hl hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
      rw [hs]; group
    have hj := hmem (t⁻¹ * n * t) (by rw [ht]; exact hk)
    rw [e] at hj
    have h1 := GlobalTheory.T.flag_support_split_places D S.X S.inst u d.c.ψ _ B hE PP.1 (G PP).q.e (G PP).q.split (G PP).idem (hTP.1 PP.1 PP.2) _
      (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn') (suppAt_conj _ _ _ _ hl.1) hj
    subst ht
    show rowChi S.X S.inst (s * ((show GA D (D.sp.Y 0) from d.t 0)⁻¹ * n * (show GA D (D.sp.Y 0) from d.t 0)) * s⁻¹) = _
    refine (congrArg _ e).trans (h1.trans (Eq.trans ?_ h2.symm))
    rw [GlobalTheory.CharLaws.psiBes_conj]
    exact congrFun hps n
  · intro b hb hk
    have h1 := (GlobalTheory.T.bessel_adapted_translate_level D u F₀ S d h0 hE hB hLev B hBl hAd a₀ hH0 b hb).2 hk
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    rw [hemb b] at e
    subst ht
    exact (congrArg _ e).trans h1
  · intro (k : GA D (D.sp.Y 0)) hk hr1
    obtain ⟨hr, ξ, hL⟩ := (hB.st 0 hm).lev
    have hLb : d.bot.L = (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B) := hL
    show rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k
    rw [GlobalTheory.T.row_level_reduction_criterion D S.X S.inst hE d.c.Pg hTP hB.com.split _ hSt _ (hmem k hk) (fun PP hPP => by
      rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.redFn_conj]; exact hr1 PP hPP), hLb]
    exact (levChi_of_red_one _ _ _ rfl rfl hr1).symm

theorem star_character_square_eq : ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.Core.Mi.IdE S.X → d.Base → IsTypePlaces d.c.Pg → GlobalTheory.FinPl.PinOff o → GlobalTheory.LocMod.PinGBy G o.cG → (∀ z, z ∈ (d.x 0).L ↔ z ∈ (F₀ u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) → LevX (F₀ u) d h0 → ∀ (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)), B.lev = d.B 0 D.R.rS h0 → B.Adapted (S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β)) ↔ ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset)) → ∀ (hr : D.R.r ≤ (D.sp.Y 0).rank) (κ : GA D (D.sp.Y 0)), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) → (iotaX S.X S.inst κ).2 ∈ S.X.K2 → ∀ hP : (fun PP : d.c.Pg => upperLeftBlock hr (redFn (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) PP.1 (finE (D.sp.Y 0) κ))) ∈ d.c.P.H, star (S.X.chi2 (iotaX S.X S.inst κ).2) = ((d.c.P.chi ⟨_, hP⟩ : ℂˣ) : ℂ) := by
  intro D u F₀ S d k _ _ _ _ ι o G h0 hE hB hTP hPO hPG hLat hLev B hBl hAd a₀ hH0 a ha hac hSt hr κ hκ hκS _ hP
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨hr', ξ, hL⟩ := (hB.st 0 hm).lev
  have hrk : (D.sp.Y 0).rank = D.R.rankY 0 := (hB.st 0 hm).rank
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by rw [hrk]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hM := GlobalTheory.T.off_type_pinned_local_groups D u F₀ S d k ι o G h0 hE hB hTP hPO hPG hLat hLev B hBl hAd a₀ hH0 a ha hac hSt hr
  have hLb : d.bot.L = (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B) := hL
  have key := rowChi_conj_of_mem u F₀ S d o.τ G o.cG h0 hE hB hTP hPG hLev B hBl hAd a₀ hH0 a hac _ _ rfl rfl hSt
  generalize ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0) = s at *
  have hfin : ∀ s k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) → s * k * s⁻¹ ∈ GfC (D.sp.Y 0) := fun s k hk => by
    rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff S.X S.inst] at hk ⊢
    rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, hk, mul_one, Prod.fst_inv, mul_inv_cancel]
  have hfe : ∀ k : GA D (D.sp.Y 0), finE (D.sp.Y 0) (s * k * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k * (finE (D.sp.Y 0) s)⁻¹ := fun k => by rw [map_mul, map_mul, map_inv]
  rw [hLb] at key
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  have hP' : (fun PP : d.c.Pg => upperLeftBlock hr (redFn d.bot.β PP.1 (finE (D.sp.Y 0) k₀))) ∈ d.c.P.H := by
    simpa only [hfe, GlobalTheory.FrameConj.redFn_conj] using hP
  have hk₀ : k₀ ∈ levS (D.sp.Y 0) d.bot.β (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B) := by
    refine ⟨?_, ?_⟩
    · have := hfin s⁻¹ _ hκ
      rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
    · show finE (D.sp.Y 0) k₀ ∈ lev _ _ _ _
      rw [mem_lev, mem_parLev]
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS
      exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hκS, fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _,
        fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, hP'⟩
  have h1 := key (fun k hk => by
    obtain ⟨hf, hl⟩ := hk
    change finE (D.sp.Y 0) k ∈ lev _ _ _ _ at hl
    rw [mem_lev, mem_parLev] at hl
    have hf' := hfin s k hf
    have hs' : finE (D.sp.Y 0) (s * k * s⁻¹) ∈ St (finE (D.sp.Y 0) s * d.bot.β) := by
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff]; exact hl.1.2.1
    refine ⟨((hSt _).1 ⟨hf', hs'⟩).1, (hM _ hf' hs').2 ?_⟩
    simp only [hfe, GlobalTheory.FrameConj.redFn_conj]
    exact hl.2) k₀ hk₀
  refine h1.trans ?_
  have e0 : (⟨_, hP⟩ : d.c.P.H) = ⟨_, hP'⟩ := Subtype.ext (by simp only [hfe, GlobalTheory.FrameConj.redFn_conj])
  rw [e0]
  have hl2 : rTup d.bot.β (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B) (finE (D.sp.Y 0) k₀) ∈
      (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B).P.H := hP'
  unfold levChi levFn
  rw [extendOne_of_mem _ hl2]
  have e1 : (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B).s = 0 := rfl
  have e2 : (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B).Q = ∅ := rfl
  simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
  rfl

end GlobalTheory.ChrMatch

end
