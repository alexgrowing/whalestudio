import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupPropertyClosedMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselAdaptedTranslateLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateSymmetricUnipotentPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceReductionsConjOfNestedFrameStabilisersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionIffPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MemMatch

variable {D : D7}

theorem st_of_kset (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0))
    (κ : GA D (D.sp.Y 0)) (hκ : (iotaX X h κ).2 ∈ X.B.I.Kset) : Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ I.Kset → Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
    intro I hI hx
    subst hI
    have hL : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 :=
      Formalism.L2.SG.InstExistsPf.Lv_eq_map D
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx' := (GlobalTheory.FlagBasis.kset_iff (Formalism.L2.SG.InstExistsPf.instOf D) (β := β) (hL ▸ hβ) _).1 hx
    rw [e2]
    exact hx'
  exact key X.B.I h hκ

theorem exists_generic (Pg : Finset (Pl D.host.E)) : ∃ ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi Pg ψ := by
  have h : ∀ PP : Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    haveI : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun e => hψ (by rw [e]; rfl)⟩
  choose ψ hψ using h
  exact ⟨ψ, fun PP _ => hψ PP⟩

theorem isIdentityOffFreePositions_rightBlock_iff {K : Type} [CommRing K] {r n : ℕ} (ρ k : ℕ) (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) K) :
    GlobalTheory.SymRes.IsPat ρ k (upperLeftBlock hr g) ↔ GlobalTheory.SymRes.IsPat ρ k g := by
  obtain rfl : r = n := le_antisymm hr hn
  rw [GlobalTheory.SeeConjRead.restrictedBlock_self_apply]

theorem reductionBlock_injective_of_eq {K : Type} [CommRing K] {r n : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g g' : GL (Fin n) K)
    (h : upperLeftBlock hr g = upperLeftBlock hr g') : g = g' := by
  obtain rfl : r = n := le_antisymm hr hn
  rwa [GlobalTheory.SeeConjRead.restrictedBlock_self_apply, GlobalTheory.SeeConjRead.restrictedBlock_self_apply] at h

theorem conj_mem_GfC (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (s k : GA D (D.sp.Y 0)) (hk : k ∈ GfC (D.sp.Y 0)) : s * k * s⁻¹ ∈ GfC (D.sp.Y 0) := by
  rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h] at hk ⊢
  rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, hk, mul_one, Prod.fst_inv, mul_inv_cancel]

theorem exists_read (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (Pg : Finset (Pl D.host.E)) (hTP : IsTypePlaces Pg) (hsp : ∃ e, IsIdemSum e Pg)
    (hid : ∀ PP : Pg, ∃ e, Formalism.L2.NTheta.IsIdemAt (D := D) e PP.1)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (Λ) (N : ℕ) (hβ : Lev.IsBaseFrame (D.sp.Y 0) β Λ N) (s : GA D (D.sp.Y 0))
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset)) :
    ∃ m : ∀ PP : Pg, GL (Fin (D.sp.Y 0).rank) (kP PP.1), ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St β →
      ((iotaX X h (s * k * s⁻¹)).2 ∈ X.K2 ↔ ∀ PP : Pg, m PP * redFn β PP.1 (finE (D.sp.Y 0) k) * (m PP)⁻¹ ∈
        unipSym (kP PP.1) (D.sp.Y 0).rank D.R.rS D.R.k) := by
  obtain ⟨ψ0, hψ⟩ := exists_generic Pg
  obtain ⟨β₀, hβ₀, hK⟩ := GlobalTheory.SeeConjRead.read_fin X h Pg hTP (GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces Pg hTP hsp) ψ0 hψ
  have hfe : ∀ k : GA D (D.sp.Y 0), finE (D.sp.Y 0) (s * k * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k * (finE (D.sp.Y 0) s)⁻¹ := fun k => by rw [map_mul, map_mul, map_inv]
  obtain ⟨β₂, rfl⟩ : ∃ β₂, β₀ = finE (D.sp.Y 0) s * β₂ := ⟨(finE (D.sp.Y 0) s)⁻¹ * β₀, by group⟩
  have h12 : ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St β → finE (D.sp.Y 0) k ∈ St β₂ := by
    intro k hk hS
    have h1 := ((hSt (s * k * s⁻¹)).1 ⟨conj_mem_GfC X h s k hk, by
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff]; exact hS⟩).2
    have h2 := st_of_kset X h _ hβ₀ _ h1
    rwa [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at h2
  have hm := fun PP : Pg => (hid PP).elim fun e he => GlobalTheory.T.splitPlaceReductions_conj_of_nestedFrameStabilisers D (D.sp.Y 0) β β₂ Λ N hβ e PP.1 he h12
  choose m hm using hm
  refine ⟨m, fun k hk hS => ?_⟩
  rw [(hK _).1, hfe, GlobalTheory.FrameConj.conj_mem_St_iff]
  simp only [GlobalTheory.FrameConj.redFn_conj]
  refine ⟨fun hh PP => ?_, fun hh => ⟨h12 k hk hS, fun PP hPP => ?_⟩⟩
  · rw [← hm PP _ hS (h12 k hk hS)]; exact hh.2 PP.1 PP.2
  · rw [hm ⟨PP, hPP⟩ _ hS (h12 k hk hS)]; exact hh ⟨PP, hPP⟩

theorem conj_mem_K_two (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)
    (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1)
    (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hE : GlobalTheory.Core.Mi.IdE S.X) (hB : d.Base)
    (hTP : IsTypePlaces d.c.Pg) (hPG : GlobalTheory.LocMod.PinGBy G cG) (hLev : LevX (F₀ u) d h0)
    (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)) (hBl : B.lev = d.B 0 D.R.rS h0) (hAd : B.Adapted (S.tr u).wt)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = d.t 0)
    (hs : s = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * d.bot.β)) ↔
      ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset))
    (hone : ∀ k ∈ levS (D.sp.Y 0) d.bot.β d.bot.L, (∀ PP ∈ d.c.Pg, redFn d.bot.β PP (finE (D.sp.Y 0) k) = 1) →
      (iotaX S.X S.inst (s * k * s⁻¹)).2 ∈ S.X.K2) :
    ∀ k ∈ levS (D.sp.Y 0) d.bot.β d.bot.L, (iotaX S.X S.inst (s * k * s⁻¹)).2 ∈ S.X.K2 := by
  have hemb : ∀ b, embA B.d B.o b = (embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b : GA D (d.st 0).V) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (d.st 0).V) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (d.bes 0 D.R.rS h0).d : Subgroup (GA D (d.st 0).V)) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  refine GlobalTheory.T.level_group_property_closed_mul D u d τ G cG h0 hB hTP hPG
    (fun k : GA D (D.sp.Y 0) => (iotaX S.X S.inst (s * k * s⁻¹)).2 ∈ S.X.K2) ?_ ?_ ?_ hone
  · intro (k : GA D (D.sp.Y 0)) _ (k' : GA D (D.sp.Y 0)) _ q q'
    show (iotaX S.X S.inst (s * (k * k') * s⁻¹)).2 ∈ S.X.K2
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    rw [e, map_mul, Prod.snd_mul]
    exact S.Y.hK.2.1 _ q _ q'
  · intro PP (n : GA D (D.sp.Y 0)) q hn _ _ hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
      rw [hs]; group
    have hk' : t⁻¹ * n * t ∈ levS (D.sp.Y 0) d.bot.β d.bot.L := by rw [ht]; exact hk
    have hKs := ((hSt (s * (t⁻¹ * n * t) * s⁻¹)).1 ⟨conj_mem_GfC S.X S.inst s _ hk'.1, by
      rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.conj_mem_St_iff]; exact parLev_St hk'.2.1⟩).2
    have hN := ((B.tieN _).1 (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn')).2
    have goal : (iotaX S.X S.inst (s * (t⁻¹ * n * t) * s⁻¹)).2 ∈ S.X.K2 := by
      rw [e] at hKs ⊢
      generalize embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹ = n' at hN hKs ⊢
      rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply] at hKs ⊢
      generalize iotaX S.X S.inst n' = y at hN hKs ⊢
      change (S.X.xu u)⁻¹ * y.2 * S.X.xu u ∈ _ at hKs ⊢
      refine Formalism.L2.SG.Pf.unipotent_conj_mem_level hN ?_
      have := Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (S.X.xu_K u) hKs)
        (Formalism.L2.SG.Pf.unitaryCongruence.K_inv _ (S.X.xu_K u))
      rwa [show S.X.xu u * ((S.X.xu u)⁻¹ * y.2 * S.X.xu u) * (S.X.xu u)⁻¹ = y.2 by group] at this
    subst ht
    exact goal
  · intro b hb hk
    have h1 := (GlobalTheory.T.bessel_adapted_translate_level D u F₀ S d h0 hE hB hLev B hBl hAd a₀ hH0 b hb).1.1 hk
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    rw [← e, hemb b] at h1
    subst ht
    exact h1.2

theorem mem_K_two_iff (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)
    (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1)
    (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hE : GlobalTheory.Core.Mi.IdE S.X) (hB : d.Base)
    (hTP : IsTypePlaces d.c.Pg) (hPG : GlobalTheory.LocMod.PinGBy G cG) (hLev : LevX (F₀ u) d h0)
    (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)) (hBl : B.lev = d.B 0 D.R.rS h0) (hAd : B.Adapted (S.tr u).wt)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = d.t 0)
    (hs : s = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * d.bot.β)) ↔
      ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset))
    (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ GfC (D.sp.Y 0)) (hκS : finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * d.bot.β)) :
    (iotaX S.X S.inst κ).2 ∈ S.X.K2 ↔ rTup (finE (D.sp.Y 0) s * d.bot.β) d.bot.L (finE (D.sp.Y 0) κ) ∈ d.bot.L.P.H := by
  have hm0 : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨hr, ξ, hL⟩ := (hB.st 0 hm0).lev
  obtain ⟨N, hN, -⟩ := (hB.st 0 hm0).base
  have hrk : (D.sp.Y 0).rank = D.R.rankY 0 := (hB.st 0 hm0).rank
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by rw [hrk]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hr' : D.R.r ≤ (D.sp.Y 0).rank := hr
  have hLb : d.bot.L = (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B) := hL
  have hlift : Lev.LiftsExist (D.sp.Y 0) d.bot.β d.bot.L := GlobalTheory.ChainOnto.FlagAct.liftsExist_stage hB.com (hB.st 0 hm0)
  obtain ⟨m, hm⟩ := exists_read S.X S.inst d.c.Pg hTP hB.com.split (fun PP => ⟨_, (G PP).idem⟩) d.bot.β d.bot.Λ N hN s hSt
  have hin := conj_mem_K_two u F₀ S d τ G cG h0 hE hB hTP hPG hLev B hBl hAd a₀ hH0 a hac t s ht hs hSt (fun k hk h1 =>
    (hm k hk.1 (parLev_St hk.2.1)).2 fun PP => by rw [h1 PP.1 PP.2, mul_one, mul_inv_cancel]; exact one_mem _)
  have hpat : ∀ g : ∀ PP : d.c.Pg, GL (Fin D.R.r) (kP PP.1), g ∈ d.c.P.H ↔ ∀ PP, GlobalTheory.SymRes.IsPat D.R.rS D.R.k (g PP) :=
    fun g => (hPG.grp g).trans (forall_congr' fun PP => GlobalTheory.T.exists_reduction_iff_pattern D u d τ PP.1 (G PP) (g PP))
  rw [hLb] at hlift hin ⊢
  have hlev : ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St d.bot.β →
      (fun PP : d.c.Pg => upperLeftBlock hr' (redFn d.bot.β PP.1 (finE (D.sp.Y 0) k))) ∈ d.c.P.H →
      k ∈ levS (D.sp.Y 0) d.bot.β (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B) := by
    intro k hk hS hP
    refine ⟨hk, ?_⟩
    show finE (D.sp.Y 0) k ∈ lev _ _ _ _
    rw [mem_lev, mem_parLev]
    exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hS, fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _,
      fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, hP⟩
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  have hk₀ : k₀ ∈ GfC (D.sp.Y 0) := by
    have := conj_mem_GfC S.X S.inst s⁻¹ _ hκ
    rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
  have hfe : finE (D.sp.Y 0) (s * k₀ * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k₀ * (finE (D.sp.Y 0) s)⁻¹ := by rw [map_mul, map_mul, map_inv]
  rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS
  rw [hfe, GlobalTheory.FrameConj.rTup_conj]
  refine ⟨fun hK => ?_, fun hP => hin k₀ (hlev k₀ hk₀ hκS hP)⟩
  refine (hpat _).2 fun PP => (isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 ?_
  haveI : Finite (kP PP.1) := Ideal.finiteQuotientOfFreeOfNeBot PP.1.asIdeal PP.1.ne_bot
  have hrr : (D.sp.Y 0).rank = D.R.k + (2 * D.R.rS + 1) := by
    have := le_antisymm hn hr'
    unfold Ranks.r at this
    omega
  refine GlobalTheory.T.conjugate_symmetric_unipotent_pattern (kP PP.1) _ D.R.rS D.R.k hrr (m PP) (fun g hg => ?_) _ ((hm k₀ hk₀ hκS).1 hK PP)
  let g0 : ∀ Q : d.c.Pg, GL (Fin D.R.r) (kP Q.1) := Function.update (fun _ => 1) PP (upperLeftBlock hr' g)
  have hg0 : g0 ∈ d.c.P.H := (hpat _).2 fun Q => by
    by_cases hQ : Q = PP
    · subst hQ
      simp only [g0, Function.update_self]
      exact (isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 hg
    · simp only [g0, Function.update_of_ne hQ]
      exact GlobalTheory.SymRes.isPat_one _ _
  obtain ⟨k, hk, hkp, hkr⟩ := hlift g0
  have hkr' : (fun PP : d.c.Pg => upperLeftBlock hr' (redFn d.bot.β PP.1 (finE (D.sp.Y 0) k))) = g0 := hkr
  have h1 := (hm k hk (parLev_St hkp)).1 (hin k (hlev k hk (parLev_St hkp) (hkr' ▸ hg0))) PP
  have h2 : redFn d.bot.β PP.1 (finE (D.sp.Y 0) k) = g :=
    reductionBlock_injective_of_eq hr' hn _ _ ((congrFun hkr' PP).trans (Function.update_self _ _ _))
  rwa [h2] at h1

theorem mem_K_two_iff_reduction_tuple : ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.Core.Mi.IdE S.X → d.Base → IsTypePlaces d.c.Pg → GlobalTheory.FinPl.PinOff o → GlobalTheory.LocMod.PinGBy G o.cG → (∀ v : GlobalTheory.FinPl.Pl D, o.atT v ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) → (∀ v : GlobalTheory.FinPl.Pl D, ¬ o.atT v → GlobalTheory.FinPl.latV (D.sp.X 0) (d.x 0).L (· = v) = GlobalTheory.FinPl.latV (D.sp.X 0) ((F₀ u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) (· = v)) → LevX (F₀ u) d h0 → ∀ (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)), B.lev = d.B 0 D.R.rS h0 → B.Adapted (S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β)) ↔ ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset)) → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) → ((iotaX S.X S.inst κ).2 ∈ S.X.K2 ↔ Formalism.L2.DIV.rTup (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) d.bot.L (finE (D.sp.Y 0) κ) ∈ d.bot.L.P.H) := by
  intro D u F₀ S d k _ _ _ _ ι o G h0 hE hB hTP _ hPG _ _ hLev B hBl hAd a₀ hH0 a _ hac hSt κ hκ hκS
  exact mem_K_two_iff u F₀ S d o.τ G o.cG h0 hE hB hTP hPG hLev B hBl hAd a₀ hH0 a hac _ _ rfl rfl hSt κ hκ hκS

end GlobalTheory.MemMatch

end
