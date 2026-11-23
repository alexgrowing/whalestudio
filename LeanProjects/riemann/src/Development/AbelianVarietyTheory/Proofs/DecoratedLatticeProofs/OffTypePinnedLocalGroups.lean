import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrixStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NLevelHolds
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateSymmetricUnipotentPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceReductionsConjOfNestedFrameStabilisersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionIffPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionUniqueOfMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroTypeFrameLocalityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeFrameConjugationDecompositionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.MemMatch

open GlobalTheory.LocMod GlobalTheory.LocGrp in

theorem isLoc_embA {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n)
    (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) {h : GA D B.A} {g₀ : GL n k} (hh : p.IsLoc FA h g₀) :
    p.IsLoc F (embA B.d B.o h) (GlobalTheory.RootEx.embX c g₀) := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : Formalism.L2.Theta.mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ Formalism.L2.Theta.mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : Formalism.L2.Theta.mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  refine ⟨suppAt_wittLeviEmbedding B.d (suppAt_emb B.o hh.1),
    eq_embX F _ g₀ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (intertwine p eA hh) fun j => ?_⟩
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine fix_vec (map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

theorem st_of_levS {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {κ : GA D V}
    (h : κ ∈ levS V β L) : κ ∈ GfC V ∧ finE V κ ∈ St β := by
  obtain ⟨hf, hl⟩ := h
  change finE V κ ∈ lev _ _ _ _ at hl
  rw [mem_lev, mem_parLev] at hl
  exact ⟨hf, hl.1.2.1⟩

open GlobalTheory.LocMod in

theorem local_gen {D : D7} {u : D.what₂.Word} (d : GlobalTheory.SeeSaw.Dat D u)
    (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (cG) (G : ∀ PP : d.c.Pg, GAt d τ PP.1)
    (hB : d.Base) (hG : PinGBy G cG) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hr : D.R.r ≤ (d.st 0).V.rank) (PP : d.c.Pg)
    (g : GL (Fin D.R.r) (kP PP.1)) (hg : ∃ x, (G PP).Red x g) :
    ∃ n ∈ flagN (d.bes 0 D.R.rS h0).d, ∃ h ∈ GfC (D.sp.X 0), (d.t 0)⁻¹ * n * d.t 0 ∈ d.lev 0 ∧
      (d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o h * d.t 0 ∈ d.lev 0 ∧
      upperLeftBlock hr (redFn (d.st 0).β PP.1 (finE (d.st 0).V
        ((d.t 0)⁻¹ * (n * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o h) * d.t 0))) = g := by
  obtain ⟨x, hx⟩ := hg
  have hc : 0 + ((G PP).s + 1) = (G PP).s + 1 := zero_add _
  have hF := (G PP).bes 0 D.R.rS h0 _ hc
  have hρ : (G PP).S.ρ = D.R.rS := by
    have h1 := hF.1
    have h2 := (G PP).S.odd
    omega
  obtain ⟨a, b, γ, ha, hb, hab⟩ := GlobalTheory.T.type_frame_conjugation_decomposition (G PP).k (G PP).s D.R.k (G PP).S (Fin D.R.t) hc x
  rw [hρ] at ha
  obtain ⟨n, hn⟩ := Witness.exists_isLoc (ofSplit (G PP).q) ((G PP).FY 0 _ hc)
    ((GlobalTheory.StepData.typeFrame (G PP).S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 ((G PP).s + 1) hc)).conj
      (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin D.R.k ⊕ Fin ((G PP).s + 1)) (Fin D.R.t)) a.1))
  obtain ⟨h, hh⟩ := Witness.exists_isLoc (ofSplit (G PP).q) ((G PP).FX 0 (by omega)) γ
  have he := isLoc_embA (ofSplit (G PP).q) (d.B 0 D.R.rS h0) _ _ _ hF hh
  rw [← hb] at he
  have hJ : ∀ y : (G PP).S.P.J,
      (GlobalTheory.StepData.typeFrame (G PP).S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 ((G PP).s + 1) hc)).conj
        (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin D.R.k ⊕ Fin ((G PP).s + 1)) (Fin D.R.t)) y.1) ∈
        (((G PP).S.T (Fin D.R.t)).lev 0 _ hc).J := by
    intro y
    refine GlobalTheory.StepData.Level.mem_map.2 ?_
    rw [MulEquiv.symm_apply_apply]
    change (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero _ _)).symm _ ∈ (G PP).S.P.J
    rw [MulEquiv.symm_apply_apply]
    exact y.2
  have hLev := GlobalTheory.T.pinned_local_groups_have_level D u d τ cG G hB hG PP
  have l1 := hLev 0 _ hc _ _ hn (hJ a)
  have l2 := hLev 0 _ hc _ _ he (hJ b)
  have hm := GlobalTheory.LocGrp.isLoc_mul (ofSplit (G PP).q) hn he
  rw [← map_mul, ← map_mul] at hm
  have l3 := hLev 0 _ hc _ _ hm (hJ (a * b))
  refine ⟨n, GlobalTheory.LocGrp.mem_flagN_of_mem_N (ofSplit (G PP).q) (d.B 0 D.R.rS h0) _ _ _ hF n _ ha hn, h,
    GlobalTheory.WeilProduct.mem_GfC_of_suppAt (G PP).q.split hh.1, l1, l2, ?_⟩
  exact GlobalTheory.T.reduction_unique_of_maximal D u d τ PP.1 (G PP) x (a * b) g _ hx
    (GlobalTheory.T.level_zero_type_frame_locality D u d τ PP.1 (G PP) hr hc (a * b) _ hm (st_of_levS l3).2) hab

theorem eq_of_lev_eq {D : D7} {ρ : ℕ} {V A V₀ V₀' L L' : HSp D} {d : HypDec V V₀ ρ} {d' : HypDec V V₀' ρ} {o : OrthDec V₀ A L}
    {o' : OrthDec V₀' A L'} {ζ ζ' l l' c c' vA vA' vN vN'}
    (h : (⟨V, V₀, A, L, d, o, ζ, l, c, vA, vN⟩ : BesLev D ρ) = ⟨V, V₀', A, L', d', o', ζ', l', c', vA', vN'⟩) :
    flagN d = flagN d' ∧ embA d o = embA d' o' := by
  cases h
  exact ⟨rfl, rfl⟩

theorem kset_iff_st {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)} (hβ : IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0))
    (κ : GA D (D.sp.Y 0)) : (iotaX X h κ).2 ∈ X.B.I.Kset ↔ finE (D.sp.Y 0) κ ∈ St β := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ I.Kset ↔ finE (D.sp.Y 0) κ ∈ St β := by
    intro I hI
    subst hI
    have hL : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 :=
      Formalism.L2.SG.InstExistsPf.Lv_eq_map D
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx := GlobalTheory.FlagBasis.kset_iff (Formalism.L2.SG.InstExistsPf.instOf D) (β := β) (hL ▸ hβ) (Formalism.IndefR.RationalEmbedding.iota D κ).2
    generalize Lev.finE (D.sp.Y 0) κ = y at e2 ⊢
    subst e2
    exact hx
  exact key X.B.I h

theorem iotaX_conj {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (x : X.B.I.Gf)
    (y : GA D (D.sp.Y 0)) :
    (iotaX X h (((iotaX X h).symm (1, x))⁻¹ * y * (iotaX X h).symm (1, x))).2 = x⁻¹ * (iotaX X h y).2 * x := by
  rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]
  rfl

theorem flag_mem_K_two {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) {n : GA D (D.sp.Y 0)} (hn : n ∈ flagN B.d)
    (hK : (X.xu u)⁻¹ * (iotaX X h n).2 * X.xu u ∈ X.B.I.Kset) : (X.xu u)⁻¹ * (iotaX X h n).2 * X.xu u ∈ X.K2 := by
  refine MassDataMassesW.NLev.nLevel_holds X u _ ((B.tieN n).1 hn).2 ?_
  have := MassDataMassesW.NLev.Kset_mul (MassDataMassesW.NLev.Kset_mul (X.xu_K u) hK) (MassDataMassesW.NLev.Kset_inv (X.xu_K u))
  rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc, mul_inv_cancel, mul_one] at this

theorem column_mem_K_two {D : D7} {u : D.what₂.Word} {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hE : IdE S.X) (hX : LevX (F₀ u) d h0) (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0))
    (hA : B.Adapted (S.tr u).wt) {a₀ : GA D (D.sp.X 0)} (ha₀ : IsTransportAdelicCorrection (S.tr u) a₀) {h : GA D (D.sp.X 0)}
    (hf : h ∈ GfC (D.sp.X 0))
    (hl : (d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o h * d.t 0 ∈ d.lev 0) :
    (S.X.xu u)⁻¹ * (iotaX S.X S.inst (embA B.d B.o (a₀ * h * a₀⁻¹))).2 * S.X.xu u ∈ S.X.K2 := by
  let φ : GA D (D.sp.X 0) → Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := fun a =>
    ⟨GlobalTheory.AdForm.Model.finGL (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a,
      GlobalTheory.AdForm.Model.finGL_mem (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⟩
  have hmul : ∀ a b, φ (a * b) = φ a * φ b := fun a b => Subtype.ext (Units.ext (unitaryAdelicPointFiniteMatrix_base_space_mul a b))
  have e0 : φ a₀ = (S.tr u).h0 := Subtype.ext (Units.ext ha₀.2)
  have e1 : (S.tr u).h0⁻¹ * φ (a₀ * h * a₀⁻¹) * (S.tr u).h0 = φ h := by
    rw [← e0, mul_assoc, ← hmul, inv_mul_cancel_right, hmul, inv_mul_cancel_left]
  have hU := (hX h hf (φ h) rfl).1.2 hl
  have hR := GlobalTheory.T.secondModel_finitePart_frameActionMatrix D S.X S.inst u d.c.ψ B (F₀ u) (S.tr u) hE hA (a₀ * h * a₀⁻¹)
  have := ((S.lev u).2 (B.toH (a₀ * h * a₀⁻¹)).2 (φ (a₀ * h * a₀⁻¹)) hR).1.2 (by rw [e1]; exact hU)
  exact this

theorem conj_mem_iff_isPat {K : Type} [CommRing K] [Finite K] {r n ρ κ : ℕ} (hr : r ≤ n) (hn : n ≤ r) (e : r = κ + (2 * ρ + 1))
    (m : GL (Fin n) K) (h : ∀ g : GL (Fin r) K, GlobalTheory.SymRes.IsPat ρ κ g → ∃ y, upperLeftBlock hr y = g ∧ m * y * m⁻¹ ∈ unipSym K n ρ κ)
    (y : GL (Fin n) K) : m * y * m⁻¹ ∈ unipSym K n ρ κ ↔ GlobalTheory.SymRes.IsPat ρ κ (upperLeftBlock hr y) := by
  obtain rfl : r = n := le_antisymm hr hn
  have h' : ∀ g : GL (Fin r) K, GlobalTheory.SymRes.IsPat ρ κ g → m * g * m⁻¹ ∈ unipSym K r ρ κ := fun g hg => by
    obtain ⟨y, hy, hy'⟩ := h g hg
    rw [GlobalTheory.SeeConjRead.restrictedBlock_self_apply] at hy
    exact hy ▸ hy'
  rw [GlobalTheory.SeeConjRead.restrictedBlock_self_apply]
  exact ⟨GlobalTheory.T.conjugate_symmetric_unipotent_pattern K r ρ κ e m h' y, h' y⟩

theorem block_frame_conjugation_identity {G : Type} [Group G] (x e t n : G) : x⁻¹ * e * t * (t⁻¹ * n * t) * (x⁻¹ * e * t)⁻¹ = x⁻¹ * (e * n * e⁻¹) * x := by
  group

theorem conj_central_mul_cancel {G : Type} [Group G] (b a h : G) (ha : a ∈ Subgroup.center G) : b * a * h * (b * a)⁻¹ = b * h * b⁻¹ := by
  rw [mul_assoc b a, ← Subgroup.mem_center_iff.1 ha h]; group

theorem mul_aux {G : Type} [Group G] (t x y : G) : t⁻¹ * (x * y) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t) := by group

theorem conj_mul_distrib {G : Type} [Group G] (t x y : G) : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group

theorem generator_mem_K_two {D : D7} {u : D.what₂.Word} {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)
    (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (cG) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hE : IdE S.X) (hB : d.Base)
    (hG : GlobalTheory.LocMod.PinGBy G cG) (hX : LevX (F₀ u) d h0) (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0))
    (hBl : B.lev = d.B 0 D.R.rS h0) (hA : B.Adapted (S.tr u).wt) (a₀ : GA D (D.sp.X 0)) (ha₀ : IsTransportAdelicCorrection (S.tr u) a₀)
    (a : GA D (D.sp.X 0)) (haz : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t₀ : GA D (D.sp.Y 0)) (ht₀ : t₀ = d.t 0) (t : GA D (D.sp.Y 0)) (ht' : t = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t₀)
    (hmove : ∀ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β → (iotaX S.X S.inst (t * y * t⁻¹)).2 ∈ S.X.B.I.Kset)
    (hr : D.R.r ≤ (D.sp.Y 0).rank) (PP : d.c.Pg) (g : GL (Fin D.R.r) (kP PP.1)) (hg : ∃ x, (G PP).Red x g) :
    ∃ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β ∧ upperLeftBlock hr (redFn d.bot.β PP.1 (finE (D.sp.Y 0) y)) = g ∧
      (iotaX S.X S.inst (t * y * t⁻¹)).2 ∈ S.X.K2 := by
  obtain ⟨eN, eA⟩ := eq_of_lev_eq hBl
  have H : ∃ n : GA D (D.sp.Y 0), n ∈ flagN B.d ∧ ∃ h ∈ GfC (D.sp.X 0), t₀⁻¹ * n * t₀ ∈ levS (D.sp.Y 0) d.bot.β d.bot.L ∧
      t₀⁻¹ * embA B.d B.o h * t₀ ∈ levS (D.sp.Y 0) d.bot.β d.bot.L ∧
      upperLeftBlock hr (redFn d.bot.β PP.1 (finE (D.sp.Y 0) (t₀⁻¹ * (n * embA B.d B.o h) * t₀))) = g := by
    rw [eN, eA]
    subst ht₀
    exact local_gen d τ cG G hB hG h0 hr PP g hg
  obtain ⟨n, hnB, h, hh, l1, l2, hg'⟩ := H
  have k2 := column_mem_K_two S d h0 hE hX B hA ha₀ hh (by rw [eA] at l2; subst ht₀; exact l2)
  have s1 := st_of_levS l1
  have s2 := st_of_levS l2
  have c1 : t * (t₀⁻¹ * n * t₀) * t⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
      (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
    rw [ht']; exact block_frame_conjugation_identity _ _ _ _
  have c2 : t * (t₀⁻¹ * embA B.d B.o h * t₀) * t⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
      embA B.d B.o (a₀ * h * a₀⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
    rw [← conj_central_mul_cancel a₀ a h haz, map_mul (embA B.d B.o) _ (a₀ * a)⁻¹, map_mul (embA B.d B.o) (a₀ * a) h, map_inv, ht']
    exact block_frame_conjugation_identity _ _ _ _
  have k1 : (iotaX S.X S.inst (t * (t₀⁻¹ * n * t₀) * t⁻¹)).2 ∈ S.X.K2 := by
    have := hmove _ s1.1 s1.2
    rw [c1, iotaX_conj] at this ⊢
    exact flag_mem_K_two B (GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D _ _ _ B.d n hnB (B.o.emb (a₀ * a, 1))) this
  have k2' : (iotaX S.X S.inst (t * (t₀⁻¹ * embA B.d B.o h * t₀) * t⁻¹)).2 ∈ S.X.K2 := by
    rw [c2, iotaX_conj]; exact k2
  have e3 : t₀⁻¹ * (n * embA B.d B.o h) * t₀ = (t₀⁻¹ * n * t₀) * (t₀⁻¹ * embA B.d B.o h * t₀) := mul_aux _ _ _
  refine ⟨_, ?_, ?_, hg', ?_⟩
  · rw [e3]; exact mul_mem s1.1 s2.1
  · rw [e3, map_mul]; exact mul_mem s1.2 s2.2
  · rw [e3, conj_mul_distrib, map_mul]
    exact S.Y.hK.2.1 _ k1 _ k2'

theorem mem_iff {D : D7} {u : D.what₂.Word} {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)
    (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (cG) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hE : IdE S.X) (hB : d.Base) (hT : GlobalTheory.Core.Mi.IsTypePlaces d.c.Pg)
    (hG : GlobalTheory.LocMod.PinGBy G cG) (hX : LevX (F₀ u) d h0) (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0))
    (hBl : B.lev = d.B 0 D.R.rS h0) (hA : B.Adapted (S.tr u).wt) (a₀ : GA D (D.sp.X 0)) (ha₀ : IsTransportAdelicCorrection (S.tr u) a₀)
    (a : GA D (D.sp.X 0)) (haf : a ∈ GfC (D.sp.X 0)) (haz : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t : GA D (D.sp.Y 0)) (ht : t = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0))
    (hSt : ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) t * d.bot.β) →
      (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset)
    (hr : D.R.r ≤ (D.sp.Y 0).rank) (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ GfC (D.sp.Y 0))
    (hκS : finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) t * d.bot.β)) :
    (iotaX S.X S.inst κ).2 ∈ S.X.K2 ↔
      (fun PP : d.c.Pg => upperLeftBlock hr (redFn (finE (D.sp.Y 0) t * d.bot.β) PP.1 (finE (D.sp.Y 0) κ))) ∈ d.c.P.H := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hrk : (D.sp.Y 0).rank = D.R.rankY 0 := (hB.st 0 hm).rank
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by rw [hrk]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hre : D.R.r = D.R.k + (2 * D.R.rS + 1) := by unfold Ranks.r; omega
  obtain ⟨N, hN, -⟩ := (hB.st 0 hm).base
  obtain ⟨-, ψ0, hψ, -⟩ := GlobalTheory.Core.Mi.PinModel.exists_isSymLev (D := D) d.c.Pg
  obtain ⟨β₀, hβ₀, hK⟩ := GlobalTheory.SeeConjRead.read_fin S.X S.inst d.c.Pg hT (GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces _ hT hB.com.split) ψ0 hψ
  have hx : (iotaX S.X S.inst).symm (1, S.X.xu u) ∈ GfC (D.sp.Y 0) := by
    rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff S.X S.inst, ContinuousMulEquiv.apply_symm_apply]
  have htf : t ∈ GfC (D.sp.Y 0) := ht ▸
    mul_mem (mul_mem (inv_mem hx) (GlobalTheory.Core.Mi.CenAct.embA_mem_GfC B.d B.o (mul_mem ha₀.1 haf))) (hB.t 0)
  have hfin : ∀ y, finE (D.sp.Y 0) (t * y * t⁻¹) = finE (D.sp.Y 0) t * finE (D.sp.Y 0) y * (finE (D.sp.Y 0) t)⁻¹ := fun y => by
    rw [map_mul, map_mul, map_inv]
  have hmove : ∀ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β → (iotaX S.X S.inst (t * y * t⁻¹)).2 ∈ S.X.B.I.Kset :=
    fun y hy hs => hSt _ (mul_mem (mul_mem htf hy) (inv_mem htf))
      (by rw [hfin]; exact (GlobalTheory.FrameConj.conj_mem_St_iff _ _ _).2 hs)
  have hc : ∀ T β y : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), y ∈ St (T⁻¹ * β) ↔ T * y * T⁻¹ ∈ St β := fun T β y => by
    rw [← GlobalTheory.FrameConj.conj_mem_St_iff T, mul_inv_cancel_left]
  have hc' : ∀ (T β y : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (PP), redFn (T⁻¹ * β) PP y = redFn β PP (T * y * T⁻¹) :=
    fun T β y PP => by rw [← GlobalTheory.FrameConj.redFn_conj T, mul_inv_cancel_left]
  have hto : ∀ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β →
      finE (D.sp.Y 0) y ∈ St ((finE (D.sp.Y 0) t)⁻¹ * β₀) := fun y hy hs => by
    rw [hc, ← hfin]
    exact (kset_iff_st S.X S.inst hβ₀ _).1 (hmove y hy hs)
  have hloc : ∀ PP : d.c.Pg, ∀ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β →
      (redFn β₀ PP.1 (finE (D.sp.Y 0) (t * y * t⁻¹)) ∈ unipSym (kP PP.1) (D.sp.Y 0).rank D.R.rS D.R.k ↔
        ∃ x, (G PP).Red x (upperLeftBlock hr (redFn d.bot.β PP.1 (finE (D.sp.Y 0) y)))) := by
    intro PP
    haveI : Finite (kP PP.1) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    obtain ⟨m, hmm⟩ := GlobalTheory.T.splitPlaceReductions_conj_of_nestedFrameStabilisers D (D.sp.Y 0) d.bot.β ((finE (D.sp.Y 0) t)⁻¹ * β₀) _ N hN _ PP.1 (G PP).idem hto
    have hred : ∀ y ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) y ∈ St d.bot.β → redFn β₀ PP.1 (finE (D.sp.Y 0) (t * y * t⁻¹)) =
        m * redFn d.bot.β PP.1 (finE (D.sp.Y 0) y) * m⁻¹ := fun y hy hs => by
      rw [hfin, ← hc', hmm _ hs (hto y hy hs)]
    intro y hy hs
    rw [hred y hy hs, GlobalTheory.T.exists_reduction_iff_pattern D u d τ PP.1 (G PP)]
    refine conj_mem_iff_isPat hr hn hre m (fun g hg => ?_) _
    obtain ⟨w, hw, hws, hwg, hwK⟩ := generator_mem_K_two S d τ cG G h0 hE hB hG hX B hBl hA a₀ ha₀ a haz _ rfl t ht hmove hr PP g
      ((GlobalTheory.T.exists_reduction_iff_pattern D u d τ PP.1 (G PP) g).2 hg)
    refine ⟨_, hwg, ?_⟩
    rw [← hred w hw hws]
    exact ((hK _).1.1 hwK).2 PP.1 PP.2
  obtain ⟨y, rfl⟩ : ∃ y, κ = t * y * t⁻¹ := ⟨t⁻¹ * κ * t, by group⟩
  have hy : y ∈ GfC (D.sp.Y 0) := (GlobalTheory.FrameConj.conj_mem_iff _ htf y).1 hκ
  have hs : finE (D.sp.Y 0) y ∈ St d.bot.β := by
    rw [hfin] at hκS
    exact (GlobalTheory.FrameConj.conj_mem_St_iff _ _ _).1 hκS
  rw [(hK _).1, hG.grp]
  have e5 : ∀ PP, redFn (finE (D.sp.Y 0) t * d.bot.β) PP (finE (D.sp.Y 0) (t * y * t⁻¹)) =
      redFn d.bot.β PP (finE (D.sp.Y 0) y) := fun PP => by rw [hfin, GlobalTheory.FrameConj.redFn_conj]
  simp only [e5]
  exact ⟨fun h PP => (hloc PP y hy hs).1 (h.2 PP.1 PP.2), fun h => ⟨(kset_iff_st S.X S.inst hβ₀ _).1 (hmove y hy hs),
    fun PP hPP => (hloc ⟨PP, hPP⟩ y hy hs).2 (h ⟨PP, hPP⟩)⟩⟩

end GlobalTheory.Core.Mi.MemMatch

namespace GlobalTheory.Core.Mi

theorem memMatch_noLat : ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.Core.Mi.IdE S.X → d.Base → IsTypePlaces d.c.Pg → GlobalTheory.FinPl.PinOff o → GlobalTheory.LocMod.PinGBy G o.cG → LevX (F₀ u) d h0 → ∀ (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)), B.lev = d.B 0 D.R.rS h0 → B.Adapted (S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β)) ↔ ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset)) → ∀ (hr : D.R.r ≤ (D.sp.Y 0).rank) (κ : GA D (D.sp.Y 0)), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) → ((iotaX S.X S.inst κ).2 ∈ S.X.K2 ↔ (fun PP : d.c.Pg => upperLeftBlock hr (redFn (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) PP.1 (finE (D.sp.Y 0) κ))) ∈ d.c.P.H) := by
  intro D u F₀ S d k _ _ _ _ ι o G h0 hE hB hT _ hG hX B hBl hA a₀ ha₀ a haf haz hSt hr κ hκ hκS
  exact MemMatch.mem_iff S d o.τ o.cG G h0 hE hB hT hG hX B hBl hA a₀ ha₀ a haf haz _ rfl
    (fun y hy hs => ((hSt y).1 ⟨hy, hs⟩).2) hr κ hκ hκS

theorem memMatch : ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.Core.Mi.IdE S.X → d.Base → IsTypePlaces d.c.Pg → GlobalTheory.FinPl.PinOff o → GlobalTheory.LocMod.PinGBy G o.cG → (∀ z, z ∈ (d.x 0).L ↔ z ∈ (F₀ u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) → LevX (F₀ u) d h0 → ∀ (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)), B.lev = d.B 0 D.R.rS h0 → B.Adapted (S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β)) ↔ ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset)) → ∀ (hr : D.R.r ≤ (D.sp.Y 0).rank) (κ : GA D (D.sp.Y 0)), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) → ((iotaX S.X S.inst κ).2 ∈ S.X.K2 ↔ (fun PP : d.c.Pg => upperLeftBlock hr (redFn (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) PP.1 (finE (D.sp.Y 0) κ))) ∈ d.c.P.H) := by
  intro D u F₀ S d k _ _ _ _ ι o G h0 hE hB hT hO hG _
  exact memMatch_noLat D u F₀ S d k ι o G h0 hE hB hT hO hG

end GlobalTheory.Core.Mi

end
