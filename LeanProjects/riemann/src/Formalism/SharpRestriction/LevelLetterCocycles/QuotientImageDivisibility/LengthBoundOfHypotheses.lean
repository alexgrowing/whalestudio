import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.InIZero
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.H2Bound
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ContentBoundLevel
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkFilLevEq
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemmaDN0

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

theorem passage_chain_zero {O FF : Type} [CommRing O] [AddCommGroup FF] [Module O FF] {lenO : ℕ∞} {c : ℝ}
    {A Bs : Submodule O FF} {ng : ℕ} (h : Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain lenO 0 c A Bs ng 0) : Bs = A := by
  obtain ⟨k, Fl, gen, h0, hk, hsub, hg, hl, hs⟩ := h
  have hall : ∀ i < k, i ∈ gen := by
    intro i hi
    by_contra hig
    have hsub' : gen ⊆ (Finset.range k).erase i := fun x hx =>
      Finset.mem_erase.2 ⟨fun h => hig (h ▸ hx), hsub hx⟩
    have := Finset.card_le_card hsub'
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 hi), Finset.card_range] at this
    omega
  have step : ∀ i < k, Fl (i + 1) = Fl i := by
    intro i hi
    obtain ⟨hle, Q, _, _, ob, hker, hgen, -⟩ := hs i hi
    obtain ⟨s, hs0, hspan⟩ := hgen (hall i hi)
    have hsE : s = ∅ := Finset.card_eq_zero.1 (by omega)
    refine le_antisymm hle fun x hx => ?_
    have h1 : ob ⟨x, hx⟩ = 0 := by
      have hm : ob ⟨x, hx⟩ ∈ Submodule.span O (↑s : Set Q) := by rw [hspan]; trivial
      rw [hsE, Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hm
      exact hm
    exact (hker ⟨x, hx⟩).1 h1
  have hall' : ∀ i ≤ k, Fl i = Fl 0 := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ j ih => intro hj; rw [step j (by omega), ih (by omega)]
  rw [← hk, ← h0]
  exact hall' k le_rfl

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section SlopeTestRemainingChoices

variable (W : LocWach PD LL O v n)

theorem qK_mem [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (T : LocLat G Qp LL O) {c : ZMod n} {Bn η : ℕ}
    (hM : ∀ z ∈ W.Nl T (c - 1), W.Q ^ Bn • W.φD T z ∈ W.N T) {x : W.DD T}
    (hx : Formalism.MainNotions.RamifiedCoefficientChains.S9.QPowSmulMemPullback W T c η x) : W.Q ^ (η + Bn) • x ∈ W.N T := by
  have key : ∀ z ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1) 1, W.Q ^ Bn • z ∈ W.N T := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, ⟨hyN, hyD⟩, rfl⟩ := hz
      rw [pow_one]
      exact hM y (mem_Nl W T hyN hyD.1)
    | zero => rw [smul_zero]; exact (W.N T).zero_mem
    | add z₁ z₂ _ _ h₁ h₂ => rw [smul_add]; exact (W.N T).add_mem h₁ h₂
    | smul a z _ h => rw [aself_comm W T]; exact (W.N T).smul_mem a h
  obtain ⟨U, hU⟩ := qp_eq_unit W hs hR
  have h1 := key _ hx.1
  have e : W.Q ^ (η + Bn) • x = ((U⁻¹ : (LetA O n)ˣ) : LetA O n) ^ η •
      (W.Q ^ Bn • (Formalism.MainNotions.LiftingTheory.qp W ^ η • x)) := by
    rw [hU, mul_pow, smul_smul, smul_smul]
    congr 1
    have hUU : ((U⁻¹ : (LetA O n)ˣ) : LetA O n) * (U : LetA O n) = 1 := Units.inv_mul U
    calc W.Q ^ (η + Bn) = (((U⁻¹ : (LetA O n)ˣ) : LetA O n) * (U : LetA O n)) ^ η *
          (W.Q ^ η * W.Q ^ Bn) := by rw [hUU, one_pow, one_mul, pow_add]
      _ = _ := by ring
  rw [e]
  exact (W.N T).smul_mem _ h1

end SlopeTestRemainingChoices

section Main

theorem ndl_osmul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {i : ZMod n} (o : O) {x : W.DD T}
    (hx : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) : o • x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i := by
  refine ⟨?_, ?_, fun δ hδ => ?_⟩
  · rw [← algebraMap_smul (LetA O n)]; exact (W.N T).smul_mem _ (NDl_N W T hx)
  · rw [osmul_comm W T, (NDl_DL W T hx).1]
  · rw [map_smul, (NDl_DL W T hx).2 δ hδ]

theorem frobenius_sq_letter_shift (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) {y : W.DD T}
    (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1)) :
    φVB PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y)) ∈
      DcrisL PD T.ρ (W.emb (c - 1)) := frobenius_sq_comparison_letter W T c hy

variable (W : LocWach PD LL O v n)

theorem length_bound_of_hypotheses [NeZero n] (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hMC : MemCrit W) (hH2 : H2Bound W) (hL41 : ContentBoundLevel W)
    (hD : Formalism.MainNotions.RamifiedCoefficientChains.S9.LemmaDN W) (hD0 : LemmaDN0 W)
    (hχ0 : algebraMap O LL (W.χΓ W.gam : O) ≠ 0)
    (hχ : ∀ i : ℤ, i ≠ 0 → (algebraMap O LL (W.χΓ W.gam : O)) ^ i ≠ 1)
    (hγN : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (c : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∀ (x : W.DD T) (hx : x ∈ W.N T) (hγx : W.γ T x ∈ W.N T) (k : ℤ),
        W.levN T c ζ ⟨W.γ T x, hγx⟩ k = (algebraMap O LL (W.χΓ W.gam : O)) ^ k • W.levN T c ζ ⟨x, hx⟩ k)
    (hγA : ∀ (c : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ f : LetA O n,
      W.lev c ζ (W.γA W.gam f) = PowerSeries.rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev c ζ f))
    (hTr : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (c : ZMod n) (ζ ζ₀ : LL),
      IsPrimitiveRoot ζ PD.p → IsPrimitiveRoot ζ₀ PD.p → ∃ δ ∈ W.DelF, ∃ χ : LL, χ ≠ 0 ∧
      (∀ (x : ↥(W.N T)) (hx : W.γD T δ x ∈ W.N T) (k : ℤ),
        W.levN T c ζ ⟨W.γD T δ x, hx⟩ k = χ ^ k • W.levN T c ζ₀ x k) ∧
      (∀ f : LetA O n, W.lev c ζ (W.γA δ f) = PowerSeries.rescale χ (W.lev c ζ₀ f))) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.WachVectorLiftingBound W := by
  intro d T₁ T₂ F b S η m hset
  have hset' := hset
  obtain ⟨hCA, hl, hn, ⟨hDom, hDVR, hFrac⟩, ⟨ζ₀, hζ₀⟩, hSur, -, -, -, -⟩ := hset'
  haveI := hDom
  haveI := hDVR
  haveI := hFrac
  obtain ⟨hbij, hs, hp2⟩ := hCA
  have hK1 : Module.finrank K₀ K = 1 := Formalism.MainNotions.UnusedSlot80.SatW.finrank_one_of_bij' hbij
  obtain ⟨-, -, h9₁⟩ := h9 T₁ hSur.1 hs hp2
  obtain ⟨hR, hmod₁⟩ := h9₁ hK1
  obtain ⟨-, -, h9₂⟩ := h9 T₂ hSur.2.1 hs hp2
  obtain ⟨-, hmod₂⟩ := h9₂ hK1
  have h3₁ := h3 T₁ hSur.1
  have h3₂ := h3 T₂ hSur.2.1
  have h5₂ := h5 T₂ (boxM d b S η) (boxH d b S η) hSur.2.1 (rk_jumpsLet₂ W hE hC hQ hset)
  have hT₁ := hSur.1
  have hT₂ := hSur.2.1
  have hl2 : 2 ≤ PD.p := by omega
  have hlam := Formalism.MainNotions.RamifiedCoefficientChains.one_le_lam PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) hl2
  have haR := Formalism.MainNotions.RamifiedCoefficientChains.aR_nonneg PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) hl2
  have hl1 : (0 : ℝ) < (PD.p : ℝ) - 1 := by
    have : (11 : ℝ) ≤ PD.p := by exact_mod_cast hl
    linarith
  have hl0 : (0 : ℝ) < (PD.p : ℝ) := by linarith
  set σ : ℝ := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) with hσ
  set EGv : ℝ := Formalism.MainNotions.RamifiedCoefficientChains.S9.EG PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S) η S with hEGv
  have hσ0 : 0 ≤ σ := by rw [hσ, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂]; positivity
  have hEG0 : 0 ≤ EGv := by
    rw [hEGv, Formalism.MainNotions.RamifiedCoefficientChains.S9.EG]
    have : 0 ≤ (3 * (Formalism.MainNotions.RamifiedCoefficientChains.S9.aN PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) : ℝ) + (S : ℝ) + 2 * (η : ℝ)) /
        ((PD.p : ℝ) - 1) := div_nonneg (by positivity) hl1.le
    linarith
  set Bd : ℝ := Formalism.MainNotions.RamifiedCoefficientChains.S9.wachVectorLiftingExponent PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S) η S with hBd
  have hBd0 : 0 ≤ Bd := by
    rw [hBd, Formalism.MainNotions.RamifiedCoefficientChains.S9.wachVectorLiftingExponent]
    have h1 : 0 ≤ ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℝ) / ((PD.p : ℝ) * ((PD.p : ℝ) - 1)) :=
      div_nonneg (by positivity) (by positivity)
    have h2 : 0 ≤ ((S : ℝ) + 1) / ((PD.p : ℝ) - 1) := div_nonneg (by positivity) hl1.le
    have h3' : (0 : ℝ) ≤ S := by positivity
    linarith
  set E : ℕ := ⌊Bd⌋₊ with hEdef
  refine ⟨E, Nat.floor_le hBd0, fun c hc FF _ _ _ _ Fs w hw => ?_⟩
  have hcD : (c.val + d) % 2 = 0 := (Finset.mem_filter.1 hc).2
  have hc1 : ((c - 1).val + d) % 2 = 1 := by
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d (c - 1)
    rw [sub_add_cancel] at this
    omega
  have hc2 : ((c - 1 - 1).val + d) % 2 = 0 := by
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d (c - 1 - 1)
    rw [sub_add_cancel] at this
    omega
  have hc2m : c - 1 - 1 ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d := Finset.mem_filter.2 ⟨Finset.mem_univ _, hc2⟩
  have hMc : boxM d b S η c = b c + S := if_pos hcD
  have hMc2 : boxM d b S η (c - 1 - 1) = b (c - 1 - 1) + S := if_pos hc2
  have hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ (b c + S) • W.φD T₂ z ∈ W.N T₂ := by
    rw [← hMc]; exact h5₂.1 c
  have hM₂' : ∀ z ∈ W.Nl T₂ (c - 1 - 1 - 1), W.Q ^ (b (c - 1 - 1) + S) • W.φD T₂ z ∈ W.N T₂ := by
    rw [← hMc2]; exact h5₂.1 (c - 1 - 1)
  have hηb := rk_eta_lt W hset c
  have hB1 : 1 ≤ b c + S := by omega
  have hQK : ∀ f, W.Q ^ (η + (b c + S)) • w f ∈ W.N T₂ := fun f => qK_mem W hs hR T₂ hM₂ (hw f)
  have hγw : ∀ f, W.γ T₂ (w f) - w f ∈ W.N T₂ := by
    intro f
    obtain ⟨y, hyN, -, hye⟩ := (hw f).2.2.2
    rw [hye, pow_one]
    exact (W.N T₂).smul_mem _ hyN
  obtain ⟨u₀, hu₀, hu0⟩ := lev_q_simple W c ζ₀ hζ₀
  have hζ₀' : IsPrimitiveRoot ζ₀ (PD.p ^ (0 + 1)) := by rwa [zero_add, pow_one]
  have hLv := (hLev T₂ hT₂ c 0 ζ₀ hζ₀').1
  obtain ⟨dd, hddLB, hdde, hddF, hdda, hdds⟩ := fam_exp W T₂ (A := ↥Fs) hs c ζ₀ hLv _ hχ0 hχ
    (hγN T₂ hT₂ c ζ₀ hζ₀) (hγA c ζ₀ hζ₀) u₀ hu₀ hu0 (η + (b c + S)) w hQK hγw
  obtain ⟨ec, hec, hH⟩ := hH2 d T₁ T₂ F b S η m hset c hc
  obtain ⟨κ, hκ, hLk⟩ := hL41 d T₁ T₂ F b S η m hset c hc
  set hh : ℕ := b (c - 1 - 1) + S with hhh

  have hbh : (b c : ℝ) ≤ (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℝ) := by
    have : b c ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ c)
    rw [Formalism.MainNotions.RamifiedCoefficientChains.hpar]; push_cast; exact_mod_cast (by omega : b c ≤ Finset.univ.sup b + S)
  have hEge : (ec : ℤ) + κ - hh ≤ (E : ℤ) := by
    have hreal : ((ec : ℤ) + κ - hh : ℝ) ≤ Bd := by
      rw [hBd, Formalism.MainNotions.RamifiedCoefficientChains.S9.wachVectorLiftingExponent]
      have key : (((b c + S : ℕ) : ℝ) + 1) / ((PD.p : ℝ) - 1) - (b c : ℝ) / (PD.p : ℝ) =
          (b c : ℝ) / ((PD.p : ℝ) * ((PD.p : ℝ) - 1)) + ((S : ℝ) + 1) / ((PD.p : ℝ) - 1) := by
        field_simp
        push_cast
        ring
      have hdiv : (b c : ℝ) / ((PD.p : ℝ) * ((PD.p : ℝ) - 1)) ≤
          ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℝ) / ((PD.p : ℝ) * ((PD.p : ℝ) - 1)) :=
        div_le_div_of_nonneg_right hbh (by positivity)
      simp only [hhh] at hκ ⊢
      push_cast at hec hκ key ⊢
      linarith
    have h1 : (ec : ℤ) + κ - hh ≤ ⌊Bd⌋ := Int.le_floor.2 (by exact_mod_cast hreal)
    have h2 : (⌊Bd⌋₊ : ℤ) = ⌊Bd⌋ := by
      rw [← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.2 hBd0)]
    rw [hEdef, h2]
    exact h1
  set N₀ : ℕ := ((E : ℤ) - ec - (κ - hh)).toNat with hN₀
  have hN₀' : (N₀ : ℤ) = (E : ℤ) - ec - (κ - hh) := Int.toNat_of_nonneg (by omega)
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  set Fη := Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-(η : ℤ)) with hFη
  have hex : ∀ f : ↥Fs, ∃ x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1),
      (PD.p : LL) ^ E • dd f 0 - (PD.p : LL) ^ (κ - hh) • ιV PD (LL := LL) (V := T₂.V)
        (φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ x))) ∈ Fη := by
    intro f
    obtain ⟨x, hx, hxF⟩ := hH ζ₀ hζ₀ u₀ hu₀ hu0 (w f) (hw f) (η + (b c + S)) (hQK f) (dd f)
      (hddLB f) (hdde f)
    refine ⟨((PD.p : ℕ) : O) ^ N₀ • x, ndl_osmul W T₂ _ hx, ?_⟩
    have hcm : Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (((PD.p : ℕ) : O) ^ N₀ • x) =
        (PD.p : LL) ^ N₀ • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ x := by
      rw [cmpD_osmul W T₂ _ (NDl_N W T₂ hx), map_pow, map_natCast]
    rw [hcm, map_smul, map_smul, map_smul, smul_smul]
    have hsc : (PD.p : LL) ^ (κ - hh) * (PD.p : LL) ^ N₀ = (PD.p : LL) ^ ((E : ℤ) - ec) := by
      rw [← zpow_natCast, ← zpow_add₀ hp, hN₀']; ring_nf
    have hsc2 : (PD.p : LL) ^ E = (PD.p : LL) ^ ((E : ℤ) - ec) * (PD.p : LL) ^ ec := by
      rw [← zpow_natCast, ← zpow_natCast (PD.p : LL) ec, ← zpow_add₀ hp]; ring_nf
    rw [hsc, hsc2, ← smul_smul, ← smul_sub]
    exact Fη.smul_mem _ hxF

  haveI := rk_fd_letter₂ W hset (c - 1)
  have hRk := rk_corankQ₂ W hE hC hQ hset (c - 1) hc1
  have hDN := hD d T₁ T₂ F b S η m hset (c - 1 - 1) hc2m
  obtain ⟨F3, hF3, ch3, hell⟩ := pass3 W T₂ hs hR h3₂ hmod₂ c η hM₂' hDN
    (FilCris PD T₂.ρ (b (c - 1) : ℤ)) hRk Fs (fun f => dd f 0)
    (fun f g => by rw [hdda]; rfl) (fun o f => by rw [hdds]; rfl) hex

  haveI : FiniteDimensional LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c) := by
    haveI := rk_fd_letter₂ W hset c
    exact Module.Finite.map _ _
  haveI : FiniteDimensional LL ↥Fη := by
    have hle : Fη ≤ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c := by
      rw [hFη, Formalism.MainNotions.UnusedSlot80.LevR.filLev_zero]; exact inf_le_left
    exact Submodule.finiteDimensional_of_le hle
  have hrk := rk_evenQ₂ W hE hC hQ hset c hcD
  have hlow : ∀ i : ℤ, ((b c + S : ℕ) : ℤ) ≤ i →
      Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c ≤ Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-i) :=
    fun i hi => rk_low₂ W hE hC hQ hset c hcD (-i) (by omega)
  have hTr₂ := fun ζ hζ => hTr T₂ hT₂ c ζ ζ₀ hζ hζ₀
  obtain ⟨F4, hF4, y, ch4, hres⟩ := pass4 W hs hR F hT₁ hT₂ hMC c ζ₀ hTr₂ u₀ hu₀ hu0
    (m := m) (cc := Formalism.MainNotions.RamifiedCoefficientChains.S9.lenC (Module.finrank LL T₂.V) m PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) S)
    hB1 hlow hrk (FilCris PD T₂.ρ (b (c - 1) : ℤ)) F3 (w.comp (Submodule.inclusion hF3))
    (fun f => (hw _).2.1) (fun f => hQK _) (fun f => dd (Submodule.inclusion hF3 f))
    (fun f => hddLB _) (fun f => hdde _) (fun f i hi => hddF _ i hi)
    (fun f g => by rw [map_add, hdda]) (fun o f => by rw [map_smul, hdds])
    hell (fun ell hell1 hell2 => hLk ell hell1 hell2) hζ₀
  refine ⟨⟨F4, hF4.trans hF3, y, (ch3.trans ch4).mono (by norm_num) (by norm_num), fun f => hres f⟩, ?_⟩

  intro hm0
  subst hm0
  have hCD := rk_corank_zero₂ W hE hC hQ hset rfl (c - 1) hc1
  have hell0 : ∀ f : ↥Fs, ∃ ell ∈ (fun z => φVB PD (LL := LL) (V := T₂.V)
      (φVB PD (LL := LL) (V := T₂.V) z)) '' Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (c - 1 - 1 - 1),
      ell ∈ FilCris PD T₂.ρ (b (c - 1) : ℤ) ∧
      (PD.p : LL) ^ (E + S) • dd f 0 - (PD.p : LL) ^ κ •
        ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) ell) ∈ Fη := by
    intro f
    obtain ⟨x, hx, hxF⟩ := hex f
    have hx0 := hD0 d T₁ T₂ F b S η 0 hset rfl (c - 1 - 1) hc2m x hx
    obtain ⟨y0, hy0, hy0e⟩ := cmp_of_mem_X W T₂ hs hR h3₂ hM₂' hx0
    have hy0N := NDl_N W T₂ hy0
    refine ⟨φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y0)),
      ⟨Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y0, ⟨y0, hy0N, NDl_DL W T₂ hy0,
        Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T₂ hy0N⟩, rfl⟩, hCD (frobenius_sq_letter_shift W T₂ c hy0), ?_⟩
    have hcm : Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (((PD.p : ℕ) : O) ^ S • x) =
        (PD.p : LL) ^ S • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ x := by
      rw [cmpD_osmul W T₂ _ (NDl_N W T₂ hx), map_pow, map_natCast]
    rw [hcm] at hy0e
    have h1 := Fη.smul_mem ((PD.p : LL) ^ S) hxF
    have hsc : (PD.p : LL) ^ (κ - hh) * (PD.p : LL) ^ hh = (PD.p : LL) ^ κ := by
      rw [← zpow_natCast, ← zpow_add₀ hp, sub_add_cancel]
    have hXS : (PD.p : LL) ^ S • ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V)
        (φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ x))) =
        (PD.p : LL) ^ hh • ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V)
          (φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y0)))) := by
      have := congrArg (fun z => ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V)
        (φVB PD (LL := LL) (V := T₂.V) z))) hy0e
      simpa only [map_smul] using this
    have e : (PD.p : LL) ^ (E + S) • dd f 0 - (PD.p : LL) ^ κ • ιV PD (LL := LL) (V := T₂.V)
        (φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V)
          (φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y0)))) =
        (PD.p : LL) ^ S • ((PD.p : LL) ^ E • dd f 0 - (PD.p : LL) ^ (κ - hh) • ιV PD (LL := LL)
          (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V)
            (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ x)))) := by
      rw [smul_sub, smul_smul, smul_comm ((PD.p : LL) ^ S) ((PD.p : LL) ^ (κ - hh)), hXS, smul_smul,
        hsc, ← pow_add, add_comm S E]
    rw [e]
    exact h1
  have hrk0 := rk_evenQ₂ W hE hC hQ hset c hcD
  obtain ⟨F4', hF4', y', ch4', hres'⟩ := pass4 W hs hR F hT₁ hT₂ hMC c ζ₀ hTr₂ u₀ hu₀ hu0
    (m := 0) (cc := 0) (e₂ := E + S) hB1 hlow hrk0 (FilCris PD T₂.ρ (b (c - 1) : ℤ)) Fs w
    (fun f => (hw _).2.1) hQK dd hddLB hdde hddF hdda hdds hell0
    (fun ell hell1 hell2 => hLk ell hell1 hell2) hζ₀
  have hFeq : F4' = Fs := passage_chain_zero ch4'
  refine ⟨y'.comp (Submodule.inclusion (le_of_eq hFeq.symm)), fun f => ?_⟩
  exact hres' (Submodule.inclusion (le_of_eq hFeq.symm) f)

end Main

end Formalism.MainNotions.N.Pv.LocalLengthBound
