import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FrobeniusSqComparisonLetter
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemmaDN0

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries TensorProduct Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Main

variable (W : LocWach PD LL O v n)

theorem frobenius_sq_bound_at_zero [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (h3₁ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₁) (h3₂ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₂)
    (hmod₁ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₁ W.π₀) (hmod₂ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₂ W.π₀)
    {c : ZMod n} {kB hh bb η' b' S : ℕ}
    (hM₁ : ∀ z ∈ W.Nl T₁ (c - 1), W.Q ^ kB • W.φD T₁ z ∈ W.N T₁)
    (hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ kB • W.φD T₂ z ∈ W.N T₂)
    (hU : ∀ y ∈ W.Nl T₂ (c - 1), W.Q ^ bb • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ (c - 1 - 1)))
    (hMη : ∀ z ∈ W.Nl T₂ (c - 1 - 1), W.Q ^ η' • W.φD T₂ z ∈ W.N T₂)
    (hM₂' : ∀ z ∈ W.Nl T₂ (c - 1 - 1 - 1), W.Q ^ hh • W.φD T₂ z ∈ W.N T₂)
    (hD0c : ∀ x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c, ((PD.p : O) ^ S) • x ∈ Xd W T₂ c kB)
    (hD0c2 : ∀ x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1),
      ((PD.p : O) ^ S) • x ∈ Xd W T₂ (c - 1 - 1) hh)
    (hle : DcrisL PD T₂.ρ (W.emb (c - 1)) ≤ FilCris PD T₂.ρ (b' : ℤ)) {k : ℤ}
    (hGc : ∀ x ∈ (fun z => φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) z)) ''
        Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (c - 1 - 1 - 1),
      x ∈ FilCris PD T₂.ρ (b' : ℤ) → (PD.p : LL) ^ k • x ∈ Formalism.MainNotions.CrystallineLiftingInputs.DlatImg W F (c - 1))
    {e pad : ℕ} (hexp : (e : ℤ) + hh = pad + k + bb)
    {y : W.DD T₂} (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) :
    ∃ x : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c x ∧
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ (e + S + S)) • y - W.map F x) := by
  obtain ⟨y1, hy1, e1⟩ := cmp_of_mem_X W T₂ hs hR h3₂ hM₂ (hD0c y hy)
  obtain ⟨y2, hy2, e2⟩ := cmp_up W T₂ hs h3₂ hmod₂ hU hMη hy1
  obtain ⟨y3, hy3, e3⟩ := cmp_of_mem_X W T₂ hs hR h3₂ hM₂' (hD0c2 y2 hy2)
  have hG := hGc _ (frobenius_sq_mem_lattice_image W T₂ c hy3) (hle (frobenius_sq_comparison_letter W T₂ c hy3))
  refine exists_inI_inPN_pow_smul_sub_map W hs hR F h3₁ h3₂ hmod₁ hmod₂ hM₁ hM₂ hy
    (d1 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y1) (d2 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y2)
    (d3 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y3) (s₁ := S) (s₂ := S) ?_ e2 ?_ hG hexp
  · rw [← e1, cmpD_osmul W T₂ _ (NDl_N W T₂ hy), map_pow, map_natCast]
  · rw [← e3, cmpD_osmul W T₂ _ (NDl_N W T₂ hy2), map_pow, map_natCast]

theorem frobenius_sq_bound_of_local [NeZero n] (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hG : Formalism.MainNotions.RamifiedCoefficientChains.S9.LemmaGs W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.S9.LemmaDN W) (hD0 : LemmaDN0 W) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.LatticeBoundSix W := by
  intro d T₁ T₂ F b S η m hset
  have hset' := hset
  obtain ⟨hCA, hl, hn, ⟨hDom, hDVR, hFrac⟩, -, hSur, -, -, -, -⟩ := hset'
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
  have h5₁ := h5 T₁ (boxM d b S η) (boxH d b S η) hSur.1 (rk_jumpsLet₁ W hset)
  have h5₂ := h5 T₂ (boxM d b S η) (boxH d b S η) hSur.2.1 (rk_jumpsLet₂ W hE hC hQ hset)
  have hl2 : 2 ≤ PD.p := by omega
  have hlam := one_le_lam PD.p (hpar n b S + η) hl2
  have haR := aR_nonneg PD.p (hpar n b S + η) hl2
  have hl1 : (0 : ℝ) < (PD.p : ℝ) - 1 := by
    have : (11 : ℝ) ≤ PD.p := by exact_mod_cast hl
    linarith
  set σ : ℝ := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ PD.p (hpar n b S + η) with hσ
  set EGv : ℝ := EG PD.p (hpar n b S) η S with hEGv
  have hσ0 : 0 ≤ σ := by
    rw [hσ, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂]; positivity
  have hEG0 : 0 ≤ EGv := by
    rw [hEGv, EG]
    have : 0 ≤ (3 * (aN PD.p (hpar n b S + η) : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((PD.p : ℝ) - 1) :=
      div_nonneg (by positivity) hl1.le
    linarith
  refine ⟨S + ⌈EGv + σ⌉₊, ?_, ?_⟩
  · unfold B6
    have h1 := Nat.ceil_lt_add_one (add_nonneg hEG0 hσ0)
    push_cast
    linarith
  intro c hc FF _ _ _ _ Fs w hw
  have hcD : (c.val + d) % 2 = 0 := (Finset.mem_filter.1 hc).2
  have hc1 : ((c - 1).val + d) % 2 = 1 := by
    have := parity_succ hn d (c - 1)
    rw [sub_add_cancel] at this
    omega
  have hc2 : ((c - 1 - 1).val + d) % 2 = 0 := by
    have := parity_succ hn d (c - 1 - 1)
    rw [sub_add_cancel] at this
    omega
  have hc2m : c - 1 - 1 ∈ evens n d := Finset.mem_filter.2 ⟨Finset.mem_univ _, hc2⟩
  have hMc : boxM d b S η c = b c + S := if_pos hcD
  have hMc1 : boxM d b S η (c - 1) = η := if_neg (by omega)
  have hHc1 : boxH d b S η (c - 1) = b (c - 1) + S := if_neg (by omega)
  have hMc2 : boxM d b S η (c - 1 - 1) = b (c - 1 - 1) + S := if_pos hc2
  have hM₁ : ∀ z ∈ W.Nl T₁ (c - 1), W.Q ^ (b c + S) • W.φD T₁ z ∈ W.N T₁ := by
    rw [← hMc]; exact h5₁.1 c
  have hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ (b c + S) • W.φD T₂ z ∈ W.N T₂ := by
    rw [← hMc]; exact h5₂.1 c
  have hU : ∀ y ∈ W.Nl T₂ (c - 1), W.Q ^ (b (c - 1) + S) • y ∈
      Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ (c - 1 - 1)) := by
    rw [← hHc1]; exact h5₂.2.1 (c - 1)
  have hMη : ∀ z ∈ W.Nl T₂ (c - 1 - 1), W.Q ^ η • W.φD T₂ z ∈ W.N T₂ := by
    rw [← hMc1]; exact h5₂.1 (c - 1)
  have hM₂' : ∀ z ∈ W.Nl T₂ (c - 1 - 1 - 1), W.Q ^ (b (c - 1 - 1) + S) • W.φD T₂ z ∈ W.N T₂ := by
    rw [← hMc2]; exact h5₂.1 (c - 1 - 1)

  obtain ⟨E, hE', hGx⟩ := hG d T₁ T₂ F b S η m hset (c - 1) hc1
  have e12 : c - 1 - 2 = c - 1 - 1 - 1 := by ring
  rw [e12] at hGx
  have hEle : (E : ℝ) ≤ EGv := by
    refine hE'.trans ?_
    rw [hEGv, EG]
    have : 3 * aR PD.p (hpar n b S + η) ≤ 3 * (aN PD.p (hpar n b S + η) : ℝ) := by
      have := Nat.le_ceil (aR PD.p (hpar n b S + η)); unfold aN; linarith
    have := div_le_div_of_nonneg_right (a := 3 * aR PD.p (hpar n b S + η) + S + 2 * η)
      (b := 3 * (aN PD.p (hpar n b S + η) : ℝ) + S + 2 * η) (by linarith) hl1.le
    linarith
  set k : ℤ := ⌈(E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 PD.p (hpar n b S + η) +
    ((b (c - 1 - 1) + S : ℕ) : ℝ) - (b (c - 1) : ℝ)⌉ with hk
  have hk' : k = ⌈(E : ℝ) + σ⌉ + (((b (c - 1 - 1) + S : ℕ) : ℤ) - (b (c - 1) : ℤ)) := by
    rw [hk, ← Int.ceil_add_intCast]
    congr 1
    rw [hσ]
    push_cast
    simp only [Formalism.MainNotions.CrystallineLiftingInputs.sig2, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂]
    ring
  have hceil : ⌈(E : ℝ) + σ⌉ ≤ ((⌈EGv + σ⌉₊ : ℕ) : ℤ) := by
    have h1 : ⌈(E : ℝ) + σ⌉ ≤ ⌈EGv + σ⌉ := Int.ceil_le_ceil (by linarith)
    have h2 : ((⌈EGv + σ⌉₊ : ℕ) : ℤ) = ⌈EGv + σ⌉ := Int.natCast_ceil_eq_ceil (add_nonneg hEG0 hσ0)
    omega
  set pad : ℕ := (((⌈EGv + σ⌉₊ : ℕ) : ℤ) - ⌈(E : ℝ) + σ⌉).toNat with hpad
  have hpad' : (pad : ℤ) = ((⌈EGv + σ⌉₊ : ℕ) : ℤ) - ⌈(E : ℝ) + σ⌉ := Int.toNat_of_nonneg (by omega)
  have hexp : ((S + ⌈EGv + σ⌉₊ : ℕ) : ℤ) + ((b (c - 1 - 1) + S : ℕ) : ℤ) =
      (pad : ℤ) + k + ((b (c - 1) + S : ℕ) : ℤ) := by
    rw [hpad', hk']
    push_cast
    ring
  haveI := rk_fd_letter₂ W hset (c - 1)
  have hw' : ∀ f, w f ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c := hw
  refine ⟨?_, ?_⟩
  · exact frobenius_sq_bound_at W hs hR F h3₁ h3₂ hmod₁ hmod₂ hM₁ hM₂ hU hMη hM₂'
      (hD d T₁ T₂ F b S η m hset c hc) (hD d T₁ T₂ F b S η m hset (c - 1 - 1) hc2m)
      (rk_corankQ₂ W hE hC hQ hset (c - 1) hc1) hGx hexp FF Fs w hw'
  · intro hm0 f
    have h := frobenius_sq_bound_at_zero W hs hR F h3₁ h3₂ hmod₁ hmod₂ hM₁ hM₂ hU hMη hM₂'
      (hD0 d T₁ T₂ F b S η m hset hm0 c hc) (hD0 d T₁ T₂ F b S η m hset hm0 (c - 1 - 1) hc2m)
      (rk_corank_zero₂ W hE hC hQ hset hm0 (c - 1) hc1) hGx hexp (hw' f)
    rw [show S + ⌈EGv + σ⌉₊ + 2 * S = S + ⌈EGv + σ⌉₊ + S + S by ring]
    exact h

end Main

section Record

theorem steps6_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hG : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.S9.LemmaGs ((HW l).W K 1 LL hg))
    (hD : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.S9.LemmaDN ((HW l).W K 1 LL hg))
    (hD0 : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaDN0 ((HW l).W K 1 LL hg)) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.steps6 D HW F := by
  intro l _ K LL hg _
  have h1 := hA.1 l K 1 LL hg
  have h11 := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  exact frobenius_sq_bound_of_local _ h1.2.2.1 h1.2.2.2.2.1 h1.2.2.2.2.2.2.2.2.1 h11.1 h11.2.1 h11.2.2
    (hG l K LL hg) (hD l K LL hg) (hD0 l K LL hg)

end Record

end Formalism.MainNotions.N.Pv.LocalLengthBound
