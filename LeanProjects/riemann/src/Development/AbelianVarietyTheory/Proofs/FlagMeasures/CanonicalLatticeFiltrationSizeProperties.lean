import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorantsStatement

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

namespace GlobalTheory.CountSteps

section Abstract

variable {R V E : Type} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ρ : V →+ E} {L : Submodule R V}

theorem strict_eq (hL : IsLat ρ L) (θ : ℝ) :
    ∃ θ₀, θ < θ₀ ∧ ∀ θ', θ < θ' → θ' ≤ θ₀ →
      sSup {N : Submodule R V | N ≤ L ∧ N ≠ ⊥ ∧ θ < muMin ρ N} = hnStep ρ L θ' := by

  obtain ⟨t, ht, hsup⟩ :=
    finSup R V E ρ L {N | N ≤ L ∧ N ≠ ⊥ ∧ θ < muMin ρ N} hL (fun N hN => hN.1)
  obtain ⟨θ₀, hθ₀, hle⟩ : ∃ θ₀, θ < θ₀ ∧ ∀ N ∈ t, θ₀ ≤ muMin ρ N := by
    rcases t.eq_empty_or_nonempty with h | h
    · exact ⟨θ + 1, by linarith, by simp [h]⟩
    · obtain ⟨N₀, hN₀, hmin⟩ := t.exists_min_image (fun N => muMin ρ N) h
      exact ⟨muMin ρ N₀, (ht hN₀).2.2, hmin⟩
  refine ⟨θ₀, hθ₀, fun θ' h1 h2 => le_antisymm ?_ ?_⟩
  · rw [hsup]
    unfold hnStep
    refine Finset.sup_le fun N hN => ?_
    exact le_sSup ⟨(ht hN).1, (ht hN).2.1, h2.trans (hle N hN)⟩
  · unfold hnStep
    exact sSup_le_sSup fun N hN => ⟨hN.1, hN.2.1, lt_of_lt_of_le h1 hN.2.2⟩

private lemma zl_mono' {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := hy
  exact ⟨a, h ha, rfl⟩

theorem isSat_of_le {S N : Submodule R V} (hS : IsSat ρ L S) (h1 : S ≤ N) (h2 : N ≤ L) :
    IsSat ρ N S := by
  unfold IsSat Formalism.F.IsSaturated at *
  exact ⟨h1, zl_mono' h1, fun y hy hspan => hS.2.2 y (zl_mono' h2 hy) hspan⟩

theorem quot_slope_lt (hL : IsLat ρ L) (θ : ℝ) {N : Submodule R V} (h1 : hnStep ρ L θ < N) (h2 : N ≤ L) :
    Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ (hnStep ρ L θ))) < θ := by
  obtain ⟨hsat, -, -, hmax⟩ := hnStep_spec R V E ρ L hL θ
  obtain ⟨hsub, -, hsatEq, -, -, -, -, -⟩ := satBasic R V E ρ L hL
  obtain ⟨-, -, -, -, -, -, -, hq⟩ := satBasic R V E ρ N (hsub N h2)
  obtain ⟨hrk, hrkle, hdeg⟩ := hq _ (isSat_of_le hsat h1.le h2)

  have hne : rk ρ (hnStep ρ L θ) ≠ rk ρ N := fun h => h1.ne (hsatEq _ _ hsat h1.le h2 h.symm).symm
  have hlt : (rk ρ (hnStep ρ L θ) : ℝ) < rk ρ N := by exact_mod_cast lt_of_le_of_ne hrkle hne
  have key := hmax N h1 h2
  unfold Formalism.F.slope
  rw [hrk, hdeg, Nat.cast_sub hrkle, div_lt_iff₀ (by linarith)]
  exact key

theorem step_eq_bot (hL : IsLat ρ L) (h0 : L ≠ ⊥) (θ : ℝ) : hnStep ρ L θ = ⊥ ↔ muMax ρ L < θ := by
  obtain ⟨hsat, hmin, hcont, -⟩ := hnStep_spec R V E ρ L hL θ
  obtain ⟨hsub, -, -, hrk0, -, -, -, -⟩ := satBasic R V E ρ L hL
  obtain ⟨hmaxL, -, ⟨N, hNsat, hN0, hNslope⟩, -, -⟩ := muChar R V E ρ L hL h0
  have hdegL : ∀ S : Submodule R V, S ≤ L → deg ρ S ≤ muMax ρ L * rk ρ S := (hmaxL _).1 le_rfl
  constructor
  · intro hbot
    by_contra hcon
    push Not at hcon

    have hNL : N ≤ L := hNsat.1
    obtain ⟨-, hminN, -, -, -⟩ := muChar R V E ρ N (hsub N hNL) hN0
    have hrkpos : (0 : ℝ) < rk ρ N := by
      have : rk ρ N ≠ 0 := fun h => hN0 ((hrk0 N hNL).1 h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hdegN : deg ρ N = muMax ρ L * rk ρ N := by
      have e : slope ρ N = deg ρ N / rk ρ N := rfl
      rw [e, div_eq_iff hrkpos.ne'] at hNslope
      exact hNslope
    have hmm : muMax ρ L ≤ muMin ρ N := (hminN _).2 fun S hS => by
      have := hdegL S (hS.trans hNL)
      rw [mul_sub, ← hdegN]
      linarith
    have hle := hcont N hNL hN0 (hcon.trans hmm)
    rw [hbot] at hle
    exact hN0 (le_bot_iff.mp hle)
  · intro hlt
    by_contra hne
    have hH := hmin hne
    have hHL : hnStep ρ L θ ≤ L := hsat.1
    obtain ⟨hmaxH, -, -, hm1, hm2⟩ := muChar R V E ρ _ (hsub _ hHL) hne
    have : muMax ρ (hnStep ρ L θ) ≤ muMax ρ L :=
      (hmaxH _).2 fun S hS => hdegL S (hS.trans hHL)
    linarith

end Abstract

theorem exp_le_iff {c m t : ℝ} (ht : 0 < t) : Real.exp (c - m) ≤ t ↔ c - Real.log t ≤ m := by
  rw [← Real.le_log_iff_exp_le ht]
  constructor <;> intro h <;> linarith

theorem exp_lt_iff {c m t : ℝ} (ht : 0 < t) : Real.exp (c - m) < t ↔ c - Real.log t < m := by
  rw [← Real.lt_log_iff_exp_lt ht]
  constructor <;> intro h <;> linarith

theorem steps : ∀ (I : AutInst) (x : I.GA) (t : ℝ), 0 < t → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLe I x t) ∧ IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLt I x t) ∧ stepLt I x t ≤ stepLe I x t ∧ (∀ t', t < t' → stepLe I x t ≤ stepLt I x t') ∧ (stepLe I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLe I x t) ≤ t) ∧ (stepLt I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLt I x t) < t) ∧ (∀ N, stepLe I x t < N → N ≤ lamX I x → t < sizeQ (bas I) (frm I x) N (stepLe I x t)) ∧ (∀ N, stepLt I x t < N → N ≤ lamX I x → t ≤ sizeQ (bas I) (frm I x) N (stepLt I x t)) ∧ (1 ≤ I.n → 0 < least I x ∧ (stepLe I x t = ⊥ ↔ t < least I x) ∧ (stepLt I x t = ⊥ ↔ t ≤ least I x)) := by
  intro I x t ht
  obtain ⟨-, hfg, hspan, -, -⟩ := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
  obtain ⟨hTC, -, -, -, hw⟩ := GlobalTheory.T.autPointMajorantFrames_give_majorants I x
  have := hTC
  have hdet : ∀ w, IsUnit (frm I x w).det := fun w => (hw w).1
  set ρ := Formalism.HermitianLatticesTheory.realize (bas I) (frm I x) with hρ
  set L := lamX I x with hLdef
  have hLlat : IsLat ρ L := (plLat _ _ _ (bas I) (frm I x) hdet L hfg).1
  have : IsNoetherian (𝓞 I.E) L := isNoetherian_of_fg_of_noetherian L hfg
  have hNfg : ∀ N, N ≤ L → N.FG := fun N hN => Submodule.FG.of_le_of_isNoetherian hN
  set c : ℝ := Real.log 2 / 2 - logDisc I.E / (2 * (Module.finrank ℚ I.E : ℝ)) with hc

  have hlarge : ∀ N, N ≤ L → N ≠ ⊥ →
      largestSize (bas I) (frm I x) N = Real.exp (c - muMin ρ N) := fun N hN h0 =>
    (sizeMu _ _ _ (bas I) (frm I x) hdet N (hNfg N hN) h0).2.2.2.2.1
  have hsq : ∀ N S, N ≤ L → N ≠ ⊥ → IsSat ρ N S → S ≠ N →
      sizeQ (bas I) (frm I x) N S = Real.exp (c - Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ S))) :=
    fun N S hN h0 hS hne => (sizeMu _ _ _ (bas I) (frm I x) hdet N (hNfg N hN) h0).2.2.1 S hS hne
  set θ := c - Real.log t with hθ

  have hLe : stepLe I x t = hnStep ρ L θ := by
    unfold stepLe hnStep
    refine congrArg sSup (Set.ext fun N => ?_)
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hN, h0, hs⟩
      rw [hlarge N hN h0] at hs
      exact ⟨hN, h0, (exp_le_iff ht).1 hs⟩
    · rintro ⟨hN, h0, hs⟩
      refine ⟨hN, h0, ?_⟩
      rw [hlarge N hN h0]
      exact (exp_le_iff ht).2 hs
  have hLt : stepLt I x t = sSup {N : Submodule (𝓞 I.E) (Fin I.n → I.E) |
      N ≤ L ∧ N ≠ ⊥ ∧ θ < muMin ρ N} := by
    unfold stepLt
    refine congrArg sSup (Set.ext fun N => ?_)
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hN, h0, hs⟩
      rw [hlarge N hN h0] at hs
      exact ⟨hN, h0, (exp_lt_iff ht).1 hs⟩
    · rintro ⟨hN, h0, hs⟩
      refine ⟨hN, h0, ?_⟩
      rw [hlarge N hN h0]
      exact (exp_lt_iff ht).2 hs
  obtain ⟨θ₀, hθ₀, hstrict⟩ := strict_eq hLlat θ
  have hLt' : stepLt I x t = hnStep ρ L θ₀ := hLt.trans (hstrict θ₀ hθ₀ le_rfl)
  have hsame : ∀ θ', θ < θ' → θ' ≤ θ₀ → hnStep ρ L θ' = hnStep ρ L θ₀ := fun θ' h1 h2 =>
    (hstrict θ' h1 h2).symm.trans (hstrict θ₀ hθ₀ le_rfl)
  have hspec := hnStep_spec _ _ _ ρ L hLlat θ
  have hspec₀ := hnStep_spec _ _ _ ρ L hLlat θ₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLe]; exact hspec.1
  · rw [hLt']; exact hspec₀.1
  · unfold stepLt stepLe
    exact sSup_le_sSup fun N hN => ⟨hN.1, hN.2.1, hN.2.2.le⟩
  · intro t' htt'
    unfold stepLe stepLt
    exact sSup_le_sSup fun N hN => ⟨hN.1, hN.2.1, hN.2.2.trans_lt htt'⟩
  · intro h0
    rw [hLe] at h0 ⊢
    rw [hlarge _ hspec.1.1 h0]
    exact (exp_le_iff ht).2 (hspec.2.1 h0)
  · intro h0
    rw [hLt'] at h0 ⊢
    rw [hlarge _ hspec₀.1.1 h0]
    exact (exp_lt_iff ht).2 (lt_of_lt_of_le hθ₀ (hspec₀.2.1 h0))
  · intro N h1 h2
    rw [hLe] at h1 ⊢
    rw [hsq N _ h2 (ne_bot_of_gt h1) (isSat_of_le hspec.1 h1.le h2) h1.ne]
    have hs := quot_slope_lt hLlat θ h1 h2
    exact (Real.log_lt_iff_lt_exp ht).1 (by linarith)
  · intro N h1 h2
    rw [hLt'] at h1 ⊢
    rw [hsq N _ h2 (ne_bot_of_gt h1) (isSat_of_le hspec₀.1 h1.le h2) h1.ne]

    have key : ∀ θ', θ < θ' → θ' ≤ θ₀ →
        Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ (hnStep ρ L θ₀))) < θ' := fun θ' h1' h2' => by
      have e := hsame θ' h1' h2'
      have := quot_slope_lt hLlat θ' (by rw [e]; exact h1) h2
      rwa [e] at this
    generalize Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ (hnStep ρ L θ₀))) = s at key ⊢
    have hs : s ≤ θ := by
      by_contra hcon
      push Not at hcon
      have := key (min s θ₀) (lt_min hcon hθ₀) (min_le_right _ _)
      exact lt_irrefl _ (this.trans_le (min_le_left _ _))
    exact (Real.log_le_iff_le_exp ht).1 (by linarith)
  · intro hn
    have hL0 : L ≠ ⊥ := by
      intro h
      have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
      have htop : (⊤ : Submodule I.E (Fin I.n → I.E)) = ⊥ := by
        rw [← hspan, h]
        simp
      exact top_ne_bot htop
    have hleast : least I x = Real.exp (c - muMax ρ L) := by
      unfold least
      exact (sizeMu _ _ _ (bas I) (frm I x) hdet L hfg hL0).2.2.2.1
    refine ⟨by rw [hleast]; exact Real.exp_pos _, ?_, ?_⟩
    · rw [hLe, step_eq_bot hLlat hL0, hleast, ← Real.log_lt_iff_lt_exp ht]
      constructor <;> intro h <;> linarith
    · rw [hLt', hleast, ← Real.log_le_iff_le_exp ht]
      constructor
      · intro hb
        by_contra hcon
        push Not at hcon
        have h1 : θ < muMax ρ L := by linarith
        have hm : muMax ρ L < θ₀ := (step_eq_bot hLlat hL0 θ₀).1 hb
        have := (step_eq_bot hLlat hL0 _).1 ((hsame _ h1 hm.le).trans hb)
        exact lt_irrefl _ this
      · intro h
        exact (step_eq_bot hLlat hL0 θ₀).2 (by linarith)

end GlobalTheory.CountSteps
