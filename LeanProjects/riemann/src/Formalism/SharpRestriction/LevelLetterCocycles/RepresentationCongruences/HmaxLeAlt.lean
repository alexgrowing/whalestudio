import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.AKill

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem hmax_le [NeZero n] (Mi hi : ZMod n → ℕ) (j : ZMod n) :
    Mi j + hi j ≤ Formalism.MainNotions.LiftingTheory.Hmax n Mi hi := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax
  have h := Finset.le_sup (f := fun k : ℕ => Mi k + hi k) (Finset.mem_range.2 (ZMod.val_lt j))
  simp only [ZMod.natCast_zmod_val] at h
  exact h

theorem ai_le [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR) (a : ZMod n) :
    (Formalism.MainNotions.LiftingTheory.AI W F a : ℝ) ≤ ((size (a + 1) : ℝ) + S + η) / PD.p + 5 / 2 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
      (¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (a + 2) →
        (Formalism.MainNotions.LiftingTheory.AI W F a : ℝ) ≤ ((size (a + 1) : ℝ) + S + η) / PD.p + 2 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size) := by
  obtain ⟨hp11, hSet, hwb, hηb, hSb, ⟨j, hj⟩⟩ := hB
  obtain ⟨hcase, hSur, hηs, hJA, _hlow, hnt, _hJL⟩ := hSet
  set h := Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size with hhdef
  have hF : (∀ i, size i + S ≤ h) ∧ w + S ≤ h := by
    rw [hhdef]
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
    split_ifs with hex
    · refine ⟨fun i => ?_, by omega⟩
      by_cases ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i
      · have := ht.2; omega
      · have := hnt i ht; omega
    · push Not at hex
      exact ⟨fun i => by have := hnt i (hex i); omega, le_rfl⟩
  have hη1 : η + 1 ≤ h := by
    have := hnt j hj
    have := hηs j
    have := hF.2
    omega
  let Mi' : ZMod n → ℕ := fun i => if up i then η else size i + S
  let hi' : ZMod n → ℕ := fun i => if up i then size i + S else η
  have hbox : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi' hi' := by
    intro i τ hτ x hx
    have h1 := hJA i τ hτ x hx
    have h2 := hηs i
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hHbox : ∀ i, Mi' i + hi' i ≤ h + η := by
    intro i
    have := hF.1 i
    cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hbx : ∀ i, Mi' i + hi' i = size i + S + η := by
    intro i
    cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  obtain ⟨hs, -⟩ := hWR hcase T₁ T₂ F Mi' hi' hSur hbox a
  set H := Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' with hHdef
  have hHle : H ≤ h + η := Finset.sup_le fun k _ => hHbox _
  have hcW : (Formalism.MainNotions.LiftingTheory.cH PD.p H : ℝ) = (cW PD.p H : ℝ) := rfl
  have hx : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hA : (Formalism.MainNotions.LiftingTheory.AI W F a : ℝ) ≤ (Formalism.MainNotions.LiftingTheory.sI W F a : ℝ) / ((PD.p : ℝ) - 1) + 1 := by
    unfold Formalism.MainNotions.LiftingTheory.AI
    have h0 : 0 ≤ (Formalism.MainNotions.LiftingTheory.sI W F a : ℝ) / ((PD.p : ℝ) - 1) :=
      div_nonneg (Nat.cast_nonneg _) (by linarith)
    exact (Nat.ceil_lt_add_one h0).le
  have hH₁ : Mi' (a + 1) + hi' (a + 1) ≤ h + η := hHbox _
  have hH₁r : ((Mi' (a + 1) + hi' (a + 1) : ℕ) : ℝ) = (size (a + 1) : ℝ) + S + η := by
    rw [hbx]; push_cast; ring
  have eSg : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p h w S η := rfl
  let fx : ℕ → ℝ := fun x => ((Mi' (a + ((x + 1 : ℕ) : ZMod n)) + hi' (a + ((x + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) +
      Formalism.MainNotions.LiftingTheory.cH PD.p H + 3
  have hf0 : ∀ x, 0 ≤ fx x := fun x => by positivity
  have hfH : ∀ x, fx x ≤ (H : ℝ) + cW PD.p H + 3 := by
    intro x
    have := hmax_le Mi' hi' (a + ((x + 1 : ℕ) : ZMod n))
    have h' : (((Mi' (a + ((x + 1 : ℕ) : ZMod n)) + hi' (a + ((x + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)) ≤ H := by
      exact_mod_cast this
    show _ + _ + _ ≤ _
    rw [hcW]; linarith
  have hf0' : fx 0 ≤ ((Mi' (a + 1) + hi' (a + 1) : ℕ) : ℝ) + cW PD.p H + 3 := by
    simp [fx, hcW]
  refine ⟨?_, fun hnt2 => ?_⟩
  · have ht := tsum_three PD.p hp11 fx _ ((H : ℝ) + cW PD.p H + 3) ((H : ℝ) + cW PD.p H + 3) hf0 hf0'
      (hfH 1) (fun x _ => hfH x)
    have hst := hs.trans ht
    have hs' : (Formalism.MainNotions.LiftingTheory.sI W F a : ℝ) ≤ (((Mi' (a + 1) + hi' (a + 1) : ℕ) : ℝ) + cW PD.p H + 3) +
        ((H : ℝ) + cW PD.p H + 3) / ((PD.p : ℝ) - 2) := by
      have h1 : (PD.p : ℝ) - 1 ≠ 0 := by intro h; linarith
      have h2 : (PD.p : ℝ) - 2 ≠ 0 := by intro h; linarith
      have e : ∀ X : ℝ, X / ((PD.p : ℝ) - 1) + X / (((PD.p : ℝ) - 1) * ((PD.p : ℝ) - 2)) =
          X / ((PD.p : ℝ) - 2) := by
        intro X; field_simp; ring
      linarith [e ((H : ℝ) + cW PD.p H + 3)]
    have := Aa_le PD.p hp11 h w S η H (Mi' (a + 1) + hi' (a + 1)) hη1 hHle hH₁ _ _ hs' hA
    rw [hH₁r] at this
    rw [eSg]; exact this
  · have hH₂ : Mi' (a + 2) + hi' (a + 2) ≤ w + S + η := by
      have := hnt (a + 2) hnt2
      rw [hbx]; omega
    have hf1 : fx 1 ≤ ((Mi' (a + 2) + hi' (a + 2) : ℕ) : ℝ) + cW PD.p H + 3 := by
      have e2 : a + ((1 + 1 : ℕ) : ZMod n) = a + 2 := by push_cast; ring
      simp only [fx, e2, hcW]; exact le_rfl
    have ht := tsum_three PD.p hp11 fx _ _ ((H : ℝ) + cW PD.p H + 3) hf0 hf0' hf1 (fun x _ => hfH x)
    have hst := hs.trans ht
    have := Aa_cut_le PD.p hp11 h w S η H (Mi' (a + 1) + hi' (a + 1)) (Mi' (a + 2) + hi' (a + 2)) hη1 hHle
      hH₁ hH₂ _ _ hst hA
    rw [hH₁r] at this
    rw [eSg]; exact this

end Formalism.MainNotions.N.FrobeniusPowerSeries.AKill
