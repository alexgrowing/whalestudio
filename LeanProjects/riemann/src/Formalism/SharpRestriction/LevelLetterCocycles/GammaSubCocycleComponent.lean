import Formalism.SharpRestriction.LevelLetterCocycles.InvariantLetterIdempotentOfFixed

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2I

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Core

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (s₁ σ : ℕ) (yv zv : W.DD T)
  (ms t : ZMod n → W.DD T)

def gammaDefectOfLetterLift (c : ZMod n) : W.DD T :=
  ((PD.p : ℕ) : O) ^ s₁ • ((letE c : LetA O n) • zv) + (W.γ T (ms c) - ms c)

def liftCorrection (c : ZMod n) : W.DD T :=
  ((PD.p : ℕ) : O) ^ σ • W.φD T (ms c) +
    ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 1) : LetA O n) • yv) - t c

def gammaDefectOfLiftCorrection (c : ZMod n) : W.DD T :=
  ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 1) : LetA O n) • zv) +
    (W.γ T (liftCorrection W T s₁ σ yv ms t c) - liftCorrection W T s₁ σ yv ms t c)

def frobeniusShiftDefectOfLiftCorrection (c : ZMod n) : W.DD T :=
  W.φD T (liftCorrection W T s₁ σ yv ms t (c - 2)) +
    ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE c : LetA O n) • yv) - ((PD.p : ℕ) : O) ^ σ • ms c

def frobeniusSquareDefectOfLiftCorrection (c : ZMod n) : W.DD T :=
  ((PD.p : ℕ) : O) ^ (s₁ + σ) •
      ((letE (c + 1) : LetA O n) • yv + W.φD T ((letE c : LetA O n) • yv)) +
    W.φD T (W.φD T (liftCorrection W T s₁ σ yv ms t (c - 2))) - liftCorrection W T s₁ σ yv ms t c

def liftCorrectionSum [NeZero n] (d : ℕ) : W.DD T :=
  ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d, (liftCorrection W T s₁ σ yv ms t c +
    ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 2) : LetA O n) • yv) +
      W.φD T (liftCorrection W T s₁ σ yv ms t c))

variable {W T s₁ σ yv zv}

theorem cocycle_relation_on_letter (hcoc : W.γ T yv - yv = W.φD T zv - zv) (i : ZMod n) :
    (letE (i + 1) : LetA O n) • W.γ T yv = (letE (i + 1) : LetA O n) • yv +
      W.φD T ((letE i : LetA O n) • zv) - (letE (i + 1) : LetA O n) • zv := by
  have h := congrArg (fun x => (letE (i + 1) : LetA O n) • x) hcoc
  simp only [smul_sub] at h
  rw [sub_eq_iff_eq_add] at h
  rw [frobenius_letter_shift, h]
  abel

theorem cocycleXi_eq (hcoc : W.γ T yv - yv = W.φD T zv - zv) (c : ZMod n) :
    gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t c = ((PD.p : ℕ) : O) ^ σ • W.φD T (gammaDefectOfLetterLift W T s₁ zv ms c) -
      (W.γ T (t c) - t c) := by
  have hc := cocycle_relation_on_letter (W := W) (T := T) hcoc c
  unfold gammaDefectOfLiftCorrection liftCorrection gammaDefectOfLetterLift
  simp only [map_add, map_sub, map_smul, gamma_letter_smul, gamma_frobenius_comm, hc]
  simp only [smul_add, smul_sub, smul_smul, ← pow_add, add_comm σ s₁]
  abel

theorem gamma_sub_cocycleW (hcoc : W.γ T yv - yv = W.φD T zv - zv) (c : ZMod n) :
    W.γ T (frobeniusShiftDefectOfLiftCorrection W T s₁ σ yv ms t c) - frobeniusShiftDefectOfLiftCorrection W T s₁ σ yv ms t c =
      W.φD T (gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t (c - 2)) -
        ((PD.p : ℕ) : O) ^ σ • gammaDefectOfLetterLift W T s₁ zv ms c := by
  have hc := cocycle_relation_on_letter (W := W) (T := T) hcoc (c - 1)
  rw [sub_add_cancel] at hc
  have hl : W.φD T ((letE (c - 2 + 1) : LetA O n) • zv) = (letE c : LetA O n) • W.φD T zv := by
    rw [frobenius_letter_shift, show c - 2 + 1 + 1 = c by ring]
  have hl' : W.φD T ((letE (c - 1) : LetA O n) • zv) = (letE c : LetA O n) • W.φD T zv := by
    rw [frobenius_letter_shift, sub_add_cancel]
  unfold frobeniusShiftDefectOfLiftCorrection gammaDefectOfLiftCorrection gammaDefectOfLetterLift
  simp only [map_add, map_sub, map_smul, gamma_letter_smul, gamma_frobenius_comm, hc, hl, hl']
  simp only [smul_add, smul_sub, smul_smul, ← pow_add, add_comm σ s₁]
  abel

theorem cocycleY_eq_frobenius_add (c : ZMod n) :
    frobeniusSquareDefectOfLiftCorrection W T s₁ σ yv ms t c = W.φD T (frobeniusShiftDefectOfLiftCorrection W T s₁ σ yv ms t c) + t c := by
  unfold frobeniusSquareDefectOfLiftCorrection frobeniusShiftDefectOfLiftCorrection liftCorrection
  simp only [map_add, map_sub, map_smul, smul_add]
  abel

theorem gamma_sub_cocycle_component (hcoc : W.γ T yv - yv = W.φD T zv - zv) (c : ZMod n) :
    W.γ T (frobeniusSquareDefectOfLiftCorrection W T s₁ σ yv ms t c) - frobeniusSquareDefectOfLiftCorrection W T s₁ σ yv ms t c =
      W.φD T (W.φD T (gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t (c - 2))) - gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t c := by
  rw [cocycleY_eq_frobenius_add, cocycleXi_eq ms t hcoc c]
  have h := congrArg (W.φD T) (gamma_sub_cocycleW (s₁ := s₁) (σ := σ) (ms := ms) (t := t) hcoc c)
  simp only [map_add, map_sub, map_smul, gamma_frobenius_comm] at h ⊢
  rw [show ∀ a b e : W.DD T, a - (b - e) = (a - b) + e from fun a b e => by abel, ← h]
  abel

theorem first_component_sum_eq [NeZero n] (hn : Even n) (d : ℕ) :
    ((PD.p : ℕ) : O) ^ (s₁ + σ) • yv +
        (W.φD T (liftCorrectionSum W T s₁ σ yv ms t d) - liftCorrectionSum W T s₁ σ yv ms t d) =
      ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d, frobeniusSquareDefectOfLiftCorrection W T s₁ σ yv ms t c := by
  have hy : yv = ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
      ((letE (c + 1) : LetA O n) • yv + (letE (c + 2) : LetA O n) • yv) := by
    conv_lhs => rw [← sum_letter_idempotents_smul W T yv]
    exact sum_eq_sum_evens_pairs hn d (fun i => (letE i : LetA O n) • yv)
  have key : ((PD.p : ℕ) : O) ^ (s₁ + σ) • yv = ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
      (((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 1) : LetA O n) • yv) +
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 2) : LetA O n) • yv)) := by
    conv_lhs => rw [hy]
    rw [Finset.smul_sum]
    simp only [smul_add]
  have h2 : ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
      W.φD T (W.φD T (liftCorrection W T s₁ σ yv ms t (c - 2))) =
      ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d, W.φD T (W.φD T (liftCorrection W T s₁ σ yv ms t c)) :=
    sum_evens_shift_sub_two hn d (fun c => W.φD T (W.φD T (liftCorrection W T s₁ σ yv ms t c)))
  have h3 : ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
      ((PD.p : ℕ) : O) ^ (s₁ + σ) • W.φD T ((letE c : LetA O n) • yv) =
      ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • W.φD T ((letE (c + 2) : LetA O n) • yv) :=
    (sum_evens_shift_add_two hn d (fun c => ((PD.p : ℕ) : O) ^ (s₁ + σ) • W.φD T ((letE c : LetA O n) • yv))).symm
  have eY : ∀ c, frobeniusSquareDefectOfLiftCorrection W T s₁ σ yv ms t c =
      ((PD.p : ℕ) : O) ^ (s₁ + σ) • ((letE (c + 1) : LetA O n) • yv) +
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • W.φD T ((letE c : LetA O n) • yv) +
        W.φD T (W.φD T (liftCorrection W T s₁ σ yv ms t (c - 2))) - liftCorrection W T s₁ σ yv ms t c := by
    intro c; unfold frobeniusSquareDefectOfLiftCorrection; rw [smul_add]
  rw [Finset.sum_congr rfl (fun c _ => eY c)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h2, h3, key]
  unfold liftCorrectionSum
  rw [map_sum]
  simp only [map_add, map_smul, Finset.sum_add_distrib]
  abel

theorem second_component_sum_eq [NeZero n] (hn : Even n) (d : ℕ) (hcoc : W.γ T yv - yv = W.φD T zv - zv) :
    ((PD.p : ℕ) : O) ^ (s₁ + σ) • zv +
        (W.γ T (liftCorrectionSum W T s₁ σ yv ms t d) - liftCorrectionSum W T s₁ σ yv ms t d) =
      ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
        (gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t c + W.φD T (gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t c)) := by
  have hz : zv = ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
      ((letE (c + 1) : LetA O n) • zv + (letE (c + 2) : LetA O n) • zv) := by
    conv_lhs => rw [← sum_letter_idempotents_smul W T zv]
    exact sum_eq_sum_evens_pairs hn d (fun i => (letE i : LetA O n) • zv)
  have hc : ∀ c : ZMod n, (letE (c + 2) : LetA O n) • W.γ T yv = (letE (c + 2) : LetA O n) • yv +
      W.φD T ((letE (c + 1) : LetA O n) • zv) - (letE (c + 2) : LetA O n) • zv := by
    intro c
    have := cocycle_relation_on_letter (W := W) (T := T) hcoc (c + 1)
    rwa [show c + 1 + 1 = c + 2 by ring] at this
  unfold gammaDefectOfLiftCorrection liftCorrectionSum
  rw [map_sum, ← Finset.sum_sub_distrib]
  conv_lhs => rw [hz]
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [map_add, map_sub, map_smul, gamma_letter_smul, gamma_frobenius_comm, hc, smul_add, smul_sub]
  abel

end Core

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2I

end
