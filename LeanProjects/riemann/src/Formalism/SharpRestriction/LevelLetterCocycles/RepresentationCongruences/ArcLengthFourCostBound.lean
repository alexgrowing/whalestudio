import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_four_cost_bound (l : ℕ) (hl : 11 ≤ l) (b wm w S η : ℕ) (hb : 1 ≤ b) (B : ℝ) (s si rr σ : ℕ)
    (hs : (s : ℝ) ≤ max 1 ((w : ℝ) - B / l + 16 / 5 * Sg l (b + η + S) wm S η) + 1)
    (hsi : (w : ℝ) - B / l - η / (l : ℝ) ^ 2 - 1 ≤ si)
    (hrr : (rr : ℝ) ≤ 3 * Sg l (b + η + S) wm S η) (hσ : (σ : ℝ) ≤ 3 * Sg l (b + η + S) wm S η) :
    ((rr + 3 * σ + 1 + (s - si) : ℕ) : ℝ) ≤ 18 * Sg l (b + η + S) wm S η + 1 := by
  have h4 := max_sub_le_errorScale l hl b wm w S η hb B ((s : ℝ) - 1) (si : ℝ)
    (max_le (Nat.cast_nonneg _) hsi) (by linarith)
  obtain ⟨-, -, -, -, -, -, h1⟩ := CaseA.sg_ge l (b + η + S) wm S η hl (by omega)
  have hsub : ((s - si : ℕ) : ℝ) ≤ max 0 ((s : ℝ) - 1 - si) + 1 := by
    rcases le_total si s with h | h
    · rw [Nat.cast_sub h]
      have := le_max_right (0:ℝ) ((s : ℝ) - 1 - si)
      linarith
    · rw [Nat.sub_eq_zero_of_le h]
      have := le_max_left (0:ℝ) ((s : ℝ) - 1 - si)
      simp only [Nat.cast_zero]
      linarith
  push_cast
  linarith

theorem sigma_eq_of_thick_letter {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (hT : ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) :
    Formalism.MainNotions.N.Ln17.Sg l b w S η size = Sg l (b + η + S) w S η := by
  unfold Formalism.MainNotions.N.Ln17.Sg Sg Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
  rw [if_pos hT]

namespace ArcLengthFourSecond

section EEh
variable {W : LocWach PD LL O v n}

theorem lE_eq (k : ℕ) : lE W k = algebraMap (LetA O n) W.EE (lA W ^ k) := by
  simp [lE, lA, map_pow, map_natCast]

theorem letE_mem (c : ZMod n) : (letE c : LetA O n) ∈ W.AΔ := fun δ _ => GS.γA_letE W δ c

theorem lA_mem : lA W ∈ W.AΔ := by
  exact natCast_mem _ _

theorem inFr_sub {a : ZMod n} {num den : LetA O n} {f g : W.EE} (hf : InFr W a num den f) (hg : InFr W a num den g) :
    InFr W a num den (f - g) := by
  obtain ⟨u, hu, hf⟩ := hf
  obtain ⟨u', hu', hg⟩ := hg
  refine ⟨u - u', sub_mem hu hu', ?_⟩
  rw [mul_sub, hf, hg, ← map_sub, mul_sub]

theorem inFr_lE {a : ZMod n} {num den : LetA O n} {f : W.EE} (k : ℕ) (hf : InFr W a num den f) :
    InFr W a num den (lE W k * f) := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨lA W ^ k * u, mul_mem (pow_mem lA_mem k) hu, ?_⟩
  rw [lE_eq, mul_left_comm, hf, ← map_mul]
  congr 1
  ring

theorem inFr_num_left {a : ZMod n} {n₁ n₂ den : LetA O n} {f : W.EE} (hf : InFr W a (n₁ * n₂) den f) (h₂ : n₂ ∈ W.AΔ) :
    InFr W a n₁ den f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨n₂ * u, mul_mem h₂ hu, ?_⟩
  rw [hf]
  congr 1
  ring

theorem inFr_num_right {a : ZMod n} {n₁ n₂ den : LetA O n} {f : W.EE} (hf : InFr W a (n₁ * n₂) den f) (h₁ : n₁ ∈ W.AΔ) :
    InFr W a n₂ den f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨n₁ * u, mul_mem h₁ hu, ?_⟩
  rw [hf]
  congr 1
  ring

theorem inFr_den_mul {a : ZMod n} {num d : LetA O n} (d' : LetA O n) {f : W.EE} (hf : InFr W a num d f) (hd' : d' ∈ W.AΔ) :
    InFr W a num (d' * d) f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨d' * u, mul_mem hd' hu, ?_⟩
  rw [map_mul, mul_assoc, hf, ← map_mul]
  congr 1
  ring

end EEh

end ArcLengthFourSecond

theorem ArcLengthFourSecond.inFr_sat [IsDomain O] [IsDiscreteValuationRing O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hinj : Function.Injective (algebraMap O LL)) {c : ZMod n} {num den : LetA O n}
    (hnum : num ∈ PiPs W) {g : W.EE} (h1 : InFr W c 1 den g) (hK : ∃ K : ℕ, InFr W c num den (lE W K * g)) :
    InFr W c num den g := by
  obtain ⟨u₀, hu₀, e₀⟩ := h1
  obtain ⟨K, u₁, hu₁, e₁⟩ := hK
  have key : lA W ^ K * (1 * (letE c * u₀)) = num * (letE c * u₁) := by
    apply W.EE_inj
    calc algebraMap (LetA O n) W.EE (lA W ^ K * (1 * (letE c * u₀)))
        = lE W K * algebraMap (LetA O n) W.EE (letE c * 1 * u₀) := by
          rw [ArcLengthFourSecond.lE_eq, ← map_mul]; congr 1; ring
      _ = algebraMap (LetA O n) W.EE den * (lE W K * g) := by rw [← e₀]; ring
      _ = _ := by rw [e₁]; congr 1; ring
  obtain ⟨y, hy, hxy⟩ := saturation_fraction_ring W hcase hP9 hinj num 1 1 hnum (one_mem _) (one_mem _) (letE c * u₀)
    (by rw [one_mul]; exact W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hu₀)
    ⟨K, letE c * u₁, W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hu₁, key⟩
  refine ⟨letE c * y, W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hy, ?_⟩
  rw [e₀]
  congr 1
  have hidem : (letE c : LetA O n) * letE c = letE c := by
    unfold letE; rw [← Pi.single_mul, one_mul]
  linear_combination (letE c : LetA O n) ^ 2 * hxy - (((letE c : LetA O n) + 1) * u₀) * hidem

end Formalism.MainNotions.N.FrobeniusPowerSeries
