import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformHeckeRelationsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinMeanSquareCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootsNormLeOfBoundedTwoStepRecurrenceStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.FactorsAtL

theorem norm_one_of_pow {R : Type*} [NormedDivisionRing R] {z : R} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    ‖z‖ = 1 := by
  have : ‖z‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 this

theorem char_inv_facts {N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ N) (l : ℕ) (hl : l.Coprime N) :
    (χ⁻¹ (l : ZMod N)) ^ N.totient = 1 ∧ χ⁻¹ (l : ZMod N) * χ (l : ZMod N) = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hu : IsUnit (l : ZMod N) := (ZMod.isUnit_iff_coprime l N).2 hl
  constructor
  · obtain ⟨v, hv⟩ := hu
    rw [← hv, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
  · rw [show χ⁻¹ (l : ZMod N) * χ (l : ZMod N) = (χ⁻¹ * χ) (l : ZMod N) from rfl, MulChar.inv_mul, MulChar.one_apply hu]

theorem norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]

end GlobalTheory.FactorsAtL

namespace GlobalTheory.FactorsAtL

theorem factors_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ : DirichletCharacter ℂ N)
    (g : ℕ → ℂ) (α β ζ : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l →
    α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) →
    α ≠ ζ ∧ β ≠ l * ζ ∧ ∀ j : ℕ, 1 ≤ j → α ≠ (l : ℂ) ^ j * ζ := by
  intro l _ ι e N χ g α β ζ he hN hlN hP hs hp hα ⟨n, hn, hζ⟩
  have hlp : l.Prime := Fact.out
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
  obtain ⟨hut, huc⟩ := char_inv_facts hN χ l hcop
  have htot : 0 < N.totient := Nat.totient_pos.2 hN
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hinv0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 hl0
  have hinv1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hnl : ‖ι.symm (l : ℂ)‖ = (l : ℝ)⁻¹ := by rw [map_natCast]; exact norm_natCast_self l
  have hnζ : ‖ι.symm ζ‖ = 1 := norm_one_of_pow hn (by rw [← map_pow, hζ, map_one])
  have hnu : ‖ι.symm (χ⁻¹ (l : ZMod N))‖ = 1 := norm_one_of_pow htot (by rw [← map_pow, hut, map_one])
  refine ⟨?_, ?_, ?_⟩
  · intro hαζ
    have hcα : ‖α‖ = 1 := by rw [hαζ]; exact Complex.norm_eq_one_of_pow_eq_one hζ hn.ne'
    have hcu : ‖χ⁻¹ (l : ZMod N)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hut htot.ne'
    have hβn : ‖β‖ = (l : ℝ) ^ (2 * e) := by
      have h := congrArg norm hp
      rw [norm_mul, norm_mul, hcα, hcu, norm_pow, Complex.norm_natCast, one_mul, one_mul] at h
      exact h
    obtain ⟨_, hrec, _⟩ := GlobalTheory.T.depletedCuspEigenform_heckeRelations (2 * e + 1) N χ g (by omega) hN hP
    obtain ⟨_, ⟨C, hC⟩, _⟩ := GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) N (ch χ) g (by omega) hP.cf
    set u := χ⁻¹ (l : ZMod N) with hu_def
    let c : ℕ → ℂ := fun r => u ^ r * g (l ^ r)
    have hc0 : c 0 = 1 := by simp [c, hP.one]
    have hc1 : c 1 = α + β := by simp [c, hs]
    have hcr : ∀ r, c (r + 2) = (α + β) * c (r + 1) - α * β * c r := by
      intro r
      simp only [c]
      rw [hrec l r hlp hlN, hs, hp, show 2 * e + 1 - 1 = 2 * e by omega]
      have key : u ^ (r + 2) * χ (l : ZMod N) = u ^ (r + 1) := by rw [pow_succ, mul_assoc, huc, mul_one]
      linear_combination (-(l : ℂ) ^ (2 * e) * g (l ^ r)) * key
    set s := Real.sqrt l with hs_def
    have hs2 : s ^ 2 = l := Real.sq_sqrt hl0.le
    have hs1 : 1 < s := by rw [hs_def]; exact Real.lt_sqrt (by norm_num) |>.2 (by simpa using hl1)
    set R := s ^ (2 * e + 1) with hR
    have hR0 : 0 ≤ R := by positivity
    have hbound : ∀ r, ‖c r‖ ≤ Real.sqrt (max C 0) * R ^ r := by
      intro r
      have h1 : ‖c r‖ = ‖g (l ^ r)‖ := by
        simp only [c]; rw [norm_mul, norm_pow, hcu, one_pow, one_mul]
      have hX : ((l ^ r : ℕ) : ℝ) ^ (2 * e + 1) = (R ^ r) ^ 2 := by
        push_cast; rw [hR, ← hs2]; ring
      have h2 : ‖g (l ^ r)‖ ^ 2 ≤ max C 0 * (R ^ r) ^ 2 := by
        rw [← hX]; exact (hC _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      rw [h1, ← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (pow_nonneg hR0 r), ← Real.sqrt_mul (le_max_right _ _)]
      exact Real.sqrt_le_sqrt h2
    obtain ⟨_, hβR⟩ := GlobalTheory.T.roots_norm_le_of_bounded_two_step_recurrence α β c (Real.sqrt (max C 0)) R hR0 hc0 hc1 hcr hbound
    rw [hβn, ← hs2, ← pow_mul, hR] at hβR
    have : s ^ (2 * e + 1) < s ^ (2 * (2 * e)) := pow_lt_pow_right₀ hs1 (by omega)
    linarith
  · intro hβζ
    have h := congrArg (fun z => ‖ι.symm z‖) hp
    simp only [map_mul, map_pow, norm_mul, norm_pow] at h
    rw [hα, hnu, hnl, one_mul, one_mul, hβζ, map_mul, norm_mul, hnl, hnζ, mul_one] at h
    have : ((l : ℝ)⁻¹) ^ (2 * e) < ((l : ℝ)⁻¹) ^ 1 := pow_lt_pow_right_of_lt_one₀ hinv0 hinv1 (by omega)
    rw [pow_one] at this
    linarith
  · intro j hj hαj
    rw [hαj, map_mul, map_pow, norm_mul, norm_pow, hnl, hnζ, mul_one] at hα
    have : ((l : ℝ)⁻¹) ^ j < 1 := pow_lt_one₀ hinv0.le hinv1 (by omega)
    linarith

end GlobalTheory.FactorsAtL
