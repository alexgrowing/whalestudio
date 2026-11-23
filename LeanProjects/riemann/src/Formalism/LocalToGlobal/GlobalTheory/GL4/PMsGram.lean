import Formalism.LocalToGlobal.GlobalTheory.GL4.PMsKey
import Formalism.GL3MeanSquares.HookFormulaTorsion.FibreCardinalityOfModuliMap

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Gram

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def meanAbs (z : E) : ℝ := (∑ φ : E →+* ℂ, ‖φ z‖) / (Module.finrank ℚ E : ℝ)

def ShortFrame (S : HSpace E) (q : ℕ) (ρ : ℝ) : Prop :=
  ∀ L : Submodule (𝓞 E) S.V, Submodule.IsLattice E L → LatT S q L →
    ∃ b : Module.Basis (Fin S.rank) E S.V, (∀ c, b c ∈ L) ∧ ∀ c, meanAbs (S.hT (b c) (b c)) ≤ ρ

def CSAt (S : HSpace E) : Prop :=
  ∀ (φ : E →+* ℂ) (x y : S.V), ‖φ (S.hT x y)‖ ^ 2 ≤ ‖φ (S.hT x x)‖ * ‖φ (S.hT y y)‖

def CoordCount (S : HSpace E) (q : ℕ) (ρ B2 : ℝ) : Prop :=
  ∃ C : Matrix (Fin S.rank) (Fin S.rank) E → Finset (Submodule (𝓞 E) (Fin S.rank → E)),
    (∀ G, ((C G).card : ℝ) ≤ Real.exp B2) ∧
    ∀ (L : Submodule (𝓞 E) S.V) (b : Module.Basis (Fin S.rank) E S.V), Submodule.IsLattice E L → LatT S q L →
      (∀ c, b c ∈ L) → (∀ c, meanAbs (S.hT (b c) (b c)) ≤ ρ) → (keyOf S b L).2 ∈ C (keyOf S b L).1

theorem meanAbs_entry (S : HSpace E) (hCS : CSAt S) {ρ : ℝ} {x y : S.V} (hx : meanAbs (S.hT x x) ≤ ρ)
    (hy : meanAbs (S.hT y y) ≤ ρ) : meanAbs (S.hT x y) ≤ ρ := by
  have hpt : ∀ φ : E →+* ℂ, ‖φ (S.hT x y)‖ ≤ (‖φ (S.hT x x)‖ + ‖φ (S.hT y y)‖) / 2 := by
    intro φ
    have h := hCS φ x y
    nlinarith [sq_nonneg (‖φ (S.hT x x)‖ - ‖φ (S.hT y y)‖), norm_nonneg (φ (S.hT x y)),
      norm_nonneg (φ (S.hT x x)), norm_nonneg (φ (S.hT y y))]
  unfold meanAbs at *
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  rw [div_le_iff₀ hd] at hx hy ⊢
  have hs := Finset.sum_le_sum fun φ (_ : φ ∈ (Finset.univ : Finset (E →+* ℂ))) => hpt φ
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hs
  linarith

theorem keyBound_of (S : HSpace E) (q : ℕ) (ρ B2 : ℝ) (hρ : 0 ≤ ρ) (hB2 : 0 ≤ B2)
    (hS : ShortFrame S q ρ) (hCS : CSAt S) (hC : CoordCount S q ρ B2) :
    KeyBound S q ((S.rank : ℝ) ^ 2 * (Module.finrank ℚ E : ℝ) * Real.log (2 * ρ + 1) + B2) := by
  classical
  obtain ⟨hfin, hcard⟩ := Formalism.HermitianLattices.ExplicitEstimates.mean_count_of_moduli_space E ρ hρ
  obtain ⟨C, hCc, hCm⟩ := hC
  set Z : Finset E := hfin.toFinset.image (fun x : 𝓞 E => (x : E)) with hZ
  have hZc : (Z.card : ℝ) ≤ (2 * ρ + 1) ^ Module.finrank ℚ E := by
    refine le_trans ?_ hcard
    have : Z.card ≤ hfin.toFinset.card := Finset.card_image_le
    rw [← Set.ncard_eq_toFinset_card _ hfin] at this
    exact_mod_cast this
  let G : Finset (Matrix (Fin S.rank) (Fin S.rank) E) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => Z
  have hGc : (G.card : ℝ) ≤ ((2 * ρ + 1) ^ Module.finrank ℚ E) ^ (S.rank * S.rank) := by
    have : G.card = (Z.card ^ S.rank) ^ S.rank := by
      show (Fintype.piFinset fun _ => Fintype.piFinset fun _ => Z : Finset (Fin S.rank → Fin S.rank → E)).card = _
      rw [Fintype.card_piFinset]
      simp [Fintype.card_piFinset, Finset.prod_const]
    rw [this, pow_mul]
    push_cast
    exact pow_le_pow_left₀ (pow_nonneg (by positivity) _) (pow_le_pow_left₀ (by positivity) hZc S.rank) S.rank
  let K := G.biUnion fun g => (C g).image fun c => (g, c)
  refine ⟨K, ?_, fun L hL hq => ?_⟩
  · have hK : (K.card : ℝ) ≤ G.card * Real.exp B2 := by
      have h1 : K.card ≤ ∑ g ∈ G, ((C g).image fun c => (g, c)).card := Finset.card_biUnion_le
      have h3 : K.card ≤ ∑ g ∈ G, (C g).card := h1.trans (Finset.sum_le_sum fun g _ => Finset.card_image_le)
      have h2 : (K.card : ℝ) ≤ ∑ g ∈ G, ((C g).card : ℝ) := by exact_mod_cast h3
      refine le_trans h2 ?_
      refine le_trans (Finset.sum_le_sum fun g _ => hCc g) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have hlog : 0 ≤ Real.log (2 * ρ + 1) := Real.log_nonneg (by linarith)
    rcases Nat.eq_zero_or_pos K.card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
    have hGpos : (0 : ℝ) < G.card := by
      have : (0 : ℝ) < G.card * Real.exp B2 := lt_of_lt_of_le (by exact_mod_cast h0) hK
      exact pos_of_mul_pos_left this (Real.exp_pos _).le
    calc Real.log K.card ≤ Real.log (G.card * Real.exp B2) := Real.log_le_log (by exact_mod_cast h0) hK
      _ = Real.log G.card + B2 := by rw [Real.log_mul hGpos.ne' (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ Real.log (((2 * ρ + 1) ^ Module.finrank ℚ E) ^ (S.rank * S.rank)) + B2 := by
          gcongr
      _ = (S.rank : ℝ) ^ 2 * (Module.finrank ℚ E : ℝ) * Real.log (2 * ρ + 1) + B2 := by
          rw [Real.log_pow, Real.log_pow]; push_cast; ring
  · obtain ⟨b, hbL, hbs⟩ := hS L hL hq
    refine ⟨b, Finset.mem_biUnion.2 ⟨(keyOf S b L).1, ?_, Finset.mem_image.2 ⟨(keyOf S b L).2,
      hCm L b hL hq hbL hbs, rfl⟩⟩⟩
    have key : ∀ i j, (keyOf S b L).1 i j ∈ Z := by
      intro i j
      have hmem := (mem_dualSub S L (b j)).1 (hq.1 _ (hbL j)) (b i) (hbL i)
      obtain ⟨z, hz⟩ := hmem
      have hzm : z ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        show meanAbs (z : E) ≤ ρ
        have : (z : E) = S.hT (b i) (b j) := hz
        rw [this]
        exact meanAbs_entry S hCS (hbs i) (hbs j)
      exact Finset.mem_image.2 ⟨z, hzm, hz⟩
    exact Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun j => key i j

end Gram

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
