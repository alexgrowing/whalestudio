import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AverageEmbeddingsFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetBoundLogAverageLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBaseChangeLineDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineDegreeLowerBoundStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.MatrixArithmetic.WeakMatSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory.LieSlopeProof

theorem sum_range_cast_id (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (i : ℝ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

noncomputable def cJ (g : ℕ) : ℝ := (Real.log (4 / Real.pi) + Real.log (15 + 14 * Real.log (Nat.factorial g))) / 2

theorem cJ_nonneg (g : ℕ) : 0 ≤ cJ g := by
  unfold cJ
  have h1 : 0 ≤ Real.log (4 / Real.pi) := Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_le_four])
  have h2 : 0 ≤ Real.log (Nat.factorial g : ℝ) := Real.log_natCast_nonneg _
  have h3 : 0 ≤ Real.log (15 + 14 * Real.log (Nat.factorial g)) := Real.log_nonneg (by linarith)
  positivity

theorem jetBd_pos (g n i : ℕ) (ρ : ℝ) (hn : 0 < n) (hρ : 0 < ρ) : 0 < jetBd g n i ρ := by
  unfold jetBd
  have ha : 0 < √(Real.exp 1 * n * i) ^ i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · exact pow_pos (Real.sqrt_pos.2 (by positivity)) _
  have hb : 0 < √(Real.exp 1 * (g.factorial : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hc : 0 < √(n : ℝ) ^ g := pow_pos (Real.sqrt_pos.2 (by exact_mod_cast hn)) _
  exact mul_pos (mul_pos ha hb) (lt_of_lt_of_le hc (le_max_right _ _))

theorem line_bound (hM : GlobalTheory.Published.MatrixLemma) (hJ : SecJets4) (g' : ℕ) : ∃ C : ℝ,
    ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g = g' → 0 < F.P₀.g → ∀ h, F.IsHerm h →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (h' : HermFam K' (Fin F.P₀.g → K'))
      (x : Fin F.P₀.g → K'), IsBC h h' → x ≠ 0 →
      deg h' (lineLat (latBC K' F.lieLat) x) ≤ Real.log (2 + max (F.falt h) 0) + C := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.log_height_bound_from_inequality g' (cJ g') (cJ_nonneg g')
  refine ⟨C, ?_⟩
  intro K _ _ F hg hgpos h hh K' _ _ _ h' x hbc hx
  subst hg
  obtain ⟨hfull, -, -, hρex⟩ := GlobalTheory.T.semi_fibration_lie_lattice_full K F
  obtain ⟨ρ, hρ, hρpos⟩ := hρex hgpos
  have hMat := hM K F h ρ hh hρ
  set H := max (F.falt h) 0 with hH
  have hH0 : 0 ≤ H := le_max_right _ _
  have hlg : 0 ≤ Real.log (F.P₀.g.factorial : ℝ) := Real.log_natCast_nonneg _
  have hMat' : (∑ σ, (ρ σ ^ 2)⁻¹) / (Module.finrank ℚ K : ℝ) ≤ 14 * (1 + H + Real.log (Nat.factorial F.P₀.g)) := by
    refine hMat.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    have hx1 : F.falt h - (F.P₀.g : ℝ) / 2 * Real.log Real.pi ≤ H := by
      have : 0 ≤ (F.P₀.g : ℝ) / 2 * Real.log Real.pi :=
        mul_nonneg (by positivity) (Real.log_nonneg (by linarith [Real.pi_gt_three]))
      linarith [le_max_left (F.falt h) 0]
    refine max_le (by linarith) (max_le (by linarith) (by linarith))
  apply hC H _ hH0
  intro n' hn2 _
  obtain ⟨K'', _, _, _, _, _, h'', hbc'', hjet⟩ := hJ K F h ρ hh hρ K' x hx n' hn2
  obtain ⟨hfull'', hline⟩ := GlobalTheory.T.lattice_base_change_line_degree K K' K'' F.P₀.g h h' h'' F.lieLat x hfull hbc hbc''
  have hx'' : (fun i => algebraMap K' K'' (x i)) ≠ 0 := by
    intro e; apply hx; funext i
    have := congrFun e i
    simpa using this
  have hn' : 0 < 4 * n' := by omega
  have hslope := GlobalTheory.T.jet_slope_degree_inequality K'' F.P₀.g h'' (latBC K'' F.lieLat) _ n' _ _ hfull'' hx''
    (fun i σ _ => jetBd_pos _ _ _ _ hn' (hρpos _)) hjet
  rw [hline] at hslope
  set s := deg h' (lineLat (latBC K' F.lieLat) x)
  set T := 1 / 2 + Real.log (Nat.factorial F.P₀.g) / 2 + ((F.P₀.g : ℝ) / 2) * Real.log (4 * n') +
    F.P₀.g * cJ F.P₀.g + ((F.P₀.g : ℝ) / 2) * Real.log (2 + H)
  set large₂ := Real.log (Real.exp 1 * (4 * n') * n')
  have hterm : ∀ i ∈ Finset.range (n' + 1),
      meanLog K'' (fun σ => jetBd F.P₀.g (4 * n') i (ρ (σ.comp (algebraMap K K'')))) ≤ (i : ℝ) / 2 * large₂ + T := by
    intro i hi
    unfold meanLog
    rw [GlobalTheory.T.average_embeddings_field_extension K K'' (fun τ => Real.log (jetBd F.P₀.g (4 * n') i (ρ τ)))]
    exact GlobalTheory.T.jet_bound_log_average_le F.P₀.g K ρ H n' i hH0 hρpos hMat' (by omega) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.sum_mul,
    ← Finset.sum_div, sum_range_cast_id] at hsum
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_neg_distrib, sum_range_cast_id] at hslope

  have hν : ((n' : ℝ) + 1) * (-H / 2 - (F.P₀.g / 4) * Real.log (2 * Real.pi)) ≤
      ((n' : ℝ) + 1) * (-F.falt h / 2 + (F.P₀.g : ℝ) / 4 * Real.log ((4 * n' : ℕ) / (2 * Real.pi))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h4 : 0 ≤ Real.log ((4 * n' : ℕ) : ℝ) := Real.log_natCast_nonneg _
    rw [Real.log_div (by positivity) (by positivity)]
    have : 0 ≤ (F.P₀.g : ℝ) / 4 * Real.log ((4 * n' : ℕ) : ℝ) := by positivity
    have : -F.falt h / 2 ≥ -H / 2 := by linarith [le_max_left (F.falt h) 0]
    nlinarith
  have hT : T = 1 / 2 + Real.log (Nat.factorial F.P₀.g) / 2 + ((F.P₀.g : ℝ) / 2) * Real.log (4 * n') +
    F.P₀.g * cJ F.P₀.g + ((F.P₀.g : ℝ) / 2) * Real.log (2 + H) := rfl
  have e1 : (n' : ℝ) * (n' + 1) / 2 / 2 * large₂ = (n' : ℝ) * (n' + 1) / 4 * large₂ := by ring
  rw [e1] at hsum
  push_cast at hsum
  have hfin : ((n' : ℝ) + 1) * (-H / 2 - (F.P₀.g / 4) * Real.log (2 * Real.pi)) ≤
      -((n' : ℝ) * (n' + 1) / 2) * s + (n' : ℝ) * (n' + 1) / 4 * large₂ + ((n' : ℝ) + 1) * T := by
    linarith
  exact hfin

theorem lieSlope : GlobalTheory.Published.MatrixLemma → GlobalTheory.Published.AbsoluteSiegel → SecJets4 → LieSlope := by
  intro hM hS hJ g
  choose C hC using line_bound hM hJ
  set C0 : ℝ := ∑ g' ∈ Finset.range (g + 1), |C g'| with hC0
  have hC00 : 0 ≤ C0 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogg : 0 ≤ Real.log g := Real.log_natCast_nonneg _
  set X := C0 + Real.log g / 2 + 1 with hX
  have hX0 : 0 ≤ X := by positivity
  refine ⟨1 + X / Real.log 2, by positivity, ?_⟩
  intro K _ _ F hg h hh
  obtain ⟨hfull, -, hconj, -⟩ := GlobalTheory.T.semi_fibration_lie_lattice_full K F
  refine ⟨hfull, ?_⟩
  intro W hW
  set ℓ := Real.log (2 + max (F.falt h) 0) with hℓ
  have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith [le_max_right (F.falt h) 0])
  rcases Nat.eq_zero_or_pos (latRank K W) with h0 | hpos
  · have hWb : W = ⊥ := by
      have h1 : Submodule.span K (W : Set (Fin F.P₀.g → K)) = ⊥ := Submodule.finrank_eq_zero.1 h0
      rw [eq_bot_iff]
      intro w hw
      have : w ∈ Submodule.span K (W : Set (Fin F.P₀.g → K)) := Submodule.subset_span hw
      rw [h1] at this
      simpa using this
    rw [h0, hWb, HadamardFrameExtension.deg_bot]
    simp
  · obtain ⟨K', _, _, _, h', x, hbc, hx, hdeg⟩ := GlobalTheory.T.exists_line_degree_lower_bound hS K F.P₀.g h F.lieLat W hfull (hconj h hh) hW hpos
    have hig : latRank K W ≤ F.P₀.g := by
      unfold latRank
      exact (Submodule.finrank_le _).trans (by simp)
    have hgpos : 0 < F.P₀.g := lt_of_lt_of_le hpos hig
    have hs := hC F.P₀.g K F rfl hgpos h hh K' h' x hbc hx
    have hCle : C F.P₀.g ≤ C0 := (le_abs_self _).trans
      (Finset.single_le_sum (f := fun g' => |C g'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hg)))
    have hlogi : Real.log (latRank K W) ≤ Real.log g :=
      Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hig.trans hg)
    have hi : (0 : ℝ) < latRank K W := by exact_mod_cast hpos
    have hA : deg h W / latRank K W ≤ ℓ + X := by rw [hX]; linarith
    have hXℓ : X ≤ X / Real.log 2 * ℓ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; nlinarith
    rw [div_le_iff₀ hi] at hA
    calc deg h W ≤ (ℓ + X) * latRank K W := hA
      _ ≤ latRank K W * ((1 + X / Real.log 2) * ℓ) := by nlinarith

end GlobalTheory.LieSlopeProof
