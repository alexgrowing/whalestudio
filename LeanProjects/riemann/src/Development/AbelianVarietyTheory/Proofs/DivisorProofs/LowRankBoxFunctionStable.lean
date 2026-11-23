import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankDeficientIntegralRowReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRankNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRightInverseNormalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariantRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv.Nbhd

section
variable {k : Type} [Field k] {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ] (v : Valuation k Γ)
variable {X Y W : Type} [Fintype Y]

theorem val_mul_le {P : Matrix X Y k} {Z : Matrix Y W k} {s t : Γ} (hP : ∀ i a, v (P i a) ≤ s)
    (hZ : ∀ a j, v (Z a j) ≤ t) (i : X) (j : W) : v ((P * Z) i j) ≤ s * t := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun a _ => ?_
  rw [map_mul]; exact mul_le_mul' (hP i a) (hZ a j)
end

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_inv_pow (ϖ : kˣ) (c : ℕ) :
    valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) = (valuation k (ϖ : k))⁻¹ ^ c := by
  simp [Units.val_inv_eq_inv_val, map_inv₀, map_pow, inv_pow]

theorem exists_le_inv_pow {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (x : k) :
    ∃ c : ℕ, valuation k x ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) := by
  by_cases h : valuation k x ≤ 1
  · exact ⟨0, by simpa using h⟩
  · have hx : x ≠ 0 := by rintro rfl; simp at h
    have h0 : 0 < valuation k x := zero_lt_iff.2 (by simpa using hx)
    have hy : valuation k x⁻¹ ≤ 1 := by
      rw [map_inv₀]
      calc (valuation k x)⁻¹ = (valuation k x)⁻¹ * 1 := (mul_one _).symm
        _ ≤ (valuation k x)⁻¹ * valuation k x := mul_le_mul' le_rfl (le_of_not_ge h)
        _ = 1 := inv_mul_cancel₀ h0.ne'
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := 𝒪[k])
      (x := ⟨x⁻¹, hy⟩) (fun h' => hx (inv_eq_zero.1 (congrArg Subtype.val h'))) hϖ.irreducible
    refine ⟨n, ?_⟩
    have h1 : valuation k (algebraMap 𝒪[k] k u) = 1 :=
      (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
    have h2 : valuation k x⁻¹ = valuation k (ϖ : k) ^ n := by
      have := congrArg (fun y : 𝒪[k] => valuation k (y : k)) hu
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow] at this
      rw [this]
      have h1' : valuation k ((u : 𝒪[k]) : k) = 1 := h1
      rw [h1', one_mul]
    rw [valuation_inv_pow, inv_pow, ← h2, map_inv₀, inv_inv]

theorem exists_bound {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {R S : Type} [Fintype R] [Fintype S]
    (H : Matrix R S k) : ∃ c : ℕ, ∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) := by
  choose f hf using fun p : R × S => exists_le_inv_pow hϖ (H p.1 p.2)
  refine ⟨Finset.univ.sup f, fun l i => (hf (l, i)).trans ?_⟩
  rw [valuation_inv_pow, valuation_inv_pow]
  have hle : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  have h1 : 1 ≤ (valuation k (ϖ : k))⁻¹ :=
    calc (1 : _) = valuation k (ϖ : k) * (valuation k (ϖ : k))⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ 1 * (valuation k (ϖ : k))⁻¹ := mul_le_mul' hle le_rfl
      _ = _ := one_mul _
  exact pow_le_pow_right₀ h1 (Finset.le_sup (f := f) (Finset.mem_univ (l, i)))

theorem exists_int_inv_one_add {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n k)
    (hE : ∀ i j, valuation k (E i j) < 1) :
    ∃ N : Matrix n n k, (∀ i j, N i j ∈ 𝒪[k]) ∧ (1 + E) * N = 1 := by
  have hI : ∀ i j, (1 + E) i j ∈ 𝒪[k] := fun i j => by
    rw [Valuation.mem_integer_iff, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ (hE i j).le
    rw [one_apply]; split_ifs <;> simp
  have hEI : ∀ i j, E i j ∈ 𝒪[k] := fun i j => (Valuation.mem_integer_iff _ _).2 (hE i j).le
  let M : Matrix n n 𝒪[k] := fun i j => ⟨(1 + E) i j, hI i j⟩
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix M = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, map_apply]
    have : M i j - (1 : Matrix n n 𝒪[k]) i j = ⟨E i j, hEI i j⟩ := by
      apply Subtype.ext
      by_cases h : i = j <;> simp [M, one_apply, h]
    have hm : M i j - (1 : Matrix n n 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [this, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact hE i j
    have e2 : (IsLocalRing.residue 𝒪[k]) (M i j) = (IsLocalRing.residue 𝒪[k]) ((1 : Matrix n n 𝒪[k]) i j) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hm
    rw [e2]; by_cases h : i = j <;> simp [one_apply, h]
  have hdet : IsUnit M.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hres, det_one]
    exact one_ne_zero
  refine ⟨(algebraMap 𝒪[k] k).mapMatrix M⁻¹, fun i j => (M⁻¹ i j).2, ?_⟩
  have hM : (algebraMap 𝒪[k] k).mapMatrix M = 1 + E := rfl
  rw [← hM, ← map_mul, Matrix.mul_nonsing_inv M hdet, map_one]

end GlobalTheory.RankCoinv.Nbhd

namespace GlobalTheory.RankCoinv.Nbhd
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem inv_mul_mem_box_iff {g : GL A k} (hg : g ∈ KO k A) (ϖ : kˣ) (C X : Matrix A D k) (m : ℕ) :
    (g⁻¹).val * X ∈ box ϖ C (fun _ => m) ↔ X ∈ box ϖ (g.val * C) (fun _ => m) := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff g).1 hg
  have h1' : ∀ i a, valuation k (g.val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (h1 i a)
  have h2' : ∀ i a, valuation k ((g⁻¹).val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (h2 i a)
  simp only [box, Set.mem_setOf_eq]
  constructor
  · intro hZ i j
    have e : X i j - (g.val * C) i j = (g.val * ((g⁻¹).val * X - C)) i j := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.sub_apply]
    rw [e]
    exact (val_mul_le (valuation k) h1' (fun a j => by rw [Matrix.sub_apply]; exact hZ a j) i j).trans_eq (one_mul _)
  · intro hZ i j
    have e : ((g⁻¹).val * X) i j - C i j = ((g⁻¹).val * (X - g.val * C)) i j := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.sub_apply]
    rw [e]
    exact (val_mul_le (valuation k) h2' (fun a j => by rw [Matrix.sub_apply]; exact hZ a j) i j).trans_eq (one_mul _)

theorem omA_boxFn {g : GL A k} (hg : g ∈ KO k A) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (C : Matrix A D k) (m : ℕ) :
    ∃ s : ℂ, omA ν β g 1 (boxFn ϖ C (fun _ => m)) = s • boxFn ϖ (g.val * C) (fun _ => m) := by
  refine ⟨(((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * apow (gdet g) (-(Fintype.card D : ℂ) / 2), funext fun X => ?_⟩
  rw [omA_one_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  by_cases h : X ∈ box ϖ (g.val * C) (fun _ => m)
  · simp only [boxFn]
    rw [Set.indicator_of_mem h, Set.indicator_of_mem ((inv_mul_mem_box_iff hg ϖ C X m).2 h)]
    rfl
  · simp only [boxFn]
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((inv_mul_mem_box_iff hg ϖ C X m).1 h'))]

end GlobalTheory.RankCoinv.Nbhd

open GlobalTheory.RankCoinv.Nbhd GlobalTheory.SplitFlip GlobalTheory.SplitWeil in

theorem GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ) (X₀ : Matrix A D k), X₀.rank = r → r < Fintype.card A → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ C ∈ GlobalTheory.RankCoinv.box ϖ X₀ (fun _ => m₀), GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hνϖ r X₀ hrank hr
  obtain ⟨g, hg, i₀, hi₀⟩ := GlobalTheory.T.rank_deficient_integral_row_reduction k A D X₀ (hrank ▸ hr)
  have hgint := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have hg1 : ∀ i a, valuation k (g.val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (hgint.1 i a)
  have hYr : (g.val * X₀).rank = r := by
    rw [← hrank]
    exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  obtain ⟨H₁, Q₁, hHQ⟩ : ∃ (H₁ : Matrix (Fin r) A k) (Q₁ : Matrix D (Fin r) k), H₁ * (g.val * X₀) * Q₁ = 1 := by
    rw [← hYr]; exact GlobalTheory.T.matrix_rank_normal_form k A D _
  let H₂ : Matrix (Fin r) A k := Matrix.of fun l i => if i = i₀ then 0 else H₁ l i
  have hH₂Y : H₂ * (g.val * X₀) = H₁ * (g.val * X₀) := by
    ext l j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [H₂, Matrix.of_apply]
    split_ifs with h
    · rw [h, hi₀ j, zero_mul, mul_zero]
    · rfl
  obtain ⟨h, Q₀, hhY, hQ₀, hhYQ⟩ := GlobalTheory.T.integral_right_inverse_normalization k D r (H₂ * (g.val * X₀)) Q₁ (by rw [hH₂Y, hHQ])
  let H := h * H₂
  have hHi₀ : ∀ l, H l i₀ = 0 := fun l => by simp [H, H₂, Matrix.mul_apply]
  obtain ⟨c, hc⟩ := exists_bound hϖ H
  refine ⟨c + 1, fun m hm C hC => ?_⟩
  have hϖ0 : valuation k (ϖ : k) ≠ 0 := by simp
  have hϖlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hCX : ∀ a j, valuation k ((C - X₀) a j) ≤ valuation k (ϖ : k) ^ (c + 1) := fun a j => by
    rw [Matrix.sub_apply]; simpa using hC a j
  have hgCX : ∀ i j, valuation k ((g.val * (C - X₀)) i j) ≤ valuation k (ϖ : k) ^ (c + 1) := fun i j => by
    simpa using val_mul_le (valuation k) hg1 hCX i j
  have hc' : ∀ l i, valuation k (H l i) ≤ (valuation k (ϖ : k))⁻¹ ^ c := fun l i => by
    rw [← valuation_inv_pow]; exact hc l i
  have hprod : (valuation k (ϖ : k))⁻¹ ^ c * valuation k (ϖ : k) ^ (c + 1) = valuation k (ϖ : k) := by
    rw [inv_pow, pow_succ, inv_mul_cancel_left₀ (pow_ne_zero _ hϖ0)]
  have hEb : ∀ l j, valuation k ((H * (g.val * (C - X₀))) l j) ≤ valuation k (ϖ : k) := fun l j => by
    rw [← hprod]; exact val_mul_le (valuation k) hc' hgCX l j
  have hsplit : g.val * C = g.val * X₀ + g.val * (C - X₀) := by rw [Matrix.mul_sub]; abel
  have hHY : H * (g.val * X₀) = h * (H₂ * (g.val * X₀)) := Matrix.mul_assoc _ _ _
  have hHC : H * (g.val * C) = H * (g.val * X₀) + H * (g.val * (C - X₀)) := by rw [hsplit, Matrix.mul_add]
  have hHCint : ∀ l j, (H * (g.val * C)) l j ∈ 𝒪[k] := fun l j => by
    rw [hHC, Valuation.mem_integer_iff, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ ((hEb l j).trans hϖlt.le)
    rw [hHY]; exact hhY l j
  have hQ₀' : ∀ j l, valuation k (Q₀ j l) ≤ 1 := fun j l => (Valuation.mem_integer_iff _ _).1 (hQ₀ j l)
  set E := H * (g.val * (C - X₀)) * Q₀ with hE
  have hEv : ∀ i j, valuation k (E i j) < 1 := fun i j =>
    lt_of_le_of_lt (by simpa using val_mul_le (valuation k) hEb hQ₀' i j) hϖlt
  have hHCQ : H * (g.val * C) * Q₀ = 1 + E := by
    rw [hHC, Matrix.add_mul, hHY, hhYQ]
  obtain ⟨N, hN, hN1⟩ := exists_int_inv_one_add E hEv
  have hN' : ∀ i j, valuation k (N i j) ≤ 1 := fun i j => (Valuation.mem_integer_iff _ _).1 (hN i j)
  have hQint : ∀ j l, (Q₀ * N) j l ∈ 𝒪[k] := fun j l => by
    rw [Valuation.mem_integer_iff]; simpa using val_mul_le (valuation k) hQ₀' hN' j l
  have hHCQ' : H * (g.val * C) * (Q₀ * N) = 1 := by rw [← Matrix.mul_assoc, hHCQ, hN1]
  have hrow : ∀ j, valuation k ((g.val * C) i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k) := fun j => by
    rw [hsplit, Matrix.add_apply, hi₀ j, zero_add]; simpa using hgCX i₀ j
  have hmem := GlobalTheory.T.box_function_twisted_coinvariant_rank k A D ϖ hϖ ν β hν hνϖ i₀ r c m (g.val * C) H (Q₀ * N) hHi₀ hc (by omega)
    hHCint hQint hHCQ' hrow
  obtain ⟨s, hs⟩ := omA_boxFn hg ν β ϖ C m
  have hΦ := boxFn_mem_SB ϖ C (fun _ => m)
  have h1 : omA ν β g 1 (boxFn ϖ C (fun _ => m)) ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    rw [hs]; exact Submodule.smul_mem _ _ hmem
  have h2 : omA ν β g 1 (boxFn ϖ C (fun _ => m)) - boxFn ϖ C (fun _ => m) ∈ lowRank (r + 1) ⊔ twistSpan ν β :=
    Submodule.mem_sup_right (sub_mem_twistSpan ν β g hΦ)
  simpa using sub_mem h1 h2
