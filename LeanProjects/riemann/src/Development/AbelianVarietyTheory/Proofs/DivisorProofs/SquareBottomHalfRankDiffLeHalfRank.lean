import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCMTypeEmbedding
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLNeZeroNat

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

namespace GlobalTheory.LValNe

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem completed_eq {χ : HChar E} {n : I → ℤ} {Λ L : ℂ → ℂ} (h : IsCompletedL χ n Λ) (hL : IsHeckeL χ L) {s : ℂ}
    (hs : ∀ i, Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) : Λ s = archFactor n s * L s := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hA : ∀ (z : ℂ) i, (2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2))) ≠ 0 := fun z i =>
    mul_ne_zero two_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
  let g : ℂ → ℂ := fun z => Λ z * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
    (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹)
  have key : ∀ z : ℂ, (∀ i, Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) → archFactor n z *
      ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹) = 1 := fun z hz => by
    unfold archFactor
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [mul_mul_mul_comm, mul_inv_cancel₀ (hA z i), mul_inv_cancel₀ (hz i), one_mul]
  have hg : Differentiable ℂ g := by
    refine h.1.mul (Differentiable.fun_finsetProd fun i _ => ?_)
    refine Differentiable.mul (fun z => ?_) ?_
    · refine DifferentiableAt.inv ?_ (hA z i)
      exact (((differentiableAt_id.add_const _).neg).const_cpow (Or.inl hpi)).const_mul 2
    · exact Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  have hgL : g = L := entire_eq_of_halfPlane hg hL.1 1 fun z hz => by
    have hz' : ∀ i, Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => Complex.Gamma_ne_zero_of_re_pos (by
      have : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
      simp only [Complex.add_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
      norm_num
      have := abs_nonneg (n i)
      have h2 : (0:ℝ) ≤ |(n i : ℝ)| := abs_nonneg _
      linarith)
    show Λ z * _ = L z
    rw [h.eq_mul hL hz, mul_comm (archFactor n z), mul_assoc, key z hz', mul_one]
  calc Λ s = Λ s * (archFactor n s * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2))⁻¹)) := by rw [key s hs, mul_one]
    _ = archFactor n s * g s := by ring
    _ = archFactor n s * L s := by rw [hgL]

end GlobalTheory.LValNe

namespace GlobalTheory.LValNe

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem nonempty_of_isCMType {φ : I → E →+* ℂ} (hφ : IsCMType φ) : Nonempty I := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  obtain ⟨i, -⟩ := hφ w.embedding
  exact ⟨i⟩

theorem exists_heckeL [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {m : I → ℤ} (hu : IsUnitary χ)
    (hm : HasInf χ φ m) (hpos : ∀ i, 0 < m i) : ∃ Λ, IsHeckeL χ Λ := by
  obtain ⟨i₀⟩ := nonempty_of_isCMType hφ
  exact GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ m χ hφ hu hm ⟨i₀, (hpos i₀).ne'⟩

theorem gamma_int_ne_zero {k : ℤ} (hk : 0 < k) : Complex.Gamma (k : ℂ) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.intCast_re]; exact_mod_cast hk)

theorem half_abs_two_mul (a : ℤ) (ha : 0 < a) : ((|2 * a| : ℤ) : ℂ) / 2 = (a : ℂ) := by
  rw [abs_of_pos (by omega)]; push_cast; ring

theorem half_abs_neg_two_mul (a : ℤ) (ha : 0 < a) : ((|-(2 * a)| : ℤ) : ℂ) / 2 = (a : ℂ) := by
  rw [abs_neg, half_abs_two_mul a ha]

theorem archFactor_ne_zero {n : I → ℤ} {s : ℂ} (hs : ∀ i, Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) :
    archFactor n s ≠ 0 := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (mul_ne_zero two_ne_zero ?_) (hs i)
  rw [Ne, Complex.cpow_eq_zero_iff]; tauto

theorem heckeL_ne_zero_int (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) (hB : CompletedLBoundedInStrips) [IsCMField E]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {m : I → ℤ} (hu : IsUnitary χ) (hm : HasInf χ φ m)
    (hpos : ∀ i, 0 < m i) {L : ℂ → ℂ} (hL : IsHeckeL χ L) (s : ℤ) (hs : ∀ i, 0 < s + m i) : L s ≠ 0 := by
  rcases le_or_gt 1 s with h1 | h1
  · have e : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [← e]
    exact hL.ne_zero_nat hu (by omega)
  obtain ⟨i₀⟩ := nonempty_of_isCMType hφ
  have hn : ∃ i, 2 * m i ≠ 0 := ⟨i₀, by have := hpos i₀; omega⟩
  have hn' : ∃ i, -(2 * m i) ≠ 0 := ⟨i₀, by have := hpos i₀; omega⟩
  have hm' : Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => -(2 * m i)) := GlobalTheory.Published.HeckeFEModel.hasInf_inv hm
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  have hmi : HasInf χ⁻¹ φ (fun i => -m i) := by
    have e : (fun i => 2 * -m i) = fun i => -(2 * m i) := funext fun i => by ring
    show Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => 2 * -m i)
    rw [e]; exact hm'
  obtain ⟨Λ, hΛ, -⟩ := hB E I φ hφ χ (fun i => 2 * m i) hu hm hn
  obtain ⟨Λ', hΛ', -⟩ := hB E I φ hφ χ⁻¹ (fun i => -(2 * m i)) hu' hm' hn'
  obtain ⟨L', hL'⟩ := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ (fun i => -m i) χ⁻¹ hφ hu' hmi
    ⟨i₀, by have := hpos i₀; omega⟩

  have g1 : ∀ i, Complex.Gamma ((1 - (s : ℂ)) + ((|-(2 * m i)| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    rw [half_abs_neg_two_mul _ (hpos i)]
    have := gamma_int_ne_zero (k := 1 - s + m i) (by have := hpos i; omega)
    push_cast at this; exact this
  have e1 := completed_eq hΛ' hL' g1
  have hL1 : L' (1 - (s : ℂ)) ≠ 0 := by
    have e : (((1 - s).toNat : ℕ) : ℂ) = 1 - (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [← e]
    exact hL'.ne_zero_nat hu' (by omega)
  have hΛ'1 : Λ' (1 - (s : ℂ)) ≠ 0 := by
    rw [e1]; exact mul_ne_zero (archFactor_ne_zero g1) hL1
  have hΛs : Λ s ≠ 0 := fun h0 =>
    hΛ'1 ((GlobalTheory.Published.HeckeFEModel.zero_iff hFE hφ hu hm hn hΛ hΛ' s).1 h0)

  have g0 : ∀ i, Complex.Gamma ((s : ℂ) + ((|2 * m i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    rw [half_abs_two_mul _ (hpos i)]
    have := gamma_int_ne_zero (hs i)
    push_cast at this; exact this
  rw [completed_eq hΛ hL g0] at hΛs
  exact right_ne_zero_of_mul hΛs

end GlobalTheory.LValNe

namespace GlobalTheory.SqTop

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

theorem squareBottomHalfRankDiff_le_halfRank (D : D7) (i j : ℕ) : e0 D i j ≤ halfRank D i j := by
  unfold e0 halfRank botBig botSmall
  omega

theorem lNe_square (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) (hB : CompletedLBoundedInStrips) {D : D7} {T : Type}
    {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} [IsCMField D.host.E] (hφ : IsCMType (cmPhi D)) {μ₀ : T} (hL : Lc.Is μ₀)
    (G : GridData Lc sc) (i j : Fin D.R.m) :
    (∀ t, ∃ Λ, IsHeckeL (nuH G t i j) Λ ∧ ∀ s : ℤ, 1 - (e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0) ∧
      ∀ c, ∃ Λ, IsHeckeL (fam G μ₀ i j c) Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0 := by
  have hv := GlobalTheory.FunObj.SqNum.Model.isValChar_nu hL G i j (Nat.zero_le (halfRank D i j))
  have hpos : ∀ τ, 0 < ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ) := fun τ => by
    have := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).2
    omega
  have fam_ok : ∀ χ : HChar D.host.E, IsValChar (cmPhi D) 0 (kap D sc.cGap i j 0) (condF G.pl) ∅ χ →
      ∃ Λ, IsHeckeL χ Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0 := fun χ h => by
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.LValNe.exists_heckeL hφ h.1 h.2.2.1 hpos
    exact ⟨Λ, hΛ, fun s hs => hΛ.ne_zero_nat h.1 hs⟩
  refine ⟨fun t => ?_, fun c => ?_⟩
  · have e : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
      simp only [nuH, hL.xi_base, mul_one]
      exact mul_div_right_comm _ _ _
    obtain ⟨n, hn, hf⟩ := hL.xi_fin t
    have hu : IsUnitary (nuH G t i j) := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G t i j hL)
    have hm : HasInf (nuH G t i j) (cmPhi D) (fun τ => ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) := by
      intro k
      rw [e, Formalism.L2.Host.HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one (Lc.xiH t) hn hf k, mul_one]
      exact hv.1.2.2.1 k
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.LValNe.exists_heckeL hφ hu hm hpos
    refine ⟨Λ, hΛ, fun s hs1 hs2 => GlobalTheory.LValNe.heckeL_ne_zero_int hFE hB hφ hu hm hpos hΛ s fun τ => ?_⟩
    have a0 := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).1
    have a1 := GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (le_refl (halfRank D i j))
    have a2 := squareBottomHalfRankDiff_le_halfRank D i j
    omega
  · cases c with
    | none => exact fam_ok _ hv.1
    | some c => exact fam_ok _ (hv.2 c)

theorem lNe_of_functionalEquation :
    GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LNe := by
  intro hFE hB hFD
  obtain ⟨CF0, h⟩ := hFD
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h'⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hCM, -, hFd, -, -⟩ := h' C hC D large₂ he hx hR T Lc μ₀ hL G
  obtain ⟨-, -, -, -, -, -, hφ, -⟩ := hFd
  exact fun i j => lNe_square hFE hB hφ hL G i j

end GlobalTheory.SqTop
