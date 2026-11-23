import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

namespace GlobalTheory.InterpConvex

theorem interp_isPosFrame_comparable_blockDiag : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {Cμ : ℝ} {U : Set (ι → ℂ)} {H₀ H : (ι → ℂ) → Matrix n n ℂ} {r s : (ι → ℂ) → ℝ}, IsPosFrame U H₀ → IsPosFrame U H → (∀ z ∈ U, Real.exp 1 ≤ r z) → ContDiffOn ℝ ∞ s U → (∀ z ∈ U, s z ∈ Icc (0 : ℝ) 1) → PowComparable U r Cμ H₀ H → IsPosFrame U (interp H₀ H s) ∧ PowComparable U r Cμ H₀ (interp H₀ H s) ∧ ∀ (σ : Type) (blk : n → σ), IsBlockDiag blk U H₀ → IsBlockDiag blk U H → IsBlockDiag blk U (interp H₀ H s) := by
  intro ι n _ _ _ Cμ U H₀ H r s h₀ h hr hs hs01 hc
  have hre : ∀ z, ∀ v : n → ℂ, (form (interp H₀ H s z) v v).re =
      (1 - s z) * (form (H₀ z) v v).re + s z * (form (H z) v v).re := by
    intro z v
    simp only [interp, form_add, form_smul, Complex.add_re, Complex.re_ofReal_mul]
  refine ⟨⟨h₀.isOpen, fun a b => ?_, fun z hz => ?_⟩, fun z hz v => ?_, fun σ blk hb₀ hb z hz a b hab => ?_⟩
  · have e : (fun x => interp H₀ H s x a b) = fun x =>
        ((1 - s x : ℝ) : ℂ) * H₀ x a b + ((s x : ℝ) : ℂ) * H x a b := by
      funext x; simp [interp]
    rw [e]
    have h1 : ContDiffOn ℝ ∞ (fun x => ((1 - s x : ℝ) : ℂ)) U :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.sub hs)
    have h2 : ContDiffOn ℝ ∞ (fun x => ((s x : ℝ) : ℂ)) U :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hs
    exact (h1.mul (h₀.smooth a b)).add (h2.mul (h.smooth a b))
  · obtain ⟨hs0, hs1⟩ := hs01 z hz
    rcases hs1.lt_or_eq with hlt | heq
    · have ha : ((H₀ z)).PosDef := h₀.posDef z hz
      have hA : (((1 - s z : ℝ) : ℂ) • H₀ z).PosDef :=
        ha.smul (by exact_mod_cast (sub_pos.2 hlt))
      have hB : (((s z : ℝ) : ℂ) • H z).PosSemidef :=
        (h.posDef z hz).posSemidef.smul (by exact_mod_cast hs0)
      exact hA.add_posSemidef hB
    · have hA : (((1 - s z : ℝ) : ℂ) • H₀ z).PosSemidef :=
        (h₀.posDef z hz).posSemidef.smul (by rw [heq]; simp)
      have hB : (((s z : ℝ) : ℂ) • H z).PosDef :=
        (h.posDef z hz).smul (by rw [heq]; simp)
      show (((1 - s z : ℝ) : ℂ) • H₀ z + ((s z : ℝ) : ℂ) • H z).PosDef
      rw [add_comm]; exact hB.add_posSemidef hA
  · obtain ⟨hs0, hs1⟩ := hs01 z hz
    obtain ⟨hlo, hhi⟩ := hc z hz v
    have hq0 : 0 ≤ (form (H₀ z) v v).re := by
      by_cases hv : v = 0
      · subst hv; simp [form]
      · have := ((posDef_iff.1 (h₀.posDef z hz)).2 v hv).1
        simp only [Complex.zero_re] at this
        exact this.le
    set q0 := (form (H₀ z) v v).re
    set q := (form (H z) v v).re
    have hrpos : 0 < r z := lt_of_lt_of_le (Real.exp_pos 1) (hr z hz)
    have hP : 0 < r z ^ Cμ := Real.rpow_pos_of_pos hrpos Cμ
    have hR : r z ^ (-Cμ) = (r z ^ Cμ)⁻¹ := Real.rpow_neg hrpos.le Cμ
    have key : r z ^ (-Cμ) * q0 ≤ q0 ∧ q0 ≤ r z ^ Cμ * q0 := by
      rcases hq0.lt_or_eq with hpos | h0
      · have hRP : r z ^ (-Cμ) ≤ r z ^ Cμ := le_of_mul_le_mul_right (hlo.trans hhi) hpos
        rw [hR] at hRP ⊢
        have h1 : 1 ≤ r z ^ Cμ := by
          by_contra hlt
          push_neg at hlt
          have : 1 < (r z ^ Cμ)⁻¹ := (one_lt_inv₀ hP).2 hlt
          linarith
        have h2 : (r z ^ Cμ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
        constructor <;> nlinarith
      · rw [← h0]; simp
    rw [hre]
    have a1 : 0 ≤ 1 - s z := by linarith
    constructor
    · nlinarith [mul_nonneg a1 (sub_nonneg.2 key.1), mul_nonneg hs0 (sub_nonneg.2 hlo)]
    · nlinarith [mul_nonneg a1 (sub_nonneg.2 key.2), mul_nonneg hs0 (sub_nonneg.2 hhi)]
  · simp [interp, hb₀ z hz a b hab, hb z hz a b hab]

end GlobalTheory.InterpConvex
