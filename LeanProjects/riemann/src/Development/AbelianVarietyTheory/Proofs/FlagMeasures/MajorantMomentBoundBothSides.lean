import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.MomBoth

def swapW {k r : ℕ} (W : LocW k r) : LocW k r where
  Wp := W.Wq
  Wq := W.Wp
  π := W.π'
  π' := W.π
  z := W.z'
  z' := W.z
  μG := W.μG
  μW := W.μW'
  μW' := W.μW
  μN := W.μN
  νS := W.νS'
  νS' := W.νS

def swapS {k r : ℕ} {W : LocW k r} (A : LocS W) : LocS (swapW W) where
  H := A.H
  σ := A.σ
  B := A.B'
  B' := A.B
  v0 := A.v0
  cN := A.cN
  deg := A.deg

theorem goodW_swap {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (h : GoodW D τ w w' θ W) : GoodW D τ w' w θ (swapW W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h2, h1, h4, h3, h6, h5, h7, h10, h11, h8, h9, h12, h14, h13⟩

theorem goodS_swap {D : D7} {W : LocW D.R.k D.R.rS} {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (h : GoodS D lam A) : GoodS D lam (swapS A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h4, h3, h5, h6, h7, h8, h10, h9, h11⟩

theorem hypTT_swap {D : D7} {w w' : D.what₂.Word} (h : HypTT D w w') : HypTT D w' w := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h2, h1, h4, h3, h5.symm⟩

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)

theorem momBd_one (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 CMo : ℝ) (hm : 4 ≤ D.R.m)
    (hM : MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo) (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0)
    (τ : D.what₂.Tau) (w w' : D.what₂.Word) (hT : HypTT D w w') (θ : ℝ) (hθ : normWin D large₂ C1 θ)
    (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (hl : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3) (S : LocS W) (hS : GoodS D lam' S) :
    MomBd W.z W.νS S.Φ (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) := by
  intro a
  have hr : 1 ≤ D.R.rS := by unfold Ranks.rS; omega
  have hr3 : (1 : ℝ) ≤ (D.R.rS : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hr)
  have hb := one_le_b large₂.sc
  have h := hM hZ τ w w' hT θ hθ W hW lam' hl S hS a (24 * D.R.rS ^ 3 + 1) (by push_cast; linarith)
  refine h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hb ?_
  have h1 : CMo ≤ max CMo 0 := le_max_left _ _
  have h2 : (0 : ℝ) ≤ (D.R.m : ℝ) * ((24 * D.R.rS ^ 3 + 1 : ℕ) : ℝ) := by positivity
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  rw [Nat.cast_mul 2, Nat.cast_ofNat]
  nlinarith

theorem momBd_both : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 CMo : ℝ), 4 ≤ D.R.m →
    MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S →
      MomBd W.z W.νS S.Φ (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) ∧
      MomBd W.z' W.νS' S.Φ' (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) := by
  intro D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm hM hZ τ w w' hT θ hθ W hW lam' hl S hS
  exact ⟨momBd_one D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm hM hZ τ w w' hT θ hθ W hW lam' hl S hS,
    momBd_one D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm hM hZ τ w' w (hypTT_swap hT) θ hθ (swapW W)
      (goodW_swap hW) lam' hl (swapS S) (goodS_swap hS)⟩

end GlobalTheory.Amp.MomBoth
