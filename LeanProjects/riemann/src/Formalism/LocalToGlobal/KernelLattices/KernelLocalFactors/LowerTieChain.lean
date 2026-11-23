import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.TensorFockHolds

open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL

section LcOne

open Formalism.BranchingDeterminantCap

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

theorem fock_pairing_normalized_isometry (c : Fin n → ℕ) (p q : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ nablaSq ℂ n s)
    (hq : q ∈ nablaSq ℂ n s) :
    fockF (nmJ hN l c p) (nmJ hN l c q) * fockF (extremal ℂ n s) (extremal ℂ n s) =
      fockF (nmJ hN l c (extremal ℂ n s)) (nmJ hN l c (extremal ℂ n s)) * fockF p q := by
  let D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ := fun p q =>
    fockF (nmJ hN l c p) (nmJ hN l c q) * fockF (extremal ℂ n s) (extremal ℂ n s) -
      fockF (nmJ hN l c (extremal ℂ n s)) (nmJ hN l c (extremal ℂ n s)) * fockF p q
  have H : BsForm s.natW D := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p p' q
      simp only [D, map_add, fischerInner_add_left]; ring
    · intro c p q
      simp only [D, map_smul, bs_fock_smul_left]; ring
    · intro p q q'
      simp only [D, map_add, fischerInner_add_right]; ring
    · intro c p q
      simp only [D, map_smul, bs_fock_smul_right]; ring
    · intro g p _ q _
      simp only [D]
      rw [nmJ_rowAct, nmJ_rowAct, fockRowAdj N N, fockRowAdj n n, nmExt_conj]
  have h0 : D (hw ℂ le_rfl s.natW) (hw ℂ le_rfl s.natW) = 0 := by
    simp only [D, extremal]; ring
  have e := H.eq_zero (natW_antitone s) h0 p hp q hq
  simp only [D] at e
  exact sub_eq_zero.mp e

theorem lc_adj (F : MvPolynomial (Fin N × Fin N) ℂ) (hF : F ∈ nablaSq ℂ N l) (v : MvPolynomial (Fin n × Fin n) ℂ)
    (hv : v ∈ nablaSq ℂ n s) :
    fockF (brOne ℂ hN l s F) v * (bFac (fun _ : Unit => nmB hN l s) : ℂ) =
      (((cBr hN l s : ℤ) : ℂ) * kapBr ℂ hN l s) * fockF F (nmJ hN l (nmB hN l s) v) := by
  rw [nm_br_fockF hN l s F v hv, fischerInner_eq_star F (raiseOne hN (nmB hN l s) v), ← nmJ_fockF hN l _ v F hF,
    ← fischerInner_eq_star]

end LcOne

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL

section LcTen

open Formalism.BranchingDeterminantCap

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def tSpan {n : ℕ} (V : ι → Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ)) :
    Submodule ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℂ, (∀ τ, f τ ∈ V τ) ∧ p = Formalism.MainNotions.product_first_zeroth_parts.ten f}

theorem lc_fockF_zero_right {σ : Type} (f : MvPolynomial σ ℂ) : fockF f 0 = 0 := by
  rw [fischerInner_eq_star, nm_fockF_zero_left, star_zero]

theorem lc_fock_ten {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    fockF (Formalism.MainNotions.product_first_zeroth_parts.ten f) (Formalism.MainNotions.product_first_zeroth_parts.ten g) = ∏ τ, fockF (f τ) (g τ) :=
  Formalism.L2.Geo.Def.TensorFock_holds ι (Fin n × Fin n) f g

theorem lc_blk_mem {n n' : ℕ} (A : ι → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ)
    (V : ι → Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ)) (W : ι → Submodule ℂ (MvPolynomial (Fin n' × Fin n') ℂ))
    (hA : ∀ τ, ∀ F ∈ V τ, A τ F ∈ W τ) (x : MvPolynomial (ι × Fin n × Fin n) ℂ) (hx : x ∈ tSpan V) :
    Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(A τ)) x ∈ tSpan W := by
  induction hx using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f, hf, rfl⟩ := hp
    rw [Formalism.MainNotions.product_first_zeroth_parts.blk_ten]
    exact Submodule.subset_span ⟨_, fun τ => hA τ _ (hf τ), rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem lc_ten_adj {n n' : ℕ} (A : ι → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ)
    (J : ι → MvPolynomial (Fin n' × Fin n') ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
    (V : ι → Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ)) (W : ι → Submodule ℂ (MvPolynomial (Fin n' × Fin n') ℂ))
    (a : ι → ℂ) (hadj : ∀ τ, ∀ F ∈ V τ, ∀ v ∈ W τ, fockF (A τ F) v = a τ * fockF F (J τ v))
    (x : MvPolynomial (ι × Fin n × Fin n) ℂ) (hx : x ∈ tSpan V) (y : MvPolynomial (ι × Fin n' × Fin n') ℂ)
    (hy : y ∈ tSpan W) :
    fockF (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(A τ)) x) y = (∏ τ, a τ) * fockF x (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(J τ)) y) := by
  induction hx using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f, hf, rfl⟩ := hp
    induction hy using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨g, hg, rfl⟩ := hq
      rw [Formalism.MainNotions.product_first_zeroth_parts.blk_ten, Formalism.MainNotions.product_first_zeroth_parts.blk_ten, lc_fock_ten, lc_fock_ten, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun τ _ => hadj τ _ (hf τ) _ (hg τ)
    | zero => rw [map_zero, lc_fockF_zero_right, lc_fockF_zero_right, mul_zero]
    | add y y' _ _ h1 h2 => rw [map_add, fischerInner_add_right, fischerInner_add_right, h1, h2, mul_add]
    | smul c y _ h1 => rw [map_smul, bs_fock_smul_right, bs_fock_smul_right, h1]; ring
  | zero => rw [map_zero, nm_fockF_zero_left, nm_fockF_zero_left, mul_zero]
  | add x x' _ _ h1 h2 => rw [map_add, fischerInner_add_left, fischerInner_add_left, h1, h2, mul_add]
  | smul c x _ h1 => rw [map_smul, bs_fock_smul_left, bs_fock_smul_left, h1]; ring

theorem lc_ten_iso {n n' : ℕ} (J : ι → MvPolynomial (Fin n' × Fin n') ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
    (W : ι → Submodule ℂ (MvPolynomial (Fin n' × Fin n') ℂ)) (b : ι → ℂ)
    (hiso : ∀ τ, ∀ v ∈ W τ, ∀ v' ∈ W τ, fockF (J τ v) (J τ v') = b τ * fockF v v')
    (y : MvPolynomial (ι × Fin n' × Fin n') ℂ) (hy : y ∈ tSpan W) (y' : MvPolynomial (ι × Fin n' × Fin n') ℂ)
    (hy' : y' ∈ tSpan W) :
    fockF (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(J τ)) y) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(J τ)) y') = (∏ τ, b τ) * fockF y y' := by
  induction hy using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f, hf, rfl⟩ := hp
    induction hy' using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨g, hg, rfl⟩ := hq
      rw [Formalism.MainNotions.product_first_zeroth_parts.blk_ten, Formalism.MainNotions.product_first_zeroth_parts.blk_ten, lc_fock_ten, lc_fock_ten, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun τ _ => hiso τ _ (hf τ) _ (hg τ)
    | zero => rw [map_zero, lc_fockF_zero_right, lc_fockF_zero_right, mul_zero]
    | add y y' _ _ h1 h2 => rw [map_add, fischerInner_add_right, fischerInner_add_right, h1, h2, mul_add]
    | smul c y _ h1 => rw [map_smul, bs_fock_smul_right, bs_fock_smul_right, h1]; ring
  | zero => rw [map_zero, nm_fockF_zero_left, nm_fockF_zero_left, mul_zero]
  | add x x' _ _ h1 h2 => rw [map_add, fischerInner_add_left, fischerInner_add_left, h1, h2, mul_add]
  | smul c x _ h1 => rw [map_smul, bs_fock_smul_left, bs_fock_smul_left, h1]; ring

theorem lc_ten_le {n n' : ℕ} (A : ι → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ)
    (J : ι → MvPolynomial (Fin n' × Fin n') ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
    (V : ι → Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ)) (W : ι → Submodule ℂ (MvPolynomial (Fin n' × Fin n') ℂ))
    (α β : ι → ℝ) (hA : ∀ τ, ∀ F ∈ V τ, A τ F ∈ W τ)
    (hadj : ∀ τ, ∀ F ∈ V τ, ∀ v ∈ W τ, fockF (A τ F) v = (α τ : ℂ) * fockF F (J τ v))
    (hiso : ∀ τ, ∀ v ∈ W τ, ∀ v' ∈ W τ, fockF (J τ v) (J τ v') = (β τ : ℂ) * fockF v v') (hβ : ∀ τ, 0 ≤ β τ)
    (x : MvPolynomial (ι × Fin n × Fin n) ℂ) (hx : x ∈ tSpan V) :
    (fockF (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(A τ)) x) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(A τ)) x)).re ≤
      (∏ τ, α τ ^ 2 * β τ) * (fockF x x).re := by
  set y := Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(A τ)) x with hy
  have hyW : y ∈ tSpan W := lc_blk_mem A V W hA x hx
  set z := Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(J τ)) y with hz
  have e1 := lc_ten_adj A J V W (fun τ => (α τ : ℂ)) hadj x hx y hyW
  have e2 := lc_ten_iso J W (fun τ => (β τ : ℂ)) hiso y hyW y hyW
  rw [← hz] at e1 e2
  rw [← Complex.ofReal_prod] at e1 e2
  set Pa := ∏ τ, α τ with hPa
  set Pb := ∏ τ, β τ with hPb
  set Y := (fockF y y).re with hYd
  set X := (fockF x x).re with hXd
  have hY0 : 0 ≤ Y := nm_fockF_nonneg y
  have hX0 : 0 ≤ X := nm_fockF_nonneg x
  have hPb0 : 0 ≤ Pb := Finset.prod_nonneg fun τ _ => hβ τ
  have hprod : ∏ τ, α τ ^ 2 * β τ = Pa ^ 2 * Pb := by rw [Finset.prod_mul_distrib, Finset.prod_pow]
  rw [hprod]
  have eY : fockF y y = (Y : ℂ) := nm_fockF_self y
  by_cases ha : Pa = 0
  · have h0 : fockF y y = 0 := by rw [e1, ha]; simp
    have : Y = 0 := by rw [hYd, h0]; simp
    rw [this]; positivity
  · have hzv : fockF x z = ((Y / Pa : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast ha), mul_comm, ← eY, e1]
    have cs := nm_cs_real x z (Y / Pa) hzv
    have hzz : (fockF z z).re = Pb * Y := by
      rw [e2, eY, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hzz] at cs
    have hpa2 : 0 < Pa ^ 2 := lt_of_le_of_ne (sq_nonneg Pa) (Ne.symm (pow_ne_zero 2 ha))
    have h3 : Y ^ 2 ≤ Pa ^ 2 * Pb * X * Y := by
      have h4 := mul_le_mul_of_nonneg_left cs hpa2.le
      have e : Pa ^ 2 * (Y / Pa) ^ 2 = Y ^ 2 := by field_simp
      calc Y ^ 2 = Pa ^ 2 * (Y / Pa) ^ 2 := e.symm
        _ ≤ Pa ^ 2 * (X * (Pb * Y)) := h4
        _ = Pa ^ 2 * Pb * X * Y := by ring
    rcases eq_or_lt_of_le hY0 with h0 | hpos
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_right (by rw [← pow_two]; exact h3) hpos

end LcTen

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL

section LcBr

open Formalism.BranchingDeterminantCap

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

def lcA : ℝ := ((cBr hN l s : ℤ) : ℝ) * kapBr ℝ hN l s / ((bFac (fun _ : Unit => nmB hN l s) : ℕ) : ℝ)

def lcB : ℝ := (fockF (nmJ hN l (nmB hN l s) (extremal ℂ n s)) (nmJ hN l (nmB hN l s) (extremal ℂ n s))).re /
  (fockF (extremal ℂ n s) (extremal ℂ n s)).re

theorem lc_bFac_ne : ((bFac (fun _ : Unit => nmB hN l s) : ℕ) : ℝ) ≠ 0 := by
  have : bFac (fun _ : Unit => nmB hN l s) ≠ 0 := by
    unfold bFac
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _
  exact_mod_cast this

theorem lc_adjR (F : MvPolynomial (Fin N × Fin N) ℂ) (hF : F ∈ nablaSq ℂ N l) (v : MvPolynomial (Fin n × Fin n) ℂ)
    (hv : v ∈ nablaSq ℂ n s) :
    fockF (brOne ℂ hN l s F) v = (lcA hN l s : ℂ) * fockF F (nmJ hN l (nmB hN l s) v) := by
  have h := lc_adj hN l s F hF v hv
  have hb : ((bFac (fun _ : Unit => nmB hN l s) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast lc_bFac_ne hN l s
  have hk : kapBr ℂ hN l s = ((kapBr ℝ hN l s : ℝ) : ℂ) :=
    (lb_map_kapBr (K := ℝ) (K' := ℂ) Complex.ofRealHom hN l s).symm
  rw [hk] at h
  have e := eq_div_of_mul_eq hb h
  rw [e]
  unfold lcA
  push_cast
  ring

theorem lc_isoR (p q : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ nablaSq ℂ n s) (hq : q ∈ nablaSq ℂ n s) :
    fockF (nmJ hN l (nmB hN l s) p) (nmJ hN l (nmB hN l s) q) = (lcB hN l s : ℂ) * fockF p q := by
  have h := fock_pairing_normalized_isometry hN l s (nmB hN l s) p q hp hq
  have hs : (((fockF (extremal ℂ n s) (extremal ℂ n s)).re : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (fockPos _ _ (lm_extremal_ne (K := ℂ) s)).1.ne'
  rw [nm_fockF_self (extremal ℂ n s), nm_fockF_self (nmJ hN l (nmB hN l s) (extremal ℂ n s))] at h
  unfold lcB
  push_cast
  rw [div_mul_eq_mul_div, eq_div_iff hs, h]

theorem lcB_nonneg : 0 ≤ lcB hN l s :=
  div_nonneg (nm_fockF_nonneg _) (fockPos _ _ (lm_extremal_ne (K := ℂ) s)).1.le

theorem lc_const (hI : Br.Interlace hN l s) (hS : SameShift l s) :
    lcA hN l s ^ 2 * lcB hN l s = ((cBr hN l s : ℤ) : ℝ) ^ 2 * kapBr ℝ hN l s *
      ((fockF (extremal ℂ n s) (extremal ℂ n s)).re / (fockF (extremal ℂ N l) (extremal ℂ N l)).re) := by
  set x := (fockF (xiBr ℂ hN l s) (xiBr ℂ hN l s)).re with hx
  set hs := (fockF (extremal ℂ n s) (extremal ℂ n s)).re with hhs
  set hl := (fockF (extremal ℂ N l) (extremal ℂ N l)).re with hhl
  set b := ((bFac (fun _ : Unit => nmB hN l s) : ℕ) : ℝ) with hb
  set cR := ((cBr hN l s : ℤ) : ℝ) with hcR
  set JH := (fockF (nmJ hN l (nmB hN l s) (extremal ℂ n s)) (nmJ hN l (nmB hN l s) (extremal ℂ n s))).re with hJH
  have xpos : 0 < x := (fockPos _ _ (xiBr_ne hN l s hI hS)).1
  have hspos : 0 < hs := (fockPos _ _ (lm_extremal_ne s)).1
  have hlpos : 0 < hl := (fockPos _ _ (lm_extremal_ne l)).1
  have bne : b ≠ 0 := lc_bFac_ne hN l s
  have cne : cR ≠ 0 := by rw [hcR]; exact_mod_cast cBr_ne_zero hN l s hI
  have E4 := congrArg (fun y => fockF y y) (nmJ_h hN l s hI hS)
  simp only [fockF_smul_smul] at E4
  rw [nm_ioConst, ← hx, ← hhs, ← hb, ← hcR, nm_fockF_self (nmJ hN l (nmB hN l s) (extremal ℂ n s)), ← hJH,
    nm_fockF_self (xiBr ℂ hN l s), ← hx] at E4
  have e4 : (cR * x / (hs * b)) * (cR * x / (hs * b)) * JH = cR * cR * x := by
    have s1 : star ((cR * x / (hs * b) : ℝ) : ℂ) = ((cR * x / (hs * b) : ℝ) : ℂ) := by simp
    have s2 : star ((cBr hN l s : ℤ) : ℂ) = ((cBr hN l s : ℤ) : ℂ) := by simp
    rw [s1, s2] at E4
    have c2 : ((cBr hN l s : ℤ) : ℂ) = ((cR : ℝ) : ℂ) := by rw [hcR]; push_cast; rfl
    rw [c2] at E4
    exact_mod_cast E4
  have hJ : JH = (hs * b) ^ 2 / x := by
    have ha : cR * x / (hs * b) ≠ 0 := div_ne_zero (mul_ne_zero cne xpos.ne') (mul_ne_zero hspos.ne' bne)
    field_simp at e4
    field_simp
    nlinarith [e4, sq_nonneg cR, sq_nonneg x, mul_pos xpos xpos]
  unfold lcA lcB
  rw [← hcR, ← hb, ← hJH, ← hhs, hJ, nm_kapR, ← hx, ← hhl]
  field_simp

end LcBr

section LcBrTen

open Formalism.BranchingDeterminantCap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N n : ℕ} (hN : N = n + 1) (l : ι → DomWeight N) (s : ι → DomWeight n)

theorem lc_den {k : ℕ} (m : ι → DomWeight k) :
    (∏ τ, fockF (extremal ℂ k (m τ)) (extremal ℂ k (m τ))) =
      (((∏ τ, (fockF (extremal ℂ k (m τ)) (extremal ℂ k (m τ))).re : ℝ)) : ℂ) := by
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun τ _ => nm_fockF_self _

theorem lc_den_pos {k : ℕ} (m : ι → DomWeight k) : 0 < ∏ τ, (fockF (extremal ℂ k (m τ)) (extremal ℂ k (m τ))).re :=
  Finset.prod_pos fun τ _ => (fockPos _ _ (lm_extremal_ne (K := ℂ) (m τ))).1

theorem lc_brTen_le (hI : ∀ τ, Br.Interlace hN (l τ) (s τ)) (hS : ∀ τ, SameShift (l τ) (s τ))
    (p : MvPolynomial (ι × Fin N × Fin N) ℂ) (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan l) :
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll s (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(brOne ℂ hN (l τ) (s τ))) p)
      (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(brOne ℂ hN (l τ) (s τ))) p)).re ≤
      (∏ τ, ((cBr hN (l τ) (s τ) : ℤ) : ℝ) ^ 2 * kapBr ℝ hN (l τ) (s τ)) * (Formalism.MainNotions.product_first_zeroth_parts.nfAll l p p).re := by
  have hp' : p ∈ tSpan (fun τ => nablaSq ℂ N (l τ)) := by
    simpa only [tSpan, Formalism.MainNotions.product_first_zeroth_parts.CSpan, nablaSq_eq_delSq] using hp
  have key := lc_ten_le (fun τ => brOne ℂ hN (l τ) (s τ)) (fun τ => nmJ hN (l τ) (nmB hN (l τ) (s τ)))
    (fun τ => nablaSq ℂ N (l τ)) (fun τ => nablaSq ℂ n (s τ)) (fun τ => lcA hN (l τ) (s τ)) (fun τ => lcB hN (l τ) (s τ))
    (fun τ F _ => brOne_mem hN (l τ) (s τ) F) (fun τ F hF v hv => lc_adjR hN (l τ) (s τ) F hF v hv)
    (fun τ v hv v' hv' => lc_isoR hN (l τ) (s τ) v v' hv hv') (fun τ => lcB_nonneg hN (l τ) (s τ)) p hp'
  rw [Finset.prod_congr rfl (fun τ _ => lc_const hN (l τ) (s τ) (hI τ) (hS τ)), Finset.prod_mul_distrib,
    Finset.prod_div_distrib] at key
  unfold Formalism.MainNotions.product_first_zeroth_parts.nfAll
  rw [lc_den s, lc_den l, Complex.div_ofReal_re, Complex.div_ofReal_re]
  have hs0 := lc_den_pos s
  have hl0 := lc_den_pos l
  calc _ ≤ ((∏ τ, ((cBr hN (l τ) (s τ) : ℤ) : ℝ) ^ 2 * kapBr ℝ hN (l τ) (s τ)) *
        ((∏ τ, (fockF (extremal ℂ n (s τ)) (extremal ℂ n (s τ))).re) /
          (∏ τ, (fockF (extremal ℂ N (l τ)) (extremal ℂ N (l τ))).re)) * (fockF p p).re) /
        (∏ τ, (fockF (extremal ℂ n (s τ)) (extremal ℂ n (s τ))).re) := div_le_div_of_nonneg_right key hs0.le
    _ = _ := by field_simp

end LcBrTen

section LcFrame

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

theorem lc_rowAct_comp {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) (p : MvPolynomial (Fin k × Fin k) ℂ) :
    rowAct ℂ B (rowAct ℂ A p) = rowAct ℂ (A * B) p := by
  rw [Formalism.UG.P.wlocal_rowAct_mul]; rfl

theorem lc_sqAct_mul {k : ℕ} (m : DomWeight k) (g h : GL (Fin k) ℂ) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    sqAct ℂ k m (g * h) f = sqAct ℂ k m g (sqAct ℂ k m h f) := by
  unfold sqAct
  rw [map_smul, smul_smul, lc_rowAct_comp, Matrix.GeneralLinearGroup.coe_mul, Matrix.transpose_mul, detPow_mul]

theorem lc_sqAct_smul {k : ℕ} (m : DomWeight k) (g : GL (Fin k) ℂ) (c : ℂ) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    sqAct ℂ k m g (c • f) = c • sqAct ℂ k m g f := by
  unfold sqAct
  rw [map_smul, smul_comm]

theorem lc_frame_one (hI : Br.Interlace hN l s) (hS : SameShift l s) (g : GL (Fin n) ℂ) (a : ℂˣ)
    (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ n s g (brOne ℂ hN l s f) = (((a ^ Formalism.MainNotions.PrimeDegreeVariant.degZ l s : ℂˣ) : ℂ))⁻¹ •
      brOne ℂ hN l s (sqAct ℂ N l (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g * Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ N a) f) := by
  rw [lc_sqAct_mul, brOne_sqAct hN l s hS, brOne_last hN l s hI, lc_sqAct_smul, inv_smul_smul₀ (Units.ne_zero _)]

end LcFrame

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL

section LcFrameTen

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N n : ℕ} (hN : N = n + 1) (l : ι → DomWeight N) (s : ι → DomWeight n)

theorem lc_frame (hI : ∀ τ, Br.Interlace hN (l τ) (s τ)) (hS : ∀ τ, SameShift (l τ) (s τ)) (g : ι → GL (Fin n) ℂ)
    (a : ℂˣ) (p : MvPolynomial (ι × Fin N × Fin N) ℂ) :
    Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => sqAct ℂ n (s τ) (g τ)) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(brOne ℂ hN (l τ) (s τ))) p) =
      (∏ τ, (((a ^ Formalism.MainNotions.PrimeDegreeVariant.degZ (l τ) (s τ) : ℂˣ) : ℂ))⁻¹) •
        Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(brOne ℂ hN (l τ) (s τ)))
          (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => sqAct ℂ N (l τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ) * Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ N a)) p) := by
  have e1 : (fun τ => sqAct ℂ n (s τ) (g τ)) = fun τ => ⇑(ta_sqActL (s τ) (g τ)) :=
    funext fun τ => (ta_sqActL_coe _ _).symm
  have e2 : (fun τ => sqAct ℂ N (l τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ) * Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ N a)) =
      fun τ => ⇑(ta_sqActL (l τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ) * Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ N a)) :=
    funext fun τ => (ta_sqActL_coe _ _).symm
  rw [e1, e2, ta_blk_comp, ta_blk_comp]
  have hF : ∀ τ, ta_sqActL (s τ) (g τ) ∘ₗ brOne ℂ hN (l τ) (s τ) =
      (((a ^ Formalism.MainNotions.PrimeDegreeVariant.degZ (l τ) (s τ) : ℂˣ) : ℂ))⁻¹ •
        (brOne ℂ hN (l τ) (s τ) ∘ₗ ta_sqActL (l τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ) * Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ N a)) := by
    intro τ
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, ta_sqActL_coe]
    exact lc_frame_one hN (l τ) (s τ) (hI τ) (hS τ) (g τ) a f
  simp only [hF]
  rw [blk_smul, LinearMap.smul_apply]

theorem lc_nfAll_smul {k : ℕ} (m : ι → DomWeight k) (c : ℂ) (q : MvPolynomial (ι × Fin k × Fin k) ℂ) :
    Formalism.MainNotions.product_first_zeroth_parts.nfAll m (c • q) (c • q) = (c * star c) * Formalism.MainNotions.product_first_zeroth_parts.nfAll m q q := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.nfAll
  rw [fockF_smul_smul, mul_div_assoc]

theorem lc_blk_sqAct_mem {k : ℕ} (m : ι → DomWeight k) (g : ι → GL (Fin k) ℂ) (p : MvPolynomial (ι × Fin k × Fin k) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan m) : Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => sqAct ℂ k (m τ) (g τ)) p ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan m := by
  have e : (fun τ => sqAct ℂ k (m τ) (g τ)) = fun τ => ⇑(ta_sqActL (m τ) (g τ)) :=
    funext fun τ => (ta_sqActL_coe _ _).symm
  rw [e]
  exact lc_blk_mem (fun τ => ta_sqActL (m τ) (g τ)) (fun τ => delSq ℂ k (m τ)) (fun τ => delSq ℂ k (m τ))
    (fun τ F hF => by rw [ta_sqActL_coe]; exact eps_sqAct_mem k (m τ) (g τ) F hF) p hp

theorem lc_sqrt_norm (T : ℝ) (hT : 0 < T) (d : ℤ) :
    ((((Units.mk0 ((Real.sqrt T : ℝ) : ℂ) (by exact_mod_cast (Real.sqrt_pos.mpr hT).ne') ^ d : ℂˣ) : ℂ))⁻¹) *
      star ((((Units.mk0 ((Real.sqrt T : ℝ) : ℂ) (by exact_mod_cast (Real.sqrt_pos.mpr hT).ne') ^ d : ℂˣ) : ℂ))⁻¹) =
      ((T ^ (-d) : ℝ) : ℂ) := by
  have hr : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr hT
  have e : (((Units.mk0 ((Real.sqrt T : ℝ) : ℂ) (by exact_mod_cast hr.ne') ^ d : ℂˣ) : ℂ)) = ((Real.sqrt T ^ d : ℝ) : ℂ) := by
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, Complex.ofReal_zpow]
  rw [e, ← Complex.ofReal_inv]
  have hst : star (((Real.sqrt T ^ d)⁻¹ : ℝ) : ℂ) = (((Real.sqrt T ^ d)⁻¹ : ℝ) : ℂ) := by simp
  rw [hst, ← Complex.ofReal_mul]
  congr 1
  rw [← mul_inv, ← mul_zpow, Real.mul_self_sqrt hT.le, zpow_neg]

end LcFrameTen

section LcRec

open Formalism.MainNotions.product_first_zeroth_parts

variable {D : Formalism.BasicNotions.D7} {u : D.what₂.Word}

def lowerNormConst (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : ℝ :=
  ∏ τ, ((D.mem u).A.T : ℝ) ^ (-(Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ))) *
    (((cBr (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) : ℤ) : ℝ) ^ 2 *
      kapBr ℝ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ))

def valNormAt (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (φ : Fn D u D.R.m) : ℝ :=
  ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re

theorem lc_nfAll_lam : nfAll ((D.fm u).lam D.R.m) = nfAll (lamTr D u) := by
  funext p q
  simp only [nfAll, lamTr, extremal_wSh]

theorem lc_nfAll_sg : nfAll (D.fm u).sg = nfAll (sgTr D u) := by
  funext p q
  simp only [nfAll, sgTr, extremal_wSh]

theorem lc_cspan_lam : CSpan ((D.fm u).lam D.R.m) = CSpan (lamTr D u) := by
  simp only [CSpan, lamTr, delSq_wSh]

theorem lc_member_le (hI : (D.fm u).SgInterlace) (g : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (p : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hp : p ∈ CSpan ((D.fm u).lam D.R.m)) :
    (nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (g τ)) (brTen D u p))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (g τ)) (brTen D u p))).re ≤
      lowerNormConst D u * (nfAll ((D.fm u).lam D.R.m) (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (g τ))) p)
        (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (g τ))) p)).re := by
  classical
  have hI' : ∀ τ, Br.Interlace (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) :=
    fun τ => (interlace_iff _ _ (Nm_succ D.R)).1 (interlaceTr D u hI τ)
  have hS : ∀ τ, SameShift (lamTr D u τ) (sgTr D u τ) := fun τ => sameShiftTr D u τ (interlaceTr D u hI τ)
  have hT : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  rw [lc_nfAll_sg, lc_nfAll_lam]
  unfold brTen
  rw [lc_frame (Nm_succ D.R).symm (lamTr D u) (sgTr D u) hI' hS g (sqrtT D u) p, lc_nfAll_smul]
  set q := blk (fun τ => sqAct ℂ _ (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R).symm.symm (g τ) *
    Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ _ (sqrtT D u))) p with hq
  have hqm : q ∈ CSpan (lamTr D u) := lc_blk_sqAct_mem _ _ p (lc_cspan_lam (D := D) (u := u) ▸ hp)
  have hc : (∏ τ, (((sqrtT D u ^ Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ) : ℂˣ) : ℂ))⁻¹) *
      star (∏ τ, (((sqrtT D u ^ Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ) : ℂˣ) : ℂ))⁻¹) =
      ((∏ τ, ((D.mem u).A.T : ℝ) ^ (-(Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ))) : ℝ) : ℂ) := by
    rw [star_prod, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun τ _ => lc_sqrt_norm _ hT _
  rw [hc, Complex.re_ofReal_mul]
  have key := lc_brTen_le (Nm_succ D.R).symm (lamTr D u) (sgTr D u) hI' hS q hqm
  have hTp : 0 ≤ ∏ τ, ((D.mem u).A.T : ℝ) ^ (-(Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ))) :=
    Finset.prod_nonneg fun τ _ => zpow_nonneg hT.le _
  unfold lowerNormConst
  rw [Finset.prod_mul_distrib, mul_assoc]
  exact mul_le_mul_of_nonneg_left key hTp

theorem lowerNorm_le {coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)}
    {gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ}
    (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) :
    ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re ≤ lowerNormConst D u * valNormAt D u φ := by
  obtain ⟨hz, P, rfl, rfl, hP⟩ := h
  rw [P.re_petersson_self_eq_sum_coord w _ (hz φ hφ), valNormAt, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [P.Pt_eq w φ hφ c, P.ipV_co w c φ hφ, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  have e : blk (fun τ => ⇑(P.br τ)) = brTen D u := by
    unfold brTen
    simp only [hP]
  rw [e]
  exact lc_member_le P.interlace (P.gP w c) _ (P.coM_mem w c φ hφ)

end LcRec

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL

section LcLog

open Formalism.MainNotions.product_first_zeroth_parts

variable {D : Formalism.BasicNotions.D7} {u : D.what₂.Word}

theorem lowerNormConst_eq_exp (hI : (D.fm u).SgInterlace) :
    lowerNormConst D u = Real.exp (∑ τ, (-(Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ) : ℝ) * Real.log ((D.mem u).A.T : ℝ) +
      (2 * Real.log |((cBr (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) : ℤ) : ℝ)| +
        Real.log (kapBr ℝ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ))))) := by
  have hT : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  rw [Real.exp_sum]
  unfold lowerNormConst
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hI' : Br.Interlace (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) :=
    (interlace_iff _ _ (Nm_succ D.R)).1 (interlaceTr D u hI τ)
  have hS := sameShiftTr D u τ (interlaceTr D u hI τ)
  have hc : ((cBr (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) : ℤ) : ℝ) ≠ 0 := by exact_mod_cast cBr_ne_zero _ _ _ hI'
  have hk := nm_kapR_pos _ _ _ hI' hS
  rw [Real.exp_add, Real.exp_add, Real.exp_log hk, two_mul, Real.exp_add, Real.exp_log (abs_pos.mpr hc), abs_mul_abs_self,
    mul_comm (-(Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ) : ℝ)), ← Real.rpow_def_of_pos hT]
  rw [show (-(Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ) : ℝ)) = ((-(Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ)) : ℤ) : ℝ) by push_cast; ring,
    Real.rpow_intCast]
  ring

theorem lowerNorm_log {coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)}
    {gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ}
    (h : LowerTieAt D u coM gP) (w : D.what₂.places.Pl) (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m)
    (hpos : 0 < ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re) :
    Real.log ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re ≤
      (∑ τ, (-(Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ) : ℝ) * Real.log ((D.mem u).A.T : ℝ) +
        (2 * Real.log |((cBr (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) : ℤ) : ℝ)| +
          Real.log (kapBr ℝ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ))))) + Real.log (valNormAt D u φ) := by
  have hI : (D.fm u).SgInterlace := by obtain ⟨-, P, -, -, -⟩ := h; exact P.interlace
  have hle := lowerNorm_le h w φ hφ
  have hK : 0 < lowerNormConst D u := by rw [lowerNormConst_eq_exp hI]; exact Real.exp_pos _
  have hv : 0 < valNormAt D u φ := by
    by_contra hn
    have h2 : lowerNormConst D u * valNormAt D u φ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK.le (not_lt.mp hn)
    linarith
  calc Real.log ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re ≤ Real.log (lowerNormConst D u * valNormAt D u φ) :=
        Real.log_le_log hpos hle
    _ = _ := by rw [Real.log_mul hK.ne' hv.ne', lowerNormConst_eq_exp hI, Real.log_exp]

end LcLog

end Formalism.L2.Ker
