import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.VAddIntNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

section Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)

theorem supE_add_le (P Q : FDSec X) : supE X la (P + Q) ≤ supE X la P + supE X la Q := by
  unfold supE
  refine iSup_le fun p => ?_
  have h1 : (X p.1).pnorm (la p.1) ((P + Q) p.1) p.2 ≤
      (X p.1).pnorm (la p.1) (P p.1) p.2 + (X p.1).pnorm (la p.1) (Q p.1) p.2 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  calc ENNReal.ofReal ((X p.1).pnorm (la p.1) ((P + Q) p.1) p.2)
      ≤ ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2) +
          ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2) :=
        (ENNReal.ofReal_le_ofReal h1).trans ENNReal.ofReal_add_le
    _ ≤ (⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) +
          ⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2) :=
        add_le_add (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p)
          (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2)) p)

theorem supE_smul (a : ℂ) (P : FDSec X) : supE X la (a • P) = ENNReal.ofReal ‖a‖ * supE X la P := by
  unfold supE
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  show ‖a * P p.1 p.2‖ * _ = ‖a‖ * (‖P p.1 p.2‖ * _)
  rw [norm_mul]
  ring

theorem supE_ne_top [Fintype Comp] {P : FDSec X} (h : P ∈ holSub X la) : supE X la P ≠ ⊤ := by
  unfold holSub at h
  induction h using Submodule.span_induction with
  | mem P hP =>
    have hb : ∀ c, ∃ C : ℝ, ∀ x ∈ (X c).dom, (X c).pnorm (la c) (P c) x ≤ C := fun c => (hP c).1.2
    choose C hC using hb
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ c, |C c|))
      (iSup_le fun p => ENNReal.ofReal_le_ofReal ?_)
    calc (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ C p.1 := hC p.1 p.2 p.2.2
      _ ≤ |C p.1| := le_abs_self _
      _ ≤ ∑ c, |C c| := Finset.single_le_sum (fun c _ => abs_nonneg (C c)) (Finset.mem_univ _)
  | zero =>
    refine ne_top_of_le_ne_top ENNReal.zero_ne_top (iSup_le fun p => ?_)
    simp [ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm]
  | add P Q _ _ hP hQ =>
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hP, hQ⟩) (supE_add_le X la P Q)
  | smul a P _ hP =>
    rw [supE_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP

end Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

open Classical in

def goodOf (σ : c.F →+* ℂ) : c.F →+* ℂ := if GoodEmb c σ then σ else (starRingEnd ℂ).comp σ

theorem norm_goodOf (σ : c.F →+* ℂ) (x : c.F) : ‖goodOf c σ x‖ = ‖σ x‖ := by
  unfold goodOf
  split_ifs <;> simp

theorem goodEmb_goodOf (σ : c.F →+* ℂ) : GoodEmb c (goodOf c σ) := by
  unfold goodOf
  split_ifs with h
  · exact h
  · unfold GoodEmb at h ⊢
    set β := (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ with hβ
    have hβsq : β ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, hβ, ← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
    have hneg : β = -H.rt0 := by
      have hm : (β - H.rt0) * (β + H.rt0) = 0 := by
        rw [show (β - H.rt0) * (β + H.rt0) = β ^ 2 - H.rt0 ^ 2 by ring, hβsq, sub_self]
      rcases mul_eq_zero.mp hm with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) h
      · exact eq_neg_of_add_eq_zero_left h1
    have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h3 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h2 h3
    have hre : H.rt0.re = 0 := by
      rcases mul_eq_zero.mp (show H.rt0.re * H.rt0.im = 0 by nlinarith) with h4 | h4
      · exact h4
      · rw [h4] at h2
        exfalso
        nlinarith [mul_self_nonneg H.rt0.re]
    show starRingEnd ℂ β = H.rt0
    rw [hneg, map_neg]
    apply Complex.ext <;> simp [hre]

theorem IsNormOn.of_goodOf {C : Submodule c.F (Rul Xo c)} {σ : c.F →+* ℂ} {N : Rul Xo c → ℝ}
    (h : IsNormOn C (goodOf c σ) N) : IsNormOn C σ N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by simpa only [norm_goodOf] using h1, by simpa only [norm_goodOf] using h2,
    by simpa only [norm_goodOf] using h3, by simpa only [norm_goodOf] using h4⟩

def lieFac (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieFac_pos (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : 0 < lieFac Dw x a := Real.exp_pos _

def supC (x : ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  lieFac Dw x a * supN (U σ).X (laU (U σ) a n) (rdU (U σ) f)

def SupDef : Prop :=
  ∀ a n, Dom a n → ∀ σ, GoodEmb c σ → ∀ f ∈ cusp Xo c U a n, supN (U σ).X (laU (U σ) a n) (rdU (U σ) f) = 0 → f = 0

variable {Xo c U}

theorem supE_cusp_ne_top {a n} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) :
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ := by
  have h1 := (Submodule.mem_inf.mp hf).2
  have h2 := Submodule.mem_iInf _ |>.mp h1 σ
  have h3 := Submodule.mem_iInf _ |>.mp h2 hσ
  exact supE_ne_top (U σ).X (laU (U σ) a n) (Submodule.mem_comap.mp h3)

theorem isNormOn_supC (x : ℝ) (h : SupDef Xo c U) {a n} (hd : Dom a n) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) :
    IsNormOn (cusp Xo c U a n) σ (supC Xo c U x σ a n) where
  nonneg f _ := mul_nonneg (lieFac_pos _ _ _).le (supN_nonneg _ _ _)
  defin f hf h0 := h a n hd σ hσ f hf ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne')
  smul y f _ := by
    unfold supC supN
    rw [map_smulₛₗ, supE_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    ring
  add f hf g hg := by
    unfold supC supN
    rw [← mul_add, map_add, ← ENNReal.toReal_add (supE_cusp_ne_top hσ hf) (supE_cusp_ne_top hσ hg)]
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ?_ (supE_add_le _ _ _ _)) (lieFac_pos _ _ _).le
    exact ENNReal.add_ne_top.mpr ⟨supE_cusp_ne_top hσ hf, supE_cusp_ne_top hσ hg⟩

variable (U)

def rdC (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n →ₛₗ[σ] FDSec (U σ).X :=
  (rdU (U σ)).comp (cusp Xo c U a n).subtype

variable {D : D7} (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)

def CuspL2 : Prop := ∀ a n, Dom a n → JMemL2 V σ (rdC U σ a n) dict mu

open Classical in

def l2C (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : JMemL2 V σ (rdC U σ a n) dict mu) (f : Rul Xo c) : ℝ :=
  if hf : f ∈ cusp Xo c U a n then
    lieFac Dw x a * l2NormAlt V σ (rdC U σ a n) dict mu h ⟨f, hf⟩ else 0

def L2DefiniteCuspForms (h : CuspL2 U σ V dict mu) : Prop :=
  ∀ a n (hd : Dom a n), L2Definite V σ (rdC U σ a n) dict mu (h a n hd)

variable {U σ V dict mu}

theorem isNormOn_l2C (x₀ : ℝ) {h : CuspL2 U σ V dict mu} (h1 : L2DefiniteCuspForms U σ V dict mu h) {a n} (hd : Dom a n) :
    IsNormOn (cusp Xo c U a n) σ (l2C U σ V dict mu x₀ a n (h a n hd)) where
  nonneg f hf := by
    rw [l2C, dif_pos hf]; exact mul_nonneg (lieFac_pos _ _ _).le (l2Norm_nonneg_bis _ _ _ _ _ _ _)
  defin f hf h0 := by
    rw [l2C, dif_pos hf] at h0
    exact congrArg Subtype.val (h1 a n hd ⟨f, hf⟩ ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne'))
  smul x f hf := by
    rw [l2C, l2C, dif_pos hf, dif_pos (Submodule.smul_mem _ x hf)]
    have := l2Norm_smul_alt V σ (rdC U σ a n) dict mu (h a n hd) x ⟨f, hf⟩
    exact (congrArg (lieFac Dw x₀ a * ·) this).trans (by ring)
  add f hf g hg := by
    rw [l2C, l2C, l2C, dif_pos hf, dif_pos hg, dif_pos (Submodule.add_mem _ hf hg), ← mul_add]
    exact mul_le_mul_of_nonneg_left (L2Norm_add_le V σ (rdC U σ a n) dict mu (h a n hd) ⟨f, hf⟩ ⟨g, hg⟩)
      (lieFac_pos _ _ _).le

theorem l2C_le_supC (x : ℝ) (hσ : GoodEmb c σ) {a n} (h : JMemL2 V σ (rdC U σ a n) dict mu)
    (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom) (hm : MuUnit V dict mu) :
    ∀ f ∈ cusp Xo c U a n, l2C U σ V dict mu x a n h f ≤ supC Xo c U x σ a n f := by
  intro f hf
  unfold l2C supC
  rw [dif_pos hf]
  refine mul_le_mul_of_nonneg_left ?_ (lieFac_pos Dw x a).le
  exact L2Norm_le_sup_norm (V := V) (la := laU (U σ) a n) (rd := rdC U σ a n) (dict := dict) (mu := mu) (h := h)
    (hd := hd) (hm := hm) (f := ⟨f, hf⟩) (hfin := supE_cusp_ne_top hσ hf)

theorem rdC_continuousOn (hU : IsUnf (U σ)) {a n} (hd : Dom a n) (f : cusp Xo c U a n) (k : (U σ).Comp) :
    ContinuousOn (rdC U σ a n f k) ((U σ).X k).dom := by
  obtain ⟨-, -, -, -, hsec, -⟩ := hU
  have hf : (f : Rul Xo c) ∈ sec Xo c a n := (Submodule.mem_inf.mp f.2).1
  exact (hsec a n hd f hf k).1.continuousOn

end Formalism.L2.Pj
