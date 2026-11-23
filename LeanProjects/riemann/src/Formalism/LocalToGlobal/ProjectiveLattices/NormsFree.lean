import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Formalism.LocalToGlobal.ProjectiveLattices.PtFree

noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

section Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)

theorem supE_add_le (P Q : FDSec X) : supE X la (P + Q) ≤ supE X la P + supE X la Q := by
  unfold supE
  refine iSup_le fun p => ?_
  have key : (X p.1).pnorm (la p.1) ((P + Q) p.1) p.2 ≤
      (X p.1).pnorm (la p.1) (P p.1) p.2 + (X p.1).pnorm (la p.1) (Q p.1) p.2 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _)
      (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact ((ENNReal.ofReal_le_ofReal key).trans ENNReal.ofReal_add_le).trans
    (add_le_add (le_iSup_of_le p le_rfl) (le_iSup_of_le p le_rfl))

theorem supE_smul (a : ℂ) (P : FDSec X) : supE X la (a • P) = ENNReal.ofReal ‖a‖ * supE X la P := by
  unfold supE
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg a)]
  congr 1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

theorem supE_ne_top [Fintype Comp] {P : FDSec X} (h : P ∈ holSub X la) : supE X la P ≠ ⊤ := by
  unfold holSub at h
  induction h using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    unfold supE
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ c, |C c|))
      (iSup_le fun p => ENNReal.ofReal_le_ofReal ?_)
    calc _ ≤ C p.1 := hC p.1 p.2.1 p.2.2
      _ ≤ |C p.1| := le_abs_self _
      _ ≤ ∑ c, |C c| :=
        Finset.single_le_sum (f := fun c => |C c|) (fun c _ => abs_nonneg _) (Finset.mem_univ _)
  | zero =>
    unfold supE
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 0)) (iSup_le fun p => ?_)
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    simp
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
  split_ifs with hσ
  · exact hσ
  · have hx : ((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ) ^ 2 + ((H.d : ℕ) : c.F) = 0 := by
      apply Subtype.ext
      have e : (((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ : c.F) : ℂ) = H.rt0 := rfl
      push_cast [e]
      rw [H.sqrt_neg_disc_sq]
      ring
    have hy : (σ ((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ)) ^ 2 = H.rt0 ^ 2 := by
      have h0 := congrArg σ hx
      rw [map_add, map_pow, map_natCast, map_zero] at h0
      rw [H.sqrt_neg_disc_sq]
      linear_combination h0
    have hre : H.rt0.re = 0 := by
      have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
      have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
      simp [sq] at h1 h2
      have hd : (0 : ℝ) < H.d := Nat.cast_pos.mpr H.d_prime.pos
      have e2 : H.rt0.re * H.rt0.im = 0 := by linear_combination h2 / 2
      have e3 : H.rt0.re ^ 4 = -(H.d * H.rt0.re ^ 2) := by
        linear_combination (H.rt0.re ^ 2) * h1 + (H.rt0.re * H.rt0.im) * e2
      have h4 : H.rt0.re ^ 4 ≤ 0 := by
        rw [e3]
        exact neg_nonpos.mpr (mul_nonneg hd.le (sq_nonneg _))
      have h5 : H.rt0.re ^ 4 = 0 := le_antisymm h4 (by positivity)
      exact (pow_eq_zero_iff (by norm_num)).mp h5
    have hconj : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
      apply Complex.ext <;> simp [hre]
    unfold GoodEmb at hσ ⊢
    simp only [RingHom.comp_apply] at hσ ⊢
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with h | h
    · exact absurd h hσ
    · rw [h, map_neg, hconj, neg_neg]

theorem IsNormOn.of_goodOf {C : Submodule c.F (Rul Xo c)} {σ : c.F →+* ℂ} {N : Rul Xo c → ℝ}
    (h : IsNormOn C (goodOf c σ) N) : IsNormOn C σ N := by
  exact ⟨h.nonneg, h.defin, fun a f hf => by rw [h.smul a f hf, norm_goodOf], h.add⟩

def lieFac (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieFac_pos (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : 0 < lieFac Dw x a := by
  unfold lieFac
  exact Real.exp_pos _

def supC (x : ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  lieFac Dw x a * supN (U σ).X (laU (U σ) a n) (rdU (U σ) f)

def SupDef : Prop :=
  ∀ a n, Dom a n → ∀ σ, GoodEmb c σ → ∀ f ∈ cusp Xo c U a n, supN (U σ).X (laU (U σ) a n) (rdU (U σ) f) = 0 → f = 0

variable {Xo c U}

theorem supE_cusp_ne_top {a n} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) :
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ := by
  unfold cusp at hf
  have h1 := (Submodule.mem_inf.mp hf).2
  have h2 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h1 σ) hσ
  exact supE_ne_top _ _ (Submodule.mem_comap.mp h2)

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

variable {U} {σ : c.F →+* ℂ}

theorem rdC_continuousOn (hU : IsUnf (U σ)) {a n} (hd : Dom a n) (f : cusp Xo c U a n) (k : (U σ).Comp) :
    ContinuousOn (rdC U σ a n f k) ((U σ).X k).dom := by
  have hf : (f : Rul Xo c) ∈ sec Xo c a n := by
    have h0 := f.2
    unfold cusp at h0
    exact (Submodule.mem_inf.mp h0).1
  exact (hU.2.2.2.2.1 a n hd f hf k).1.continuousOn

end Formalism.L2.PjFree
