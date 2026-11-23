import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LamSpread

open Classical in

def sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (b : E →+* ℂ) : ℕ := ∑ i : Fin (Dw.mult b), a (b, i)

theorem le_sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (b : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult b) : a (b, i) ≤ sumA Dw a b :=
  Finset.single_le_sum (f := fun i : Fin (Dw.mult b) => a (b, i)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨i, hi⟩ : Fin (Dw.mult b)))

theorem spread_le_sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (hr : 0 < r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (k : U.Comp) (τ : (U.X k).Ψ) :
    (U.X k).spread (laU U a n k) τ ≤ (sumA Dw a (Function.invFun (relab c σ) τ.1) : ℝ) +
      sumA Dw a (Function.invFun (relab c σ) (conjEmb τ.1)) + n := by
  have hsurj : Function.Surjective (relab (E := E) c σ) :=
    Finite.injective_iff_surjective.1 (GlobalTheory.AllWt.relab_injective σ)
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  have hrr := hU.1
  obtain ⟨ρ, hρ⟩ := hsurj τ.1
  have hρΨ : ρ (H.rt : E) = H.rt0 := by
    by_contra hn
    have h3 : relab c σ (conjEmb ρ) (H.rt : E) = H.rt0 := by
      have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
      exact (congrArg σ (Subtype.ext (GlobalTheory.AllWt.conj_mem hn))).trans hσ0
    rw [GlobalTheory.AllWt.relab_conj, hρ] at h3
    exact GlobalTheory.AllWt.conj_not_mem ⟨τ.1, (hΨ _).1 τ.2⟩ h3
  have e1 : Function.invFun (relab c σ) τ.1 = ρ := by
    rw [← hρ]; exact Function.leftInverse_invFun (GlobalTheory.AllWt.relab_injective σ) ρ
  have e2 : Function.invFun (relab c σ) (conjEmb τ.1) = conjEmb ρ := by
    rw [← hρ, ← GlobalTheory.AllWt.relab_conj]; exact Function.leftInverse_invFun (GlobalTheory.AllWt.relab_injective σ) _
  have m1 : Dw.mult ρ = Dw.p := by rw [Datum.mult, if_pos hρΨ]
  have m2 : Dw.mult (conjEmb ρ) = Dw.q := by rw [Datum.mult, if_neg (GlobalTheory.AllWt.conj_not_mem ⟨ρ, hρΨ⟩)]
  rw [e1, e2]
  have hn : ((n / 2 : ℕ) : ℝ) + ((n / 2 : ℕ) : ℝ) ≤ n := by
    have : n / 2 + n / 2 ≤ n := by omega
    exact_mod_cast this
  have key : ∀ i : Fin r, -((sumA Dw a (conjEmb ρ) : ℤ) + ((n / 2 : ℕ) : ℤ)) ≤ laU U a n k τ i ∧
      laU U a n k τ i ≤ (sumA Dw a ρ : ℤ) + ((n / 2 : ℕ) : ℤ) := by
    intro i
    have hi' := i.isLt
    unfold laU
    rw [e1, e2]
    split_ifs with hi
    · have := le_sumA Dw a ρ ((i : ℕ) - (U.X k).p0) (by rw [m1]; omega)
      constructor <;> omega
    · have := le_sumA Dw a (conjEmb ρ) ((U.X k).p0 - 1 - (i : ℕ)) (by rw [m2]; omega)
      constructor <;> omega
  refine (GlobalTheory.WtSizes.spread_le hr _ ((sumA Dw a ρ : ℝ) + ((n / 2 : ℕ) : ℝ))
    ((sumA Dw a (conjEmb ρ) : ℝ) + ((n / 2 : ℕ) : ℝ)) (fun i => ?_) (fun i => ?_)).trans (by linarith)
  · have h1 := (Int.cast_le (R := ℝ)).2 (key i).2
    rwa [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
  · exact_mod_cast (key i).1

theorem sum_spread_laU_le : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : (U σ).Comp), (∑ τ, ((U σ).X k).spread (laU (U σ) a n k) τ) ≤ ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) := by
  intro D j H Dw l Xo c U dict hL σ hσ a n k
  have hU := hL.unf σ hσ
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hsurj : Function.Surjective (relab (E := D.host.E) c σ) :=
    Finite.injective_iff_surjective.1 (GlobalTheory.AllWt.relab_injective σ)
  have hgb : Function.Bijective (Function.invFun (relab c σ)) :=
    Finite.injective_iff_bijective.1 (Function.LeftInverse.injective (Function.rightInverse_invFun hsurj))
  refine (Finset.sum_le_sum fun τ _ => spread_le_sumA (U σ) hσ hU hr a n k τ).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (U σ).X k),
    nsmul_eq_mul]
  have h1 : ∑ τ : ((U σ).X k).Ψ, ((sumA Dw a (Function.invFun (relab c σ) τ.1) : ℝ) +
      sumA Dw a (Function.invFun (relab c σ) (conjEmb τ.1))) ≤ absA Dw a := by
    have := GlobalTheory.WtSizes.sum_cm_le ((U σ).X k) (fun b => sumA Dw a (Function.invFun (relab c σ) b))
    rw [hgb.sum_comp (fun b => sumA Dw a b)] at this
    show _ ≤ ((∑ b, sumA Dw a b : ℕ) : ℝ)
    exact_mod_cast this
  have h2 : (fdeg D.host.E : ℝ) * n ≤ ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) := by
    have : fdeg D.host.E * n ≤ fdeg D.host.E * D.R.r * n :=
      Nat.mul_le_mul_right n (Nat.le_mul_of_pos_right _ hr)
    exact_mod_cast this
  linarith

end GlobalTheory.LamSpread
