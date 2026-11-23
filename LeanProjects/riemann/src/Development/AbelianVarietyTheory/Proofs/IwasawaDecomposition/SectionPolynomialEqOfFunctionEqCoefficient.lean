import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PolyId

theorem shiftOf_lamT_succ {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (i : ℕ)
    (hi : i < R.m) (τ : ι) : shiftOf (Col2.lamT hc (i + 1)) τ = -C.sDiv i τ := by
  have hN : R.N (i + 1) = R.k + (i + 1) * (R.t + 1) := rfl
  have h1 : 1 ≤ (i + 1) * (R.t + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpos : 0 < R.N (i + 1) := by rw [hN]; omega
  have hk : ¬ (R.N (i + 1) - 1 < R.k) := by rw [hN]; omega
  have hq : (R.N (i + 1) - 1 - R.k) / (R.t + 1) = i := by
    rw [hN]
    have hm : (i + 1) * (R.t + 1) = i * (R.t + 1) + R.t + 1 := by ring
    rw [hm, show R.k + (i * (R.t + 1) + R.t + 1) - 1 - R.k = R.t + i * (R.t + 1) by omega,
      Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]
  have h2 := C.sDiv_eq i hi τ
  obtain ⟨c, hc'⟩ := R.t_odd
  have hcq : (R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc'
  have e2 : (R.t + 1) / 2 = c + 1 := by omega
  simp only [shiftOf, DomWeight.detShift, dif_pos hpos, Col2.lamT, Col2.shW, Examples₂.lamOf, dif_pos (show i + 1 ≤ R.m by omega), Examples₂.wtQ, dif_neg hk]
  simp only [hq, e2]
  have hw : -wG R ((hc τ).e ⟨i, hi⟩) (i + 1) = ((-C.sDiv i τ + ((i + 1) * (c + 1) : ℕ) : ℤ) : ℚ) := by
    push_cast
    rw [h2]
    simp only [wG, sExp, Ranks.N, Nat.add_sub_cancel]
    push_cast
    rw [hcq]
    ring
  rw [hw, Int.floor_intCast]
  push_cast
  ring

theorem secC_eq_of_evC_eq_evV : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (z : VV B.LL (lamT (B.hcW u) (i + 1))) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = evV B.fields.emb (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (lamT (B.hcW u) (i + 1)) B.embLL z → ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL)) = (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) := by
  intro B X I hOk hP l Z Qp O hStd u μ i hi z v' h
  have hfun : fnOf (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb))
      (shiftOf (Col2.lamT (B.hcW u) (i + 1))) 1
      (MvPolynomial.map B.embLL ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL))) =
      fnOf (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb))
      (shiftOf (Col2.lamT (B.hcW u) (i + 1))) 1 (MvPolynomial.map B.embLL z.1) := by
    rw [← evV_apply]
    rw [← h]
    refine Eq.trans ?_ (evC_sec O u μ (i + 1) v').symm
    funext y
    have hfr := hStd.frm u μ (i + 1) y
    show _ = (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(((I.rec7 l Z).chTw u μ).sDiv i τ))) *
      GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL))) ((O u μ).frm (i + 1) y)
    rw [hfr]
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, GL3Theta.evFr]
    congr 1
    · refine Finset.prod_congr rfl fun τ _ => ?_
      have hs : shiftOf (Col2.lamT (B.hcW u) (i + 1)) τ = -((I.rec7 l Z).chTw u μ).sDiv i τ :=
        shiftOf_lamT_succ ((I.rec7 l Z).chTw u μ) i hi τ
      rw [hs, Pi.one_apply, Matrix.one_mul]
      rfl
    · simp only [Pi.one_apply, Matrix.one_mul]
      rfl
  have h2 := fnOf_injective _ _ 1 (fun _ => by simp) (stdFrC (n := B.R.N (i + 1)) (embAt B.embLL B.fields.emb)) hfun
  exact MvPolynomial.map_injective _ B.embLL.injective h2

end GlobalTheory.Mem.Col2.PolyId
