import Mathlib
import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.ElevenLe
import Formalism.SharpRestriction.Divisibility.SlopeExcess.FamilyStatementOfScaledLemmas
import Formalism.SharpRestriction.Divisibility.HookProducts.NormAtEqSqrtMajAt
import Formalism.SharpRestriction.Divisibility.HookProducts.LambdaZeroLeFourB

open Module NumberField

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.MainNotions

def FunSharpRec : Prop :=
  ∀ (D : D7) (X0 : BaseLevelRowSide D) (Y : DivX D) {Bs : DefBase D.what₂.LL} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1}
    {Sp : SPer Dc} {N : IndefNum Bs} (P : IndefCoreR Df0 Df1 Dc Sp N)
    (eRR0 : (Fin P.base.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X0.s.RR.V),
    HLatTie X0.s.RR P.base.RR P.base.XE eRR0 →
    (∀ e : D.what₂.LL →+* ℂ, Y.kapR e = P.cols.κ (InfinitePlace.mk e)) →
    ∀ C : ℝ, C * ((D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ)) ≤ 1 / 3 →
    LemmaT D X0 C →
    D.div.RR.muMax + meanE D (fun e => Real.log (Y.kapR e)) ≤ N.hh + 14 * lam0 D

theorem funSharpRec : FunSharpRec := by
  intro D X0 Y Bs Df0 Df1 Dc Sp N P eRR0 hRR hkap C hδ hT
  have hmu : X0.principalHermitianLattice.muMax = P.base.muMaxRR := by
    unfold Formalism.BasicNotions.BaseLevelRowSide.principalHermitianLattice Formalism.L2.Indef.IndefData.muMaxRR
    exact (Formalism.MainNotions.DIV.HookProducts.FunSharp.muMax_tie X0.s.RR P.base.RR P.base.XE eRR0 hRR.lat hRR.metric).symm
  have hf0 : P.base.muMaxRR ≤ N.hh - meanLog P.base.κ := P.extra.fun0
  have h1 := (hT hδ (N.hh - meanLog P.base.κ) (hmu ▸ hf0)).1
  have hκ : meanE D (fun e => Real.log (Y.kapR e)) = meanLog P.base.κ := by
    rw [P.extra.level.2.1]
    exact meanEmb_eq_meanLog P.cols.κ _ (fun σ => by rw [hkap σ])
  linarith

structure FunDat (D : D7) (X0 : BaseLevelRowSide D) where
  Bs : DefBase D.what₂.LL
  Df0 : DefSide Bs
  Df1 : DefSide Bs
  Dc : DefCols Df1
  Sp : SPer Dc
  Z : IndefScale Bs
  Cp : ℝ
  CHp : ℝ
  P : IndefCoreR Df0 Df1 Dc Sp (Z.num Cp CHp)
  eRR0 : (Fin P.base.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X0.s.RR.V

def FunTies {eps : ℝ} (Fm : FamP eps) (CHf : List ℝ → ℝ) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x)
    (T : FunDat (Fm.D x i) (Fm.ex x hx i).p0) : Prop :=
  T.Z.x = (Fm.L x i).sc.x ∧ T.Z.b = (Fm.L x i).sc.b ∧ T.CHp ≤ CHf Fm.cOut ∧
    HLatTie (Fm.ex x hx i).p0.s.RR T.P.base.RR T.P.base.XE T.eRR0 ∧
    ∀ e : (Fm.D x i).what₂.LL →+* ℂ, (Fm.X x i).kapR e = T.P.cols.κ (InfinitePlace.mk e)

def sharpFunctionalExponent (CHf : List ℝ → ℝ) : List ℝ → ℝ := fun l => max (CHf l) 1 + 1

def FunSharpFam : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (CHf : List ℝ → ℝ)
    (Pt : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, FunDat (Fm.D x i) (Fm.ex x hx i).p0),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Pt.1 ≤ x) (i : Fm.Ix x), FunTies Fm CHf x hx i (Pt.2 x hx h i)) →
    Formalism.MainNotions.PrimeDegreeVariant.SlopeLossFamily Fm →
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ sharpFunctionalExponent CHf Fm.cOut * (Fm.L x i).sc.b

theorem funSharpFam : FunSharpFam := by
  rintro eps Fm CHf Pt ⟨x0, hpt⟩ ⟨C, -, x5, h5⟩
  refine ⟨max (max x0 x5) (max Pt.1 56), fun x hx hx1 i => ?_⟩
  have g0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have g5 : x5 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have gP : Pt.1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have g56 : (56 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hZx, hZb, hCH, hRR, hkap⟩ := hpt x g0 hx1 gP i
  obtain ⟨hδ, hT⟩ := h5 x g5 hx1 i
  have hrec := funSharpRec (Fm.D x i) (Fm.ex x hx1 i).p0 (Fm.X x i) (Pt.2 x hx1 gP i).P (Pt.2 x hx1 gP i).eRR0 hRR hkap C hδ hT
  have hhh : ((Pt.2 x hx1 gP i).Z.num (Pt.2 x hx1 gP i).Cp (Pt.2 x hx1 gP i).CHp).hh =
      (Pt.2 x hx1 gP i).Z.x ^ (Pt.2 x hx1 gP i).CHp * (Pt.2 x hx1 gP i).Z.b := rfl
  rw [hhh, hZx, hZb] at hrec
  have hlam := Formalism.MainNotions.DIV.HookProducts.FunSharp.lambda_zero_le_four_b (Fm.L x i) (Fm.sizes x hx1 i)
  have hsc : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  rw [hsc] at hrec ⊢
  set B := (Fm.L x i).sc.b with hB
  have hB1 : 1 ≤ B := by
    rw [hB]; unfold Scale.b
    exact Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  set E := max (CHf Fm.cOut) 1 with hE
  have hx1' : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have e1 : x ^ (Pt.2 x hx1 gP i).CHp ≤ x ^ E := Real.rpow_le_rpow_of_exponent_le hx1' (hCH.trans (le_max_left _ _))
  have e2 : x ≤ x ^ E := by
    have := Real.rpow_le_rpow_of_exponent_le hx1' (le_max_right (CHf Fm.cOut) 1)
    rwa [Real.rpow_one] at this
  have e3 : x ^ (sharpFunctionalExponent CHf Fm.cOut) = x * x ^ E := by
    unfold sharpFunctionalExponent; rw [← hE, Real.rpow_add hx0, Real.rpow_one, mul_comm]
  rw [e3]
  have hEpos : 0 ≤ x ^ E * B := by positivity
  have t1 : x ^ (Pt.2 x hx1 gP i).CHp * B ≤ x ^ E * B := mul_le_mul_of_nonneg_right e1 (by linarith)
  have t2 : 56 * B ≤ x ^ E * B := by
    have : 56 * B ≤ x * B := mul_le_mul_of_nonneg_right g56 (by linarith)
    have : x * B ≤ x ^ E * B := mul_le_mul_of_nonneg_right e2 (by linarith)
    linarith
  have t3 : 2 * (x ^ E * B) ≤ x * (x ^ E * B) := mul_le_mul_of_nonneg_right (by linarith) hEpos
  nlinarith

theorem sharp_functional_bound_family {eps : ℝ} (Fm : FamP eps) (CHf : List ℝ → ℝ)
    (Pt : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, FunDat (Fm.D x i) (Fm.ex x hx i).p0)
    (hT : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Pt.1 ≤ x) (i : Fm.Ix x), FunTies Fm CHf x hx i (Pt.2 x hx h i))
    (YF : Formalism.MainNotions.PrimeDegreeVariant.ProvF Fm) (hA : Formalism.MainNotions.PrimeDegreeVariant.AdmFB Fm YF) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ sharpFunctionalExponent CHf Fm.cOut * (Fm.L x i).sc.b :=
  funSharpFam Fm CHf Pt hT (Formalism.MainNotions.PrimeDegreeVariant.familyLemmaFive_of_large Fm (Formalism.MainNotions.DIV.Proofs.family_statement_of_scaled_lemmas Fm YF hA).2.2)

end Formalism.MainNotions.DIV.HookProducts
