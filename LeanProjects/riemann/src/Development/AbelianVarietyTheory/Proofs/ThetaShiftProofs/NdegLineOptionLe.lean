import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CoeffMemOfLoc
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmNumbersOfGood

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

private theorem prod_option_eq_prod_isSome_of_none_eq_one {V M : Type} [Fintype V] [CommMonoid M] {g : ℕ} (k : V → Option (Fin g))
    (F : V → Option (Fin g) → M) (h1 : ∀ v, F v none = 1) :
    ∏ v, F v (k v) = ∏ w : {v // (k v).isSome = true}, F w.1 (some ((k w.1).get w.2)) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v => (k v).isSome = true) (fun v => F v (k v))]
  have h2 : ∏ w : {v // ¬ (k v).isSome = true}, F w.1 (k w.1) = 1 := by
    refine Finset.prod_eq_one (fun w _ => ?_)
    have hw : k w.1 = none := by simpa using w.2
    rw [hw, h1]
  rw [h2, _root_.mul_one]
  refine Finset.prod_congr rfl (fun w _ => ?_)
  rw [Option.some_get]

private theorem mLine_prodPow_option_elim_eq_prodPow_isSome {K : Type} [Field K] [NumberField K] {g : ℕ} (ℓ : Fin g → MLine K)
    {V : Type} [Fintype V] (k : V → Option (Fin g)) (mu : V → ℕ) :
    MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu =
      MLine.prodPow (fun w : {v // (k v).isSome = true} => ℓ ((k w.1).get w.2)) (fun w => mu w.1) := by
  unfold MLine.prodPow
  congr 1
  · exact prod_option_eq_prod_isSome_of_none_eq_one k (fun v o => (o.elim MLine.one ℓ).I ^ mu v) (fun v => by simp [MLine.one])
  · funext σ
    exact prod_option_eq_prod_isSome_of_none_eq_one k (fun v o => (o.elim MLine.one ℓ).n σ ^ mu v) (fun v => by simp [MLine.one])

theorem ndeg_line_option_le {K : Type} [Field K] [NumberField K] {g : ℕ} (abelian₂ : MLine K) (ℓ : Fin g → MLine K)
    (de : MLine K) (La logOm : ℝ) {V : Type} [Fintype V] (k : V → Option (Fin g)) (mu : V → ℕ) (n G : ℕ)
    (h : CMNumbers0 abelian₂ ℓ de La logOm) (hG : g ≤ G) :
    ((de.pow n).tensor (MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu).dual).Good ∧
    ((de.pow n).tensor (MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu).dual).ndeg ≤
      (pDeg logOm + (1 / 2) * Real.log La) * (((∑ v, mu v : ℕ) : ℝ) + ((G * n : ℕ) : ℝ)) := by
  rw [mLine_prodPow_option_elim_eq_prodPow_isSome ℓ k mu]
  have hN := degree_norm_base K g abelian₂ ℓ de La logOm {v // (k v).isSome = true} (fun w => (k w.1).get w.2)
    (fun w => mu w.1) n h
  have hLa : 1 ≤ La := h.2.2.2.1
  have hP : 0 ≤ pDeg logOm + (1 / 2) * Real.log La := by
    have h0 := Real.log_nonneg hLa
    have h1 := abs_nonneg logOm
    unfold pDeg
    linarith
  refine ⟨hN.1, le_trans hN.2 (mul_le_mul_of_nonneg_left ?_ hP)⟩
  have hs : ∑ w : {v // (k v).isSome = true}, (mu w.1 : ℝ) ≤ ∑ v, (mu v : ℝ) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun v => (k v).isSome = true) (fun v => (mu v : ℝ))]
    have h0 : 0 ≤ ∑ w : {v // ¬ (k v).isSome = true}, (mu w.1 : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    linarith
  have hgG : (g : ℝ) * n ≤ (G : ℝ) * n :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hG) (Nat.cast_nonneg n)
  push_cast
  linarith

theorem valLine_ndeg_le : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (logOm : ℝ) (mo : ArcLt Dw →₀ ℕ) (n : ℕ), 1 ≤ La → LamDegSt H logOm → (s.valLine mo n).Good ∧ (s.valLine mo n).ndeg ≤ (pDeg logOm + (1 / 2) * Real.log La) * (((∑ v, mo v : ℕ) : ℝ) + ((Module.finrank ℚ E / 2 * (Dw.p + Dw.q) * n : ℕ) : ℝ)) := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s logOm mo n hLa hdeg
  letI := H.starRing
  have hcm := cmNumbers_of_good hK E H l c (Dw.p - 1) (Dw.q - 1) (Module.finrank ℚ E / 2) s.toCMPart.obj La logOm
    (fun _ => rfl) s.good s.L s.L_good hLa hdeg
  have hg : a.D₀.P.g ≤ Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
    have h9 : a.D₀.P.g = Module.finrank ℚ E / 2 * (Dw.p - 1 + (Dw.q - 1)) := s.good.2.2.2.2.2.2.2.2.1
    rw [h9]
    apply Nat.mul_le_mul_left
    omega
  exact ndeg_line_option_le (K := K₁) s.LamL s.L.ℓ s.Tl.dual La logOm (fun v : ArcLt Dw => s.kind v.1 v.2.2) mo n
    (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) hcm hg

end GlobalTheory.ArcCM
