import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

def PlaceIntegralUnramified : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la),
      (∀ p ∈ ({2, D.host.q, D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ),
        ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
      0 ≤ vAtV y f

def PlaceBoundOwnPrime : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la),
      ((D.host.pde : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la (D.host.pde : T.Q.c.F) : ℤ) : ℝ) *
          ((DF w : ℝ) + 2 * D.R.f * D.R.r * w.n))) : ℝ) : EReal) ≤
        vAtV y f

def PlaceBoundTwo : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la),
      (((2 : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la ((2 : ℕ) : T.Q.c.F) : ℤ) : ℝ) *
          ((D.R.e : ℝ) + 1 - (2 : ℝ)⁻¹ ^ D.R.e) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤
        vAtV y f

def PlaceBoundOddRamified : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la) (p : ℕ), p ∈ ({D.host.q, D.host.d} : Finset ℕ) →
      ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * (1 / 2) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤
        vAtV y f

def PlaceBoundSplitPrime : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la) (i : Fin 2) (πE : 𝓞 D.host.E) (τ : D.host.E →+* ℂ),
      InPsi T.Q.H τ → πE * T.Q.H.bar πE = (D.host.g i : 𝓞 D.host.E) →
      T.Q.l.Mb ≤ Ideal.span {T.Q.H.bar πE} → ((D.host.g i : 𝓞 T.Q.c.F) ∈ la.asIdeal) → D.host.g i ≠ D.host.q →
      (((-(((vLa la (embK T.Q.c τ πE) : ℤ) : ℝ) * ((∑ t, ∑ k, w.aP t k : ℕ) : ℝ) +
          ((vLa la (embK T.Q.c τ (T.Q.H.bar πE)) : ℤ) : ℝ) * ((∑ t, ∑ k, w.aM t k : ℕ) : ℝ))) : ℝ) : EReal) ≤
        vAtV y f

def WeightAssemblyClause : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (S : Scal (recB h.toLawsCore)) (wL : WeightFamilies.Wt D j),
    S.sW ≠ 0 → LastPos (T.Q.Dw j) (wtA wL) →
    (∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la) (g : T.R j), g ∈ T.th j wL →
      (((-(((vLa la ((S.sW : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ))) : ℝ) : EReal) ≤ vAtV y g) →
    (recPJ h j hj).WWc S.sW wL ≤ (recB h.toLawsCore).Mlat j wL

end ReciprocityTheory.ChartRestriction.G.PullbackSections
