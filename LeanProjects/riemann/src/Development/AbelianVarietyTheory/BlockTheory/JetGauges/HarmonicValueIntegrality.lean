import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramifiedOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarmonicValueIntegrality

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Poly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def IsIntHarm (Dw : Datum H) (T : CDVR) (n : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr) : Prop :=
  (∀ m, P.coeff m ∈ (algebraMap T.V T.Fr).range) ∧
    ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
      InPsi H τ →
        ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
          (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

def chartVal {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ}
    (P : MvPolynomial (LtN Dw n) T.Fr) (f : PS T.Fr n (chD C.ch)) : T.Fr :=
  letI := io.toAlgebra
  nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P

omit [StarRing (𝓞 E)] in

theorem isIntHarm_of_mem_FFV (T : CDVR) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr)
    (hP : P ∈ FFV (Dw := Dw) T a n) : IsIntHarm Dw T n P := by
  refine ⟨hP.2, fun τ i i' hτ => ?_⟩
  have h := hP.1.1
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h
  have h1 := h τ hτ i i'
  simpa [lap, Matrix.one_apply, LinearMap.sum_apply] using h1

omit [StarRing (𝓞 E)] in

example (T : CDVR) (n : ℕ) (ℓ : LtN Dw n) : IsIntHarm Dw T n (MvPolynomial.X ℓ) := by
  classical
  refine ⟨fun m => ?_, fun τ i i' _ => ?_⟩
  · rw [MvPolynomial.coeff_X]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;> simp

end Poly

def HarmonicValueIntegral : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → y.IsAlg →
      (∀ p ∈ (D.host.small ∪ {D.host.q, D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ), (p : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
      ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io y) (k n : ℕ)
        (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), IsIntHarm (T.Q.Dw j) Tc n P →
        ∀ f : PS Tc.Fr n (chD C.ch), IsIntPS Tc f → 0 ≤ nval Tc.V e (chartVal C k P f)

example (hS : HarmonicValueIntegral) (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    [StarRing (𝓞 D.host.E)] (hst : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a)
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (ho : OverLa la Tc.V io e) (hy : y.IsAlg)
    (hp : ∀ p ∈ (D.host.small ∪ {D.host.q, D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ), (p : 𝓞 T.Q.c.F) ∉ la.asIdeal)
    (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io y) (k n : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    0 ≤ nuLocC C e k a n :=
  le_iInf fun P => le_iInf fun hP => le_iInf fun f => le_iInf fun hf =>
    hS D T h j hj hst Tc io y e la ho hy hp C k n P (isIntHarm_of_mem_FFV Tc a n P hP) f hf

end GlobalTheory.IndefiniteRowSideFullHecke.HarmonicValueIntegrality
