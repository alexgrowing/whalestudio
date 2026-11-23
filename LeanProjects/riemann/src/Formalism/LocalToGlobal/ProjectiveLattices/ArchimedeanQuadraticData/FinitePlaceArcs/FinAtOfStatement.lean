import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.QbridgeOf
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ValLine
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.PolyFr
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCoreSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangeSt

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct

structure FinSite (K₁ : Type) [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁)) where
  K : Type
  [nf : NormedField K]
  [um : IsUltrametricDist K]
  [cs : CompleteSpace K]
  ι : K₁ →+* K
  r : ℝ
  r_pos : 0 < r
  r_lt : r < 1
  norm_ι : ∀ x : K₁, x ≠ 0 → ‖ι x‖ = r ^ ordAt w x
  K₀ : Subfield K
  res : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)
  S : Set K
  S_disc : ∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1
  S_dense : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - ρ| < ε
  S_units : ∀ t ∈ S, ∀ τ ∈ K₀, ‖τ‖ = 1 → t * τ ∈ S

attribute [instance] FinSite.nf FinSite.um FinSite.cs

def lcoeffPoly {ι K₁ : Type} [Field K₁] (P : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ) : MvPolynomial ι K₁ :=
  ∑ μ ∈ P.support, MvPolynomial.monomial μ ((P.coeff μ).coeff m)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def frameSub {K : Type} [Field K] (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (Y : ArcLt Dw → K) : ArcLt Dw → K :=
  fun x => (∑ l, Y ⟨x.1, x.2.1, l⟩ * Bm x.1 l x.2.2) * (lam x.1 x.2.2)⁻¹

variable {D : D7} {T : Core D} {j : ℕ}

def FinLocalAt {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)] (d : ArcDatumAt T j K₁) (w : HeightOneSpectrum (𝓞 K₁)) (n : ℕ)
    (vth : ℤ) (vη : ∀ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ) → ℤ) (m : ℕ) (Fs : Set (T.R j)) : Prop :=
  ∃ (Z : FinSite K₁ w) (γ : Z.K) (lam : ∀ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ) → Z.K)
    (A Bm : ∀ τ : D.host.E →+* ℂ, Matrix (Fin ((T.Q.Dw j).mult τ)) (Fin ((T.Q.Dw j).mult τ)) Z.K),
    (γ ≠ 0 ∧ ‖γ‖ = Z.r ^ vth) ∧
    (∀ τ k, lam τ k ≠ 0 ∧ ‖lam τ k‖ = Z.r ^ vη τ k) ∧
    ((∀ τ, A τ * Bm τ = 1) ∧ ∀ τ k l, ‖A τ k l‖ ≤ Z.r ^ (-(m : ℤ))) ∧
    ∀ F ∈ Fs, ∀ t ∈ Z.S, ∀ Y : ArcLt (T.Q.Dw j) → Z.K, (∀ x, Y x ∈ Z.K₀ ∧ ‖Y x‖ ≤ 1) →
      ‖∏ τ : D.host.E →+* ℂ, (Matrix.of fun i l : Fin ((T.Q.Dw j).mult τ) => Y ⟨τ, i, l⟩).det‖ = 1 →
      Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval (frameSub Bm lam Y)
          (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR (T.Q.Xo j) T.Q.c F d.yF)) k)) * t ^ k‖)
        Filter.cofinite (nhds 0) ∧
      ‖(γ ^ n)⁻¹ * ∑' k : ℤ, MvPolynomial.eval (frameSub Bm lam Y)
          (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR (T.Q.Xo j) T.Q.c F d.yF)) k)) * t ^ k‖ ≤ 1

variable {h : LawsCore T} {ka : WeightFamilies.Wt D j} {CR Tt cc : ℝ}

def IsValLineAt (q : QDataAt h j ka CR Tt cc)
    (s : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → HeightOneSpectrum (𝓞 q.K₁) → ℝ)
    (vth : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → HeightOneSpectrum (𝓞 q.K₁) → ℤ)
    (vη : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → HeightOneSpectrum (𝓞 q.K₁) →
      ∀ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ) → ℤ) : Prop :=
  (∀ i w, s i w = (lineVal ka.n (vth i w) (vη i w) (q.d i).μ : ℝ)) ∧
  ∀ i, {w | vth i w ≠ 0 ∨ ∃ τ k, vη i w τ k ≠ 0}.Finite

def mlatRul (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) : Set (T.R j) :=
  {F | ∃ G : (recB h).Cusp j ka, G ∈ (recB h).Mlat j ka ∧ G.1 = F}

def FinAtOfStatement (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : Prop :=
  PolyFrStatement T →
  ∀ (q : QDataAt h j ka CR Tt cc) (large₂ : SizeData₂ D) (Cc Ac : ℝ) (n' : ℕ)
    (s : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → HeightOneSpectrum (𝓞 q.K₁) → ℝ)
    (vth : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → HeightOneSpectrum (𝓞 q.K₁) → ℤ)
    (vη : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → HeightOneSpectrum (𝓞 q.K₁) →
      ∀ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ) → ℤ),
    0 < n' → IsValLineAt q s vth vη →
    (∀ i (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (w : HeightOneSpectrum (𝓞 q.K₁)), LiesOver w la →
      FinLocalAt (q.d i) w ka.n (vth i w) (vη i w)
        (w.asIdeal.ramificationIdx (𝓞 T.Q.c.F) * mOf D.host.E n' la) (mlatRul h j ka)) →
    (Real.log |((discr D.host.E : ℤ) : ℝ)| + Real.log n') * (aAbs ka : ℝ) ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size →
    FinAt q large₂ Cc Ac (beOf D.host.E n' (aAbs ka)) s

end Formalism.L2.Pj.QAt
