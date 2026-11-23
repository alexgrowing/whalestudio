import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.PtFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCoreSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt

noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FreeQuotientRank Formalism.L2.Pj Formalism.L2.Pj.QAt

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

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def frameSub {K : Type} [Field K] (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (Y : ArcLt Dw → K) : ArcLt Dw → K :=
  fun x => (∑ l, Y ⟨x.1, x.2.1, l⟩ * Bm x.1 l x.2.2) * (lam x.1 x.2.2)⁻¹

def FinLocalAt {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
    [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (n : ℕ)
    (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ) (Fs : Set (Rul Xo c)) : Prop :=
  ∃ (Z : FinSite K₁ w) (γ : Z.K) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Z.K)
    (A Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Z.K),
    (γ ≠ 0 ∧ ‖γ‖ = Z.r ^ vth) ∧
    (∀ τ k, lam τ k ≠ 0 ∧ ‖lam τ k‖ = Z.r ^ vη τ k) ∧
    ((∀ τ, A τ * Bm τ = 1) ∧ ∀ τ k l, ‖A τ k l‖ ≤ Z.r ^ (-(m : ℤ))) ∧
    ∀ F ∈ Fs, ∀ t ∈ Z.S, ∀ Y : ArcLt Dw → Z.K, (∀ x, Y x ∈ Z.K₀ ∧ ‖Y x‖ ≤ 1) →
      ‖∏ τ : E →+* ℂ, (Matrix.of fun i l : Fin (Dw.mult τ) => Y ⟨τ, i, l⟩).det‖ = 1 →
      Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval (frameSub Bm lam Y)
          (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR Xo c F d.yF)) k)) * t ^ k‖)
        Filter.cofinite (nhds 0) ∧
      ‖(γ ^ n)⁻¹ * ∑' k : ℤ, MvPolynomial.eval (frameSub Bm lam Y)
          (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR Xo c F d.yF)) k)) * t ^ k‖ ≤ 1

def arcDetR (Dw : Datum H) (V : Type) [CommRing V] : MvPolynomial (ArcLt Dw) (PowerSeries V) :=
  ∏ τ : E →+* ℂ, Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (PowerSeries V)))

abbrev ArcSR (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) : Type :=
  Localization.Away (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)

def arcXR (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) (x : ArcLt Dw) : ArcSR Dw V ϖ :=
  algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ) (MvPolynomial.X x)

def FrameBound {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
    [Algebra c.F (ArcS Dw K₁)] {w : HeightOneSpectrum (𝓞 K₁)} (Z : FinSite K₁ w) (γ : Z.K)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Z.K)
    (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Z.K) (n : ℕ)
    (d : ArcDatum Xo c K₁) (Fs : Set (Rul Xo c)) : Prop :=
  ∀ F ∈ Fs, ∀ t ∈ Z.S, ∀ Y : ArcLt Dw → Z.K, (∀ x, Y x ∈ Z.K₀ ∧ ‖Y x‖ ≤ 1) →
    ‖∏ τ : E →+* ℂ, (Matrix.of fun i l : Fin (Dw.mult τ) => Y ⟨τ, i, l⟩).det‖ = 1 →
    Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval (frameSub Bm lam Y)
        (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR Xo c F d.yF)) k)) * t ^ k‖)
      Filter.cofinite (nhds 0) ∧
    ‖(γ ^ n)⁻¹ * ∑' k : ℤ, MvPolynomial.eval (frameSub Bm lam Y)
        (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR Xo c F d.yF)) k)) * t ^ k‖ ≤ 1

structure DvrFrame {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
    [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁))
    (Z : FinSite K₁ w) where
  Tv : CDVR
  io : K₁ →+* Tv.Fr
  ιT : Tv.Fr →+* Z.K
  ιT_io : ιT.comp io = Z.ι
  norm_le : ∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1
  ϖ : Tv.V
  ϖ_irr : Irreducible ϖ
  norm_ϖ : ‖ιT (algebraMap Tv.V Tv.Fr ϖ)‖ < 1
  [algR : Algebra c.F (ArcSR Dw Tv.V ϖ)]
  [algW : Algebra c.F (ArcS Dw Tv.Fr)]
  algW_eq : ∀ r : c.F, algebraMap c.F (ArcS Dw Tv.Fr) r =
    arcι Dw Tv.Fr (PowerSeries.C (R := Tv.Fr) (io (algebraMap c.F K₁ r)))
  yR : FrPt Xo c (ArcSR Dw Tv.V ϖ)

attribute [instance] DvrFrame.algR DvrFrame.algW

variable {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)]
  {d : ArcDatum Xo c K₁} {w : HeightOneSpectrum (𝓞 K₁)} {Z : FinSite K₁ w}

def BcRigidAt (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr)
    (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr) : Prop :=
  ∃ (φ : ArcS Dw K₁ →ₐ[c.F] ArcS Dw Dv.Tv.Fr)
    (ψ : ArcSR Dw Dv.Tv.V Dv.ϖ →ₐ[c.F] ArcS Dw Dv.Tv.Fr)
    (z₁ z₂ : FrPt Xo c (ArcS Dw Dv.Tv.Fr)) (tγ : Ix Dw → (ArcS Dw Dv.Tv.Fr)ˣ),
    (∀ f : LaurentSeries K₁, ∃ g : LaurentSeries Dv.Tv.Fr, (∀ m, g.coeff m = Dv.io (f.coeff m)) ∧
      φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.C f)) = algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C g)) ∧
    (∀ x : ArcLt Dw, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.X x)) =
      ∑ l : Fin (Dw.mult x.1), arcX Dw Dv.Tv.Fr x.1 x.2.1 l *
        algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C (HahnSeries.C (Γ := ℤ) (Bm x.1 l x.2.2 * (lam x.1 x.2.2)⁻¹)))) ∧
    (∀ p : PowerSeries Dv.Tv.V, ψ (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Dv.Tv.V)) _ (MvPolynomial.C p)) =
      algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr) p)))) ∧
    (∀ x : ArcLt Dw, ψ (arcXR Dw Dv.Tv.V Dv.ϖ x) = arcX Dw Dv.Tv.Fr x.1 x.2.1 x.2.2) ∧
    (tγ none : ArcS Dw Dv.Tv.Fr) = algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C (HahnSeries.C (Γ := ℤ) γ)) ∧
    (∀ a, tγ (some a) = 1) ∧
    FrMap φ d.yF z₁ ∧ FrMap ψ Dv.yR z₂ ∧ FrBor tγ z₂ z₁

def RecordAt (Dv : DvrFrame d w Z) (Fs : Set (Rul Xo c)) : Prop :=
  ∀ F ∈ Fs, ∀ t ∈ Z.S, ∀ Y : ArcLt Dw → Z.K, (∀ x, Y x ∈ Z.K₀ ∧ ‖Y x‖ ≤ 1) →
    ‖∏ τ : E →+* ℂ, (Matrix.of fun i l : Fin (Dw.mult τ) => Y ⟨τ, i, l⟩).det‖ = 1 →
    ∀ ev : ArcSR Dw Dv.Tv.V Dv.ϖ →+* Z.K,
      (∀ p : PowerSeries Dv.Tv.V, ev (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Dv.Tv.V)) _ (MvPolynomial.C p)) =
        ∑' k : ℕ, Dv.ιT (algebraMap Dv.Tv.V Dv.Tv.Fr (PowerSeries.coeff k p)) * t ^ k) →
      (∀ x, ev (arcXR Dw Dv.Tv.V Dv.ϖ x) = Y x) →
      ‖ev (evR Xo c F Dv.yR)‖ ≤ 1

def FinLocalCutAt (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (vth : ℤ)
    (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ) (Fs : Set (Rul Xo c)) : Prop :=
  ∃ (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr)
    (A Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr),
    (γ ≠ 0 ∧ ‖Dv.ιT γ‖ = Z.r ^ vth) ∧
    (∀ τ k, lam τ k ≠ 0 ∧ ‖Dv.ιT (lam τ k)‖ = Z.r ^ vη τ k) ∧
    ((∀ τ, A τ * Bm τ = 1) ∧ ∀ τ k l, ‖Dv.ιT (A τ k l)‖ ≤ Z.r ^ (-(m : ℤ))) ∧
    BcRigidAt Dv γ lam Bm ∧ RecordAt Dv Fs

def SiteAlg (Z : FinSite K₁ w) (Tv : CDVR) (ιT : Tv.Fr →+* Z.K) : Prop :=
  ∀ s : Finset Z.K, (∀ x ∈ s, (x ∈ Z.K₀ ∨ x ∈ Z.S) ∧ ‖x‖ ≤ 1) →
    ∃ (T' : CDVR) (j : Tv.V →+* T'.V) (i' : T'.Fr →+* Z.K), T'.FinRes ∧ IsLocalHom j ∧
      (∀ v, i' (algebraMap T'.V T'.Fr (j v)) = ιT (algebraMap Tv.V Tv.Fr v)) ∧
      (∀ x : T'.Fr, ‖i' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V T'.Fr)) ∧
      ∀ x ∈ s, ∃ v : T'.V, i' (algebraMap T'.V T'.Fr v) = x

def intAt (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (la : HeightOneSpectrum (𝓞 c.F)) :
    Set (Rul Xo c) :=
  {F | F ∈ sec Xo c a n ∧ ∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, 0 ≤ v F}

structure IntModel (d : ArcDatum Xo c K₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) where
  b : c.V Wl →+* Tv.V
  b_eq : ∀ x, algebraMap Tv.V Tv.Fr (b x) = io (algebraMap c.F K₁ (x : c.F))
  ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V)
  ρ_eq : ∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = io (algebraMap c.F K₁ (embK c τ x))
  aw : ArcIn Dw l (c.V Wl).subtype Tv.V b
  aK : ArcIn Dw l (RingHom.id c.F) Tv.Fr (io.comp (algebraMap c.F K₁))
  pw : Out.IsPullDeg (algebraMap Tv.V Tv.Fr) aw.D₀ aK.D₀
  pK : Out.IsPullDeg io d.a.D₀ aK.D₀
  bcw : InBC (algebraMap Tv.V Tv.Fr) aw (aK.restrict (c.V Wl).subtype) pw
  bcK : InBC io d.a aK pK
  thw : aw.D₀.P.L.Sec
  thw_nz : ThNZ thw
  ew : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt aw.D₀ (epsR Tv.V)
  γ : Tv.Fr
  g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Tv.Fr
  th_tie : ∃ th₁ th₂ : aK.D₀.P.L.Sec, ThBC pw thw th₁ ∧ ThBC pK d.th th₂ ∧ ThMul γ th₁ th₂
  e_tie : ∃ e₁ e₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt aK.D₀ (epsR Tv.Fr),
    (∀ τ k, LetBC pw (ew τ k) (e₁ τ k)) ∧ (∀ τ k, LetBC pK (d.e τ k) (e₂ τ k)) ∧ (∀ τ k, GtTanR (e₁ τ k)) ∧
    ∀ τ k, GtComb (g τ k) (e₁ τ) (e₂ τ k)

def arcιR (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) : PowerSeries V →+* ArcSR Dw V ϖ :=
  (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)).comp MvPolynomial.C

def letMR (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) (τ : E →+* ℂ) :
    Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (ArcSR Dw V ϖ) := Matrix.of fun i k => arcXR Dw V ϖ ⟨τ, i, k⟩

end GlobalTheory.ArcQ
