import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.FinAtOfStatement

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def arcDetR (Dw : Datum H) (V : Type) [CommRing V] : MvPolynomial (ArcLt Dw) (PowerSeries V) :=
  ∏ τ : E →+* ℂ, Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (PowerSeries V)))

abbrev ArcSR (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) : Type :=
  Localization.Away (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)

def arcXR (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) (x : ArcLt Dw) : ArcSR Dw V ϖ :=
  algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ) (MvPolynomial.X x)

variable {D : D7} {T : Core D} {j : ℕ}

def FrameBound {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)] {w : HeightOneSpectrum (𝓞 K₁)} (Z : FinSite K₁ w) (γ : Z.K)
    (lam : ∀ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ) → Z.K)
    (Bm : ∀ τ : D.host.E →+* ℂ, Matrix (Fin ((T.Q.Dw j).mult τ)) (Fin ((T.Q.Dw j).mult τ)) Z.K) (n : ℕ)
    (d : ArcDatumAt T j K₁) (Fs : Set (T.R j)) : Prop :=
  ∀ F ∈ Fs, ∀ t ∈ Z.S, ∀ Y : ArcLt (T.Q.Dw j) → Z.K, (∀ x, Y x ∈ Z.K₀ ∧ ‖Y x‖ ≤ 1) →
    ‖∏ τ : D.host.E →+* ℂ, (Matrix.of fun i l : Fin ((T.Q.Dw j).mult τ) => Y ⟨τ, i, l⟩).det‖ = 1 →
    Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval (frameSub Bm lam Y)
        (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR (T.Q.Xo j) T.Q.c F d.yF)) k)) * t ^ k‖)
      Filter.cofinite (nhds 0) ∧
    ‖(γ ^ n)⁻¹ * ∑' k : ℤ, MvPolynomial.eval (frameSub Bm lam Y)
        (MvPolynomial.map Z.ι (lcoeffPoly (arcNum (evR (T.Q.Xo j) T.Q.c F d.yF)) k)) * t ^ k‖ ≤ 1

structure DvrFrame {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)] (d : ArcDatumAt T j K₁) (w : HeightOneSpectrum (𝓞 K₁))
    (Z : FinSite K₁ w) where
  Tv : CDVR
  io : K₁ →+* Tv.Fr
  ιT : Tv.Fr →+* Z.K
  ιT_io : ιT.comp io = Z.ι
  norm_le : ∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1
  ϖ : Tv.V
  ϖ_irr : Irreducible ϖ
  norm_ϖ : ‖ιT (algebraMap Tv.V Tv.Fr ϖ)‖ < 1
  [algR : Algebra T.Q.c.F (ArcSR (T.Q.Dw j) Tv.V ϖ)]
  [algW : Algebra T.Q.c.F (ArcS (T.Q.Dw j) Tv.Fr)]
  algW_eq : ∀ r : T.Q.c.F, algebraMap T.Q.c.F (ArcS (T.Q.Dw j) Tv.Fr) r =
    arcι (T.Q.Dw j) Tv.Fr (PowerSeries.C (R := Tv.Fr) (io (algebraMap T.Q.c.F K₁ r)))
  yR : FrPt (T.Q.Xo j) T.Q.c (ArcSR (T.Q.Dw j) Tv.V ϖ)

attribute [instance] DvrFrame.algR DvrFrame.algW

variable {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)]
  {d : ArcDatumAt T j K₁} {w : HeightOneSpectrum (𝓞 K₁)} {Z : FinSite K₁ w}

def BcRigidAt (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr) (lam : ∀ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ) → Dv.Tv.Fr)
    (Bm : ∀ τ : D.host.E →+* ℂ, Matrix (Fin ((T.Q.Dw j).mult τ)) (Fin ((T.Q.Dw j).mult τ)) Dv.Tv.Fr) : Prop :=
  ∃ (φ : ArcS (T.Q.Dw j) K₁ →ₐ[T.Q.c.F] ArcS (T.Q.Dw j) Dv.Tv.Fr)
    (ψ : ArcSR (T.Q.Dw j) Dv.Tv.V Dv.ϖ →ₐ[T.Q.c.F] ArcS (T.Q.Dw j) Dv.Tv.Fr)
    (z₁ z₂ : FrPt (T.Q.Xo j) T.Q.c (ArcS (T.Q.Dw j) Dv.Tv.Fr)) (tγ : Ix (T.Q.Dw j) → (ArcS (T.Q.Dw j) Dv.Tv.Fr)ˣ),
    (∀ f : LaurentSeries K₁, ∃ g : LaurentSeries Dv.Tv.Fr, (∀ m, g.coeff m = Dv.io (f.coeff m)) ∧
      φ (algebraMap (MvPolynomial (ArcLt (T.Q.Dw j)) (LaurentSeries K₁)) _ (MvPolynomial.C f)) = algebraMap (MvPolynomial (ArcLt (T.Q.Dw j)) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C g)) ∧
    (∀ x : ArcLt (T.Q.Dw j), φ (algebraMap (MvPolynomial (ArcLt (T.Q.Dw j)) (LaurentSeries K₁)) _ (MvPolynomial.X x)) =
      ∑ l : Fin ((T.Q.Dw j).mult x.1), arcX (T.Q.Dw j) Dv.Tv.Fr x.1 x.2.1 l *
        algebraMap (MvPolynomial (ArcLt (T.Q.Dw j)) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C (HahnSeries.C (Γ := ℤ) (Bm x.1 l x.2.2 * (lam x.1 x.2.2)⁻¹)))) ∧
    (∀ p : PowerSeries Dv.Tv.V, ψ (algebraMap (MvPolynomial (ArcLt (T.Q.Dw j)) (PowerSeries Dv.Tv.V)) _ (MvPolynomial.C p)) =
      algebraMap (MvPolynomial (ArcLt (T.Q.Dw j)) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr) p)))) ∧
    (∀ x : ArcLt (T.Q.Dw j), ψ (arcXR (T.Q.Dw j) Dv.Tv.V Dv.ϖ x) = arcX (T.Q.Dw j) Dv.Tv.Fr x.1 x.2.1 x.2.2) ∧
    (tγ none : ArcS (T.Q.Dw j) Dv.Tv.Fr) = algebraMap (MvPolynomial (ArcLt (T.Q.Dw j)) (LaurentSeries Dv.Tv.Fr)) _ (MvPolynomial.C (HahnSeries.C (Γ := ℤ) γ)) ∧
    (∀ a, tγ (some a) = 1) ∧
    FrMap φ d.yF z₁ ∧ FrMap ψ Dv.yR z₂ ∧ FrBor tγ z₂ z₁

def RecordAt (Dv : DvrFrame d w Z) (Fs : Set (T.R j)) : Prop :=
  ∀ F ∈ Fs, ∀ t ∈ Z.S, ∀ Y : ArcLt (T.Q.Dw j) → Z.K, (∀ x, Y x ∈ Z.K₀ ∧ ‖Y x‖ ≤ 1) →
    ‖∏ τ : D.host.E →+* ℂ, (Matrix.of fun i l : Fin ((T.Q.Dw j).mult τ) => Y ⟨τ, i, l⟩).det‖ = 1 →
    ∀ ev : ArcSR (T.Q.Dw j) Dv.Tv.V Dv.ϖ →+* Z.K,
      (∀ p : PowerSeries Dv.Tv.V, ev (algebraMap (MvPolynomial (ArcLt (T.Q.Dw j)) (PowerSeries Dv.Tv.V)) _ (MvPolynomial.C p)) =
        ∑' k : ℕ, Dv.ιT (algebraMap Dv.Tv.V Dv.Tv.Fr (PowerSeries.coeff k p)) * t ^ k) →
      (∀ x, ev (arcXR (T.Q.Dw j) Dv.Tv.V Dv.ϖ x) = Y x) →
      ‖ev (evR (T.Q.Xo j) T.Q.c F Dv.yR)‖ ≤ 1

def FrameOfCutStatement (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) : Prop :=
  InR D j → AllTest (T.Q.Xo j) T.Q.c → WtField (T.Q.Xo j) T.Q.c → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : ArcDatumAt T j K₁) (w : HeightOneSpectrum (𝓞 K₁)) (Z : FinSite K₁ w) (Dv : DvrFrame d w Z)
    (γ : Dv.Tv.Fr) (lam : ∀ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ) → Dv.Tv.Fr)
    (Bm : ∀ τ : D.host.E →+* ℂ, Matrix (Fin ((T.Q.Dw j).mult τ)) (Fin ((T.Q.Dw j).mult τ)) Dv.Tv.Fr),
    γ ≠ 0 → (∀ τ k, lam τ k ≠ 0) →
    BcRigidAt Dv γ lam Bm → RecordAt Dv (mlatRul h j ka) →
    FrameBound Z (Dv.ιT γ) (fun τ k => Dv.ιT (lam τ k)) (fun τ => (Bm τ).map Dv.ιT) ka.n d (mlatRul h j ka)

def FinLocalCutAt (d : ArcDatumAt T j K₁) (w : HeightOneSpectrum (𝓞 K₁)) (vth : ℤ)
    (vη : ∀ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ) → ℤ) (m : ℕ) (Fs : Set (T.R j)) : Prop :=
  ∃ (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr)
    (lam : ∀ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ) → Dv.Tv.Fr)
    (A Bm : ∀ τ : D.host.E →+* ℂ, Matrix (Fin ((T.Q.Dw j).mult τ)) (Fin ((T.Q.Dw j).mult τ)) Dv.Tv.Fr),
    (γ ≠ 0 ∧ ‖Dv.ιT γ‖ = Z.r ^ vth) ∧
    (∀ τ k, lam τ k ≠ 0 ∧ ‖Dv.ιT (lam τ k)‖ = Z.r ^ vη τ k) ∧
    ((∀ τ, A τ * Bm τ = 1) ∧ ∀ τ k l, ‖Dv.ιT (A τ k l)‖ ≤ Z.r ^ (-(m : ℤ))) ∧
    BcRigidAt Dv γ lam Bm ∧ RecordAt Dv Fs

def FinLocalOfCutStatement (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) : Prop :=
  InR D j → AllTest (T.Q.Xo j) T.Q.c → WtField (T.Q.Xo j) T.Q.c → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : ArcDatumAt T j K₁) (w : HeightOneSpectrum (𝓞 K₁)) (vth : ℤ)
    (vη : ∀ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ) → ℤ) (m : ℕ),
    FinLocalCutAt d w vth vη m (mlatRul h j ka) → FinLocalAt d w ka.n vth vη m (mlatRul h j ka)

end Formalism.L2.Pj.QAt
