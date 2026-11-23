import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def IsThetaWt (la : Weight Dw) (n : ℕ) : Prop :=
  8 ∣ n ∧ (∀ τ, Antitone (la τ)) ∧
    (∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) < Dw.p → ((n / 2 : ℕ) : ℤ) ≤ la τ i) ∧
    (∀ τ (i : Fin (Dw.p + Dw.q)), Dw.p ≤ (i : ℕ) → la τ i ≤ -((n / 2 : ℕ) : ℤ)) ∧
    ∀ τ (i k : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (k : ℕ) = Dw.p → (n : ℤ) + 2 < la τ i - la τ k

abbrev thetaG (la : Weight Dw) (n : ℕ) : WTZ E := wtOf Dw la ((n / 2 : ℕ) : ℤ)

def what₂ (la : Weight Dw) (n : ℕ) : (E →+* ℂ) × ℕ → ℕ := fun x => ((thetaG Dw la n).1 x).toNat

def size (la : Weight Dw) : ℝ := ∑ τ, ∑ i, |(la τ i : ℝ)|

def degree (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)

def width (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : ℕ := n + 2 * Finset.univ.sup fun τ : E →+* ℂ => a (τ, 0)

example (n : ℕ) (h : 8 ∣ n) :
    IsThetaWt Dw (fun _ i => if (i : ℕ) < Dw.p then ((n / 2 : ℕ) : ℤ) + 1 else -((n / 2 : ℕ) : ℤ) - 2) n := by
  refine ⟨h, fun τ i k hik => ?_, fun τ i hi => ?_, fun τ i hi => ?_, fun τ i k hi hk => ?_⟩
  · have : (i : ℕ) ≤ k := hik
    dsimp only
    split_ifs <;> omega
  · simp [hi]
  · simp [not_lt.2 hi]
  · dsimp only
    split_ifs <;> omega

end Weights

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

def Adapted (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (bad : ℕ) {n : ℕ} (Λ : GenLat E n) : Prop :=
  Λ.Unimod ∧ ∃ I : Ideal (𝓞 E), I ⊔ Ideal.span {(bad : 𝓞 E)} = ⊤ ∧
    (∀ P : Ideal (𝓞 E), P.IsPrime → I ≤ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P) ∧
    I • Λ.La ≤ stdLat E n ∧ I • stdLat E n ≤ Λ.La

def rootDisc (K : Type) [Field K] [NumberField K] : ℝ := |(discr K : ℝ)| ^ ((1 : ℝ) / (finrank ℚ K : ℝ))

variable (Xo : Moduli Dw l) (c : Coeff l)

def polyNorm {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : ℝ :=
  Real.sqrt (∑ s : c.F →+* ℂ, ∑ m ∈ P.support, ‖s (P.coeff m)‖ ^ 2)

variable (Dw) in

def harmRank (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : ℕ :=
  finrank ℚ c.F * finrank c.F (Submodule.span c.F
    (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)))

def IsShortPoly (B : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (Λ : GenLat E n) (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  P ∈ harmL c Λ a ∧ polyNorm c P ≤
    Real.sqrt (((harmRank Dw c a n : ℝ) + 3) / 4) * Real.sqrt (finrank ℚ c.F) * rootDisc c.F *
      Real.exp (13 * ((Dw.p + Dw.q : ℕ) : ℝ) * B * (degree Dw a : ℝ))

variable (Dw) in

def IsBeta {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β

def IsTheta (nab : NabV Xo c) (G : WTZ E) {n : ℕ} (Λ : GenLat E n) (β : c.F) (N : ℕ) (x₀ : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) : Prop :=
  f ∈ secZ Xo c (exZ Dw G) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k),
      ShortValAt Xo c nab (x0Dat (l := l) c x₀) Λ β N P y (evR Xo c f y)

def IsMemberData (bad : ℕ) (B : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (Λ : GenLat E n) (N : ℕ) (x₀ : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Adapted H bad Λ ∧ Λ.LevOK N l.M ∧ AdmX (l := l) false x₀ ∧ IsShortPoly c B a Λ P

def family (nab : NabV Xo c) (bad : ℕ) (B : ℝ) (la : Weight Dw) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (Λ : GenLat E n) (β : c.F) (N : ℕ) (x₀ : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F),
    IsMemberData c bad B (what₂ Dw la n) Λ N x₀ P ∧ IsBeta Dw c Λ β ∧
      IsTheta Xo c nab (thetaG Dw la n) Λ β N x₀ P f}

def Rational (nab : NabV Xo c) (bad : ℕ) (B : ℝ) (la : Weight Dw) (n : ℕ) : Prop :=
  ∀ (Λ : GenLat E n) (N : ℕ) (x₀ : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F),
    IsMemberData c bad B (what₂ Dw la n) Λ N x₀ P →
      (∃ β, IsBeta Dw c Λ β) ∧ ∀ β, IsBeta Dw c Λ β → ∃ f, IsTheta Xo c nab (thetaG Dw la n) Λ β N x₀ P f

variable {Xo c} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def SupLe (x : ℝ) (G : WTZ E) (Z : Comp Xo c) (σ : c.F →+* ℂ) (f : Rul Xo c) (A : ℝ) : Prop :=
  ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) x G f z ≤ Real.exp A

def ShortSpan (x : ℝ) (G : WTZ E) (S : Set (Rul Xo c)) (A A' : ℝ) : Prop :=
  (∀ f ∈ S, f ∈ cuspW Xo c U G) ∧
    (∀ f ∈ S, ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), SupLe U x G Z σ f A) ∧
    (∃ Na : ℕ, 0 < Na ∧ Real.log Na ≤ A' ∧
      ∀ f ∈ S, ∀ h : f ∈ cuspW Xo c U G, (Na • ⟨f, h⟩ : cuspW Xo c U G) ∈ latW U G) ∧
    ∀ Z : Comp Xo c, Submodule.span c.F ((fun f => GlobalTheory.FlatLine.idem Z * f) '' S) = cuspOn U Z G

theorem ShortSpan.mono {x : ℝ} {G : WTZ E} {S : Set (Rul Xo c)} {A A' B B' : ℝ} (h : ShortSpan U x G S A A')
    (hA : A ≤ B) (hA' : A' ≤ B') : ShortSpan U x G S B B' := by
  obtain ⟨h1, h2, ⟨Na, h3, h4, h5⟩, h6⟩ := h
  exact ⟨h1, fun f hf Z σ z hz => (h2 f hf Z σ z hz).trans (Real.exp_le_exp.2 hA), ⟨Na, h3, h4.trans hA', h5⟩, h6⟩

end Family

section Constants

variable (D : D7) (large₂ : SizeData₂ D)

def levelM (e : ℕ) : ℕ := D.host.g 0 * D.host.g 1 * 15 ^ e

def badM (M : ℕ) : ℕ := D.host.QS * D.host.q * D.host.d * M

def constB (M n w dg : ℕ) : ℝ :=
  Real.log M + Real.log (Ideal.absNorm D.host.ccK) + Real.log D.host.rdE +
    Real.log ((D.R.f : ℝ) * D.R.r * n * w * ((dg : ℝ) + 2))

def constP (B : ℝ) : ℝ := (D.R.f : ℝ) * D.R.r * (24 * B + Real.log Real.pi / 2)

def constG (K : Type) [Field K] [NumberField K] (B : ℝ) (p : ℕ) : ℝ :=
  constP D B + (3 * large₂.sc.L + 2 * (Real.log (finrank ℚ K) + Real.log (rootDisc K))) +
    2 * (D.R.f : ℝ) * D.R.r * (WeightAlgebra.lamStar D + 2 * Real.log p) + 31 * zBase large₂

def Page : Prop :=
  (∃ P : ParameterChoice' D large₂, Nonempty (ParamsT D large₂ P)) ∧ SizesAt large₂ ∧ 9 ≤ D.R.r ∧ 10 ≤ large₂.sc.L ∧
    Ideal.absNorm D.host.ccK ≤ D.host.d

end Constants

section Statement

variable (D : D7) (large₂ : SizeData₂ D)

def IsHostOf (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) : Prop :=
  H.d = D.host.d ∧ (H.rt : D.host.E) = D.host.sqrtMinusD ∧ H.rt0 = D.host.φ₀ D.host.sqrtMinusD

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

def Objects (j e : ℕ) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (nab : NabV Xo c) :
    Prop :=
  IsHostOf D H ∧ IsDatW D j Dw ∧
    (4 ≤ e ∧ l.M = levelM D e ∧ l.A = 1 ∧ Real.log l.M ≤ 30 * large₂.sc.L) ∧
    ((∀ y : D.what₂.O, D.what₂.embLL (D.what₂.OtoLL y) ∈ c.F) ∧ KPsiIn (Dw := Dw) c ∧ FnAlgClosed Xo c) ∧
    (∀ σ, GoodEmb c σ → IsUnf (U σ) ∧ ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧
    ∃ _ : StarRing (𝓞 D.host.E), IsNab Xo c nab

def InRange (Dw : Datum H) (la : Weight Dw) (n : ℕ) : Prop :=
  IsThetaWt Dw la n ∧ 8 * D.R.f * D.R.r + 4 ≤ n ∧ (D.R.f : ℝ) * D.R.r * n ≤ large₂.sc.b ∧ size Dw la ≤ large₂.sc.b ^ 2

def constBAt (l : Level H) (Dw : Datum H) (la : Weight Dw) (n : ℕ) : ℝ :=
  constB D l.M n (width (what₂ Dw la n) n) (degree Dw (what₂ Dw la n))

def Concl (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (nab : NabV Xo c)
    (la : Weight Dw) (n p : ℕ) : Prop :=
  Rational Xo c nab (badM D l.M) (constBAt D l Dw la n) la n ∧
    ShortSpan U (xiR D) (thetaG Dw la n) (family Xo c nab (badM D l.M) (constBAt D l Dw la n) la n)
      (constG D large₂ c.F (constBAt D l Dw la n) p * (size Dw la + n)) (31 * zBase large₂ * (size Dw la + n))

def GminAt (j : ℕ) : Prop :=
  ∀ (e : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (nab : NabV Xo c), Objects D large₂ j e Xo c U nab →
    ∀ (la : Weight Dw) (n : ℕ), InRange D large₂ Dw la n →
      ∀ p : ℕ, p = D.host.pde ∨ p = D.host.pde' → Concl D large₂ Xo c U nab la n p

end Statement

def Gmin : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D), Page D large₂ → ∀ j, 1 ≤ j → j < D.R.m → GminAt D large₂ j

def GminWithDefinite : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D), Page D large₂ → ∀ j, 1 ≤ j → j ≤ D.R.m → GminAt D large₂ j

theorem GminWithDefinite.gmin (h : GminWithDefinite) : Gmin := fun D large₂ hP j h1 h2 => h D large₂ hP j h1 h2.le

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData
