import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.DetHT

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def lnDet {X : Scheme.{0}} (t : SAB H X) (p : ℕ) [Fact p.Prime] (x : Sp ℂ_[p] ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (τ : E →+* ℂ) : ℝ :=
  ∑ i, Real.log (Pad.grNorm t x (latHT t p x) (u τ) i) - ∑ j, Real.log (Pad.grNorm t x (latHT t p x) (u (conjEmb τ)) j)

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def InducesPl (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] : Prop :=
  ∀ a : c.F, ‖algebraMap c.F ℂ_[p] a‖ ≤ 1 ↔ la.valuation c.F a ≤ 1

variable {p : ℕ} [Fact p.Prime]

def IsAlgFr [Algebra c.F ℂ_[p]] (P : FrPt Xo c ℂ_[p]) : Prop :=
  ∃ (K : Type) (_ : Field K) (k : K →+* ℂ_[p]) (z : Sp K ⟶ Xo.XF c), (∀ a : K, IsAlgebraic ℤ a) ∧ GlobalTheory.AllWt.ptF P = spMap k ≫ z

def IsTestAt (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [Algebra c.F ℂ_[p]] (P : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X) : Prop :=
  spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = GlobalTheory.AllWt.ptF P ≫ Z.j ∧
    ∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ Z.X), T.FinRes ∧ Function.Injective kO ∧ spMap kO ≫ yT = yb

def PtAt [StarRing (𝓞 E)] (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X) (yy : Sp ℂ_[p] ⟶ Xo.XF c)
    (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left) : Prop :=
  spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = yy ≫ Z.j ∧ IsGrpPullback Q.G Z.t.G yb π ∧
    (∀ a, (Q.oG.act a).left ≫ π = π ≫ (Z.t.act.act a).left) ∧ IsGrpPullback Q.A.A Z.oF.t.G yy ψ ∧
    ψ ≫ Z.m.φ = Q.gen ≫ π

def DetConst (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (Zc : Formalism.L2.Pj.Comp Xo c) (τ : E →+* ℂ) (f : Rul Xo c) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) [Fact p.Prime], ∃ ρ : ℝ, ∀ [Algebra c.F ℂ_[p]], InducesPl la p →
    ∀ P : FrPt Xo c ℂ_[p], IsAlgFr P → GlobalTheory.AllWt.LiesOn Zc P → evR Xo c f P ≠ 0 ∧
      Real.log ‖evR Xo c f P‖ + lnDet Z.t p (GlobalTheory.AllWt.ptF P ≫ Z.j) (frameOf Z P).v τ = ρ

end Defs

def RegLocSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : GlobalTheory.Mean4O.Cover Y) (U W : V.X.Opens), (W : Set V.X).Nonempty →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (g : V.X.functionField),
    (∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U →
      below (z ≫ V.j) ∈ W → e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1) →
    ∀ x ∈ U, (V.p x).asIdeal = v.asIdeal → RegAt x g

def GeoSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : GlobalTheory.Mean4O.Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn)
    (a : ∀ σ : F →+* ℂ, TrueGeo.Pts Y σ → ℝ) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → TrueGeo.AlgPt Y → ℝ),
    Norms V L f a lg → ∀ (s : Y.Fn) (W : Y.X.Opens), (W : Set Y.X).Nonempty → ∀ l : ℕ, l.Prime →
    (∀ v : HeightOneSpectrum (𝓞 F), (l : 𝓞 F) ∈ v.asIdeal → ∃ ρ : ℝ, ∀ (e : TrueGeo.Ext v) (y : TrueGeo.AlgPt Y),
      below y.1 ∈ W → UnitAt (below y.1) (s / f (below y.1)) ∧
        Real.log (e.w (TrueGeo.valAt y.1 (s / f (below y.1)))) + lg v e y = ρ) → NefOver L l

def AnyLevSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ q : ℕ, q.Prime → l.GoodAt q) →
    (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → GlobalTheory.CompRat.CurveOver H c.F l.M' →
    ∀ (Zc : Formalism.L2.Pj.Comp Xo c) (τ : Psi H), ∃ f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0),
      ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ ρ : ℝ, ∀ w ∈ htValOn Zc la, w f = (ρ : EReal)

def TestPtSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (p : ℕ) [Fact p.Prime]
    [Algebra c.F ℂ_[p]] (P : FrPt Xo c ℂ_[p]), IsAlgFr P → ∃ yb, IsTestAt Z P yb

def ExFrameSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q →
    ∀ (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (Zc : Formalism.L2.Pj.Comp Xo c)
    (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]], InducesPl la p →
    ∀ (P : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X), IsTestAt Z P yb → GlobalTheory.AllWt.LiesOn Zc P →
    ∃ y : FrPt Xo c ℂ_[p], (fun f => val_vw la p (Valued.v : Valuation ℂ_[p] ℝ≥0) (evR Xo c f y)) ∈ htValOn Zc la ∧
      GlobalTheory.AllWt.ptF y = GlobalTheory.AllWt.ptF P ∧
      letI := H.starRing; ∃ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left) (z : FrPt Xo c ℂ_[p]),
        PtAt Z yb (GlobalTheory.AllWt.ptF P) Q π ψ ∧ IsHTChange Q (ψ ≫ Z.m0.toSABMap.φ) z y

def BridgeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    [IsLocallyNoetherian X] [X.IsSeparated] (t : SAB H X) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (Q : PtP E p)
    (yb : Sp 𝓞_ℂ_[p] ⟶ X) (π : Q.G.left ⟶ t.G.left), IsGrpPullback Q.G t.G yb π →
    ∀ (n : ℕ) (x : Fin n → LieG Q.Gt) (u : Fin n → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)),
    (∀ j, LieTie Q (Q.gen ≫ π) (x j) (u j)) → ∀ (a : Fin n → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
    IsCombAtG t (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) u a w →
      (w ∈ latHT t p (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) ↔ ∑ j, a j • Q.bLie (x j) ∈ Q.latT)

def EigSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ)
    [Fact p.Prime], ∃ δ : ℂ_[p], δ ≠ 0 ∧ ∀ (l : Level H) (c : Coeff l) [Algebra c.F ℂ_[p]] [StarRing (𝓞 E)] (Q : PtP E p)
      (τ : Psi H) (w : Q.V), w ∈ Q.eigV (embInt c Q.integers τ.1) → (w ∈ htLat c Q τ.1 ↔ δ • w ∈ Q.latT)

def CovolSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X) (Λ : Set (Sp (DualNumber C) ⟶ t.G.left))
    (m : ℕ) (u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (g : Matrix (Fin m) (Fin m) C) (δ : C), δ ≠ 0 →
    (∀ k, IsTanAtG t x (u' k)) → (∀ a a' w, IsCombAtG t x u' a w → IsCombAtG t x u' a' w → a = a') →
    (∀ a w, IsCombAtG t x u' a w → (w ∈ Λ ↔ ∀ i, ‖δ * a i‖ ≤ 1)) → (∀ i, IsCombAtG t x u' (g i) (u i)) → g.det ≠ 0 →
    ∑ i, Real.log (Pad.grNorm t x Λ u i) = Real.log ‖g.det‖ + m * Real.log ‖δ‖

def PointSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (τ : Psi H) (p : ℕ) [Fact p.Prime], ∃ K : ℝ, ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) [Algebra c.F ℂ_[p]],
    ∀ f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0), ∀ (P y z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X),
    GlobalTheory.AllWt.ptF y = GlobalTheory.AllWt.ptF P →
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb (GlobalTheory.AllWt.ptF P) Q π ψ → IsHTChange Q (ψ ≫ Z.m0.toSABMap.φ) z y → evR Xo c f y ≠ 0 →
      evR Xo c f P ≠ 0 ∧ Real.log ‖evR Xo c f P‖ + lnDet Z.t p (GlobalTheory.AllWt.ptF P ≫ Z.j) (frameOf Z P).v τ.1 =
        Real.log ‖evR Xo c f y‖ + K

def FlagSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (Zc : Formalism.L2.Pj.Comp Xo c) (τ : Psi H),
    ∀ f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0), (letI := (constF e Y.Y).toAlgebra; GlobalTheory.AllWt.LiesOn Zc Y.y0) →
    DetConst Z Zc τ.1 f → ∀ (N : ℕ), Dw.p + Dw.q = N → ∀ (a : ℕ → Bool) (R : Option ℝ) (v : HeightOneSpectrum (𝓞 F)),
    a (resP v) = true → ∃ ρ : ℝ, ∀ (ε : TrueGeo.Ext v) (y : TrueGeo.AlgPt Y.Y), Y.π (below y.1) ∉ genBd Z →
      UnitAt (below y.1) (Y.val f / ∏ i : Fin N, genAt (divOf Y (expo Dw (rootSym Dw a R τ.1 i))) (below y.1)) ∧
      Real.log (ε.w (TrueGeo.valAt y.1
        (Y.val f / ∏ i : Fin N, genAt (divOf Y (expo Dw (rootSym Dw a R τ.1 i))) (below y.1)))) +
        ∑ i : Fin N, lgOf Y (rootSym Dw a R τ.1 i) v ε y = ρ

end GlobalTheory.DetHT

end
