import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

def IsPre {F : Type} [Field F] [NumberField F] {G T : Scheme.{0}} (s : G ⟶ Sp F) (S : Set G) (d : ℕ) (ι : G ⟶ T)
    {X W : Scheme.{0}} (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ G) (ρ : X ⟶ T) : Prop :=
  IsArithVar q d ∧ IsPullback jB (πB ≫ s) q (spMap (algebraMap (𝓞 F) F)) ∧ IsFinite πB ∧ Set.range πB = S ∧
    jB ≫ ρ = πB ≫ ι

def IntCrit {F : Type} [Field F] [NumberField F] {X W : Scheme.{0}} (s : W ⟶ Sp F) (jB : W ⟶ X) : Prop :=
  ∀ (V : X.Opens), IsAffineOpen V → ∀ f : Γ(W, jB ⁻¹ᵁ V),
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (xg : Sp (AlgebraicClosure F) ⟶ W)
      (xt : Sp ε.O ⟶ X), xg ≫ s = spMap (algebraMap F (AlgebraicClosure F)) → spMap ε.O.subtype ≫ xt = xg ≫ jB →
      ⊤ ≤ xt ⁻¹ᵁ V → ∀ hx : ⊤ ≤ xg ⁻¹ᵁ (jB ⁻¹ᵁ V), TangentOrigin.evalPt xg (jB ⁻¹ᵁ V) hx f ∈ ε.O) →
    ∃ f₀ : Γ(X, V), jB.app V f₀ = f

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {T : Scheme.{0}}
  (t : SAB H T)

def LatPres {R : Type} [CommRing R] (x : Sp R ⟶ T) (kind : ℕ → Bool) (sc : ℕ → ℝ) {g M : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin M → Fin g → R) : Prop :=
  (∃ n : ℕ, n ≠ 0 ∧ ∀ i, Pi.single i (n : R) ∈ Submodule.span R (Set.range h)) ∧
  ∀ (p : ℕ) [Fact p.Prime] (φ : R →+* ↥(intO ℂ_[p])), ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-sc p) ∧
    ∀ (cf : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x)
        (fun i => spMap (dualMap ((intO ℂ_[p]).subtype.comp φ)) ≫ e i) cf w →
      (spMap (epsMul δ) ≫ w ∈ lat t p (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x) (kind p) ↔
        ∀ j, ‖∑ i, ((φ (h j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ ≤ 1)

end Tangent

def IsSplitting {R : Type} [CommRing R] {g M r : ℕ} (D : ℕ) (P : Matrix (Fin g) (Fin g) R) (h : Fin M → Fin g → R)
    (N : ℕ) (U : Matrix (Fin g) (Fin r) R) (I : Fin r → Fin M) : Prop :=
  P * U = (D : R) • U ∧ (Matrix.of fun i => h (I i)) * U = (N : R) • (1 : Matrix (Fin r) (Fin r) R) ∧
    U * (Matrix.of fun i => h (I i)) * P = (N : R) • P ∧
    ∀ j, ∃ a : Fin r → R, Matrix.vecMul (h j) P = ∑ i, a i • Matrix.vecMul (h (I i)) P

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

open Classical in

def scOf (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (kind : ℕ → Bool) (p : ℕ) : ℝ :=
  if kind p = true ∧ τ (H.rt : E) = H.rt0 then vDiff E p else 0

def IsEigProj {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)) (D : ℕ) (P : Matrix (Fin g) (Fin g) R) : Prop :=
  P * P = (D : R) • P ∧
  ∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K), spMap ψ ≫ x ≫ Z.s = spMap (φ.comp β) →
    ∀ (cf : Fin g → K) (w : Sp (DualNumber K) ⟶ Z.t.G.left),
      IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w →
      (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ (P.map ψ).mulVec cf = (D : K) • cf)

def RingBasis {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) (r : ℕ) (kind : ℕ → Bool) (sc : ℕ → ℝ) : Prop :=
  ∃ (N : ℕ) (u : Fin r → (Sp (DualNumber R) ⟶ Z.t.G.left)), N ≠ 0 ∧
    (∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K), spMap ψ ≫ x ≫ Z.s = spMap (φ.comp β) →
      IsEigBasis Z φ (spMap ψ ≫ x) τ (fun i => spMap (dualMap ψ) ≫ u i)) ∧
    ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (φ : c.F →+* ℂ_[p]),
      spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x ≫ Z.s = spMap (φ.comp β) →
      ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-sc p) ∧
        ∀ w, IsEigTan Z φ (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x) τ w →
          ((∃ a : Fin r → ℂ_[p], (∀ i, ‖(N : ℂ_[p]) * a i‖ ≤ 1) ∧
              IsCombAtG Z.t (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x)
                (fun i => spMap (dualMap ((intO ℂ_[p]).subtype.comp ψ)) ≫ u i) a w) ↔
            spMap (epsMul δ) ≫ w ∈ lat Z.t p (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x) (kind p))

abbrev LocAssign {X W : Scheme.{0}} (r : ℕ) (jB : W ⟶ X) (U : X.Opens) : Type 1 :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W), ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U → Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)

def IsLocFrame {F : Type} [Field F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) (r : ℕ)
    (τ : E →+* ℂ) (U : X.Opens) (u : LocAssign Z r jB U) : Prop :=
  (∀ (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (ψ : F →+* K),
      x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ →
      IsEigBasis Z (ψ.comp e.symm.toRingHom) (x ≫ πB ≫ genι Z) τ (u K x hx)) ∧
  ∀ (K K' : Type) [CommRing K] [CommRing K'] (ψ : K →+* K') (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U)
      (hx' : ⊤ ≤ ((spMap ψ ≫ x) ≫ jB) ⁻¹ᵁ U) (i : Fin r),
      u K' (spMap ψ ≫ x) hx' i = spMap (dualMap ψ) ≫ u K x hx i

def IsLocLat {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z)
    (r : ℕ) (τ : E →+* ℂ) (kind : ℕ → Bool) (U : X.Opens) (u : LocAssign Z r jB U) : Prop :=
  ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime) (ε : TrueGeo.Ext v)
    (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X),
    xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)) →
    spMap ε.O.subtype ≫ xt = xg ≫ jB → ⊤ ≤ xt ⁻¹ᵁ U → ∀ (hx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U),
      haveI : Fact (resP v).Prime := ⟨hp⟩
      ∃ δ : ℂ_[resP v], ‖δ‖ = (resP v : ℝ) ^ (-scOf H τ kind (resP v)) ∧
        ∀ w, IsEigTan Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
            (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) τ w →
          ((∃ a : Fin r → ℂ_[resP v], (∀ i, ‖a i‖ ≤ 1) ∧
              IsCombAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
                (fun i => spMap (dualMap (ioOf (resP v) ε)) ≫ u _ xg hx i) a w) ↔
            spMap (epsMul δ) ≫ w ∈ lat Z.t (resP v) (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) (kind (resP v)))

def IsTrans {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) {r : ℕ} {U U' : X.Opens} (u : LocAssign Z r jB U)
    (u' : LocAssign Z r jB U') (A : Matrix (Fin r) (Fin r) Γ(X, U ⊓ U')) : Prop :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (hx' : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U')
    (hxx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (U ⊓ U')) (i : Fin r),
    IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u K x hx) (fun b => TangentOrigin.evalPt (x ≫ jB) (U ⊓ U') hxx (A b i))
      (u' K x hx' i)

def FramesMatch {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) {M : X.Modules} {r : ℕ} (dual : Bool)
    {U U' : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) (f' : Fin r → Γ(M, U')) (u : LocAssign Z r jB U)
    (u' : LocAssign Z r jB U') : Prop :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (hx' : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U')
    (hxx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (U ⊓ U')) (i : Fin r),
    cond dual
      (IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u' K x hx')
        (fun a => TangentOrigin.evalPt (x ≫ jB) (U ⊓ U') hxx (trCo hf f' i a)) (u K x hx i))
      (IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u K x hx)
        (fun b => TangentOrigin.evalPt (x ≫ jB) (U ⊓ U') hxx (trCo hf f' b i)) (u' K x hx' i))

def EigConj (G : ∀ σ' : c.F →+* ℂ, EigMet Z σ') : Prop :=
  ∀ (σ σ' : c.F →+* ℂ) (y : CxPts (genStr Z) σ) (y' : CxPts (genStr Z) σ') (g : EigFrame Z σ (y.1 ≫ genι Z))
    (g' : EigFrame Z σ' (y'.1 ≫ genι Z)) (τ : E →+* ℂ), σ' = (starRingEnd ℂ).comp σ →
    y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → g.IsMap (starRingEnd ℂ) g' →
    (G σ').gram y' g' τ = ((G σ).gram y g τ).map (starRingEnd ℂ)

end Free

end GlobalTheory.ArLieBase

end
