import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

def IsEigTan {K : Type} [CommRing K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (τ : E →+* ℂ)
    (w : Sp (DualNumber K) ⟶ Z.t.G.left) : Prop :=
  IsTanAtG Z.t x w ∧ ∀ a : 𝓞 E, w ≫ (Z.t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ w

def IsEigBasis {K : Type} [CommRing K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (τ : E →+* ℂ) {m : ℕ}
    (u : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)) : Prop :=
  (∀ i, IsEigTan Z φ x τ (u i)) ∧ ∀ w, IsEigTan Z φ x τ w → ∃! a : Fin m → K, IsCombAtG Z.t x u a w

omit [NumberField E] [IsCMField E] in

def trCo {X : Scheme.{0}} {M : X.Modules} {r : ℕ} {U U' : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f)
    (f' : Fin r → Γ(M, U')) (b a : Fin r) : Γ(X, U ⊓ U') :=
  (hf.basis inf_le_left).repr (Twist.resM M inf_le_right (f' a)) b

abbrev FrAssign {X W : Scheme.{0}} (M : X.Modules) (r : ℕ) (jB : W ⟶ X) : Type 1 :=
  ∀ (U : X.Opens) (f : Fin r → Γ(M, U)), VB.IsFrame f → ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W),
    ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U → Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)

def IsLieFrames {F : Type} [Field F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z)
    (M : X.Modules) (r : ℕ) (τ : E →+* ℂ) (dual : Bool) (u : FrAssign Z M r jB) : Prop :=
  (∀ (U : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f) (K : Type) [CommRing K] (x : Sp K ⟶ W)
      (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (ψ : F →+* K), x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ →
      IsEigBasis Z (ψ.comp e.symm.toRingHom) (x ≫ πB ≫ genι Z) τ (u U f hf K x hx)) ∧
  (∀ (U U' : X.Opens) (f : Fin r → Γ(M, U)) (f' : Fin r → Γ(M, U')) (hf : VB.IsFrame f) (hf' : VB.IsFrame f')
      (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (hx' : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U')
      (hxx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (U ⊓ U')) (i : Fin r),
      cond dual
        (IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u U' f' hf' K x hx')
          (fun a => TangentOrigin.evalPt (x ≫ jB) (U ⊓ U') hxx (trCo hf f' i a)) (u U f hf K x hx i))
        (IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u U f hf K x hx)
          (fun b => TangentOrigin.evalPt (x ≫ jB) (U ⊓ U') hxx (trCo hf f' b i)) (u U' f' hf' K x hx' i))) ∧
  ∀ (U : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f) (K K' : Type) [CommRing K] [CommRing K'] (ψ : K →+* K')
      (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (hx' : ⊤ ≤ ((spMap ψ ≫ x) ≫ jB) ⁻¹ᵁ U) (i : Fin r),
      u U f hf K' (spMap ψ ≫ x) hx' i = spMap (dualMap ψ) ≫ u U f hf K x hx i

open Classical in

def IsLieLat {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z)
    (M : X.Modules) (r : ℕ) (τ : E →+* ℂ) (kind : ℕ → Bool) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Prop)
    (u : FrAssign Z M r jB) : Prop :=
  ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), P v → ∀ (hp : (resP v).Prime) (ε : TrueGeo.Ext v)
    (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X),
    xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)) →
    spMap ε.O.subtype ≫ xt = xg ≫ jB →
    ∀ (U : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f), ⊤ ≤ xt ⁻¹ᵁ U → ∀ (hx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U),
      haveI : Fact (resP v).Prime := ⟨hp⟩
      ∃ δ : ℂ_[resP v], ‖δ‖ = (resP v : ℝ) ^ (-(if kind (resP v) = true ∧ τ (H.rt : E) = H.rt0 then
          vDiff E (resP v) else 0)) ∧
        ∀ w, IsEigTan Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
            (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) τ w →
          ((∃ a : Fin r → ℂ_[resP v], (∀ i, ‖a i‖ ≤ 1) ∧
              IsCombAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
                (fun i => spMap (dualMap (ioOf (resP v) ε)) ≫ u U f hf _ xg hx i) a w) ↔
            spMap (epsMul δ) ≫ w ∈ lat Z.t (resP v) (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) (kind (resP v)))

def IsLieMet {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X)
    (πB : W ⟶ gen Z) (M : X.Modules) (r : ℕ) (τ : E →+* ℂ) (dual : Bool) (hr : r = Dw.mult τ)
    (G : ∀ σ' : c.F →+* ℂ, EigMet Z σ') (h : VMetric q M r) (u : FrAssign Z M r jB) : Prop :=
  ∀ (σ : F →+* ℂ) (z : CxPts q (σ.comp (algebraMap (𝓞 F) F))) (zg : Sp ℂ ⟶ W)
    (yc : CxPts (genStr Z) (σ.comp e.symm.toRingHom)), zg ≫ jB = z.1 → yc.1 = zg ≫ πB →
    ∀ (ch : Chart M r) (hx : ⊤ ≤ (zg ≫ jB) ⁻¹ᵁ ch.U) (g : EigFrame Z (σ.comp e.symm.toRingHom) (yc.1 ≫ genι Z)),
      (∀ i, g.v τ (Fin.cast hr i) = u ch.U ch.e ch.isFrame ℂ zg hx i) →
      (h.met (σ.comp (algebraMap (𝓞 F) F))).G ch z =
        (cond dual ((G _).gram yc g τ)⁻¹ (Matrix.transpose ((G _).gram yc g τ))).submatrix (Fin.cast hr) (Fin.cast hr)

end Free

def embB (D : D7) (a : D.what₂.Tau × Bool) : D.host.E →+* ℂ := cond a.2 (DV.tauEmb D a.1) (conjEmb (DV.tauEmb D a.1))

def LieBase {D : D7} (O : Setup D) (B R : ℝ) (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (E : D.what₂.Tau × Bool → Bs.Modules) (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) : Prop :=
  ∃ (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (_ : IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (G : ∀ σ', EigMet O.s.T.Z σ'),
    IsFinite πB ∧ Set.range πB = Set.range (O.Φ.C c).π ∧
    (∀ a, IsLieFrames O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (!a.2) (u a)) ∧
    (∀ a, IsLieLat O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (ArIn.ind (FlagAr.setB O.Y B)) (fun _ => True) (u a)) ∧
    (∀ σ n, O.met.hm c (some R) σ n = (O.Φ.C c).met (G (embOf O.κ.e σ)) n) ∧
    ∀ a, ∃ hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a),
      IsLieMet O.s.T.Z O.κ.e q jB πB (E a) _ (embB D a) (!a.2) hr G (h a) (u a)

end GlobalTheory.ArLieBase

end
