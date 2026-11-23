import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilTwistColumns

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open Classical in

def perReal (X : Data E r) (x : Frame X.Ψ r) (v : X.Ψ → Fin r → ℂ) (τ : E →+* ℂ) (i : ℕ) : ℂ :=
  if h : τ ∈ X.Ψ then
    (if hi : X.p0 + i < r then ((mat x ⟨τ, h⟩)⁻¹.mulVec (v ⟨τ, h⟩)) ⟨X.p0 + i, hi⟩ else 0)
  else if h' : conjEmb τ ∈ X.Ψ then
    (if hj : X.p0 - 1 - i < r then
      hermC (conjEmb τ) X.Gm (col (mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, hj⟩) (v ⟨conjEmb τ, h'⟩) else 0)
  else 0

end Period

section Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

def IsCanTheta {g : ℕ} {lab : Fin g → E →+* ℂ}
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab) (k : Fin F.n)
    (Pm : (F.Di k).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (θ : (Fin g → ℂ) → ℂ) : Prop :=
  IsPeriod (F.Di k) lab Pm ∧ y.x = F.u k Pm ∧
    Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di k).EF a b) ∧
    ∃ (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
      (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
      (∀ j z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
      (∀ j j' z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
        fr j z = valAt' (F.ex k Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
          (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
      (∀ j, ⊤ ≤ (F.ex k Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
          (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
      (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
          Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
      ∀ j z (pt : Sp ℂ ⟶ Gx y.x), pt ≫ gxFst y.x = (F.ex k Pm z).left → pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
        ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z

end Theta

section Const

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def colAt {V W : HSp D} (hr : W.rank = r) {Ψ : Finset (D.host.E →+* ℂ)}
    (th : Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (w : WO V W) (b : Fin V.rank) : Ψ → Fin r → ℂ :=
  fun τ a => th τ (infPart D (w (Fin.cast hr.symm a) b))

def IsFrameConst (U : Unf Xo c σ r) (V W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (vac : WO V W → ℂ) (cst : GA D W → ℂ) : Prop :=
  ∀ h : GA D W, ∃ γ : GA D W, MarkBy U W hr dict ι F ik φ h γ ∧
    (∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM W (th (dict h).1 τ) (γ * h)) * x₀ τ.1) ∧
    ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (Pm : (F.Di (ik (dict h).1)).La →+ (Fin g → ℂ))
      (Hm : Matrix (Fin g) (Fin g) ℂ) (θ : (Fin g → ℂ) → ℂ),
      (∀ a j, Pm a j = perFr (U.X (dict h).1) (dict h).2 (φ (dict h).1 a : Fin r → D.host.E)
        (relab c σ (e j).1) (e j).2) ∧
      IsCanTheta F (ik (dict h).1) Pm (U.un (dict h).1 ⟨(dict h).2, hx⟩) Hm θ ∧
      ∀ w : WO V W, Matrix.map w (finPart D) = 0 → ∀ z : Fin V.rank → Fin g → ℂ,
        (∀ b j, z b j = perReal (U.X (dict h).1) (dict h).2 (colAt hr (th (dict h).1) w b)
          (relab c σ (e j).1) (e j).2) →
        Complex.exp (Real.pi / 2 * ∑ b, hermForm Hm (z b) (z b)) * om (1, γ * h) vac w =
          cst h * ∏ b, θ (z b)

def cXi {n : ℕ} (d : DeltaDat Xo c n) {W : HSp D}
    (U₂ : Unf d.Xo₂ d.c₂ (σ.comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D W → Σ k, Frame (U₂.X k).Ψ r)
    (h : GA D W) : ℂ :=
  rdU U₂ d.cδ (dict₂ h).1 (dict₂ h).2

end Const

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def WeilTwist : Prop :=
  R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ (t : T0) (h : GA D (Vc D i)) (g : GA D (Wc D i)) (y x : (AE D)ˣ),
    IsDetRoot (Vc D i) h y → IsDetRoot (Wc D i) g x → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      R.ωP i t (h, g) f = (((R.xi t x * (R.xi t y)⁻¹ : Circle)) : ℂ) • R.ωP i A.μ0 (h, g) f

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ}
  (U : Unf Xo c σ D.R.r) (dict : GA D (Wc D i) → Σ k, Frame (U.X k).Ψ D.R.r)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) {g : ℕ}
  (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
  (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
  (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  (dδ : T0 → DeltaDat Xo c (Vc D i).rank)
  (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) D.R.r)
  (dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r)
  (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)

def Ties : Prop :=
  R.toLevCh.Is A.μ0 ∧ R.thP_ωP ∧ R.thP_vP ∧ VStd D i ∧
    (∀ k, ModelW (Wc D i) (rank_Wc i) (U.X k)) ∧
    (∀ k (τ : D.host.E →+* ℂ), τ ∈ (U.X k).Ψ ↔ ∃ ρ, τ = tauE D ρ) ∧
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) x₀ ∧ LatEmb (Wc D i) ι ∧
    DictLat U (Wc D i) (rank_Wc i) dict ι e F ik φ th x₀ ∧
    CovPin Xo c dδ ∧ (∀ t, XiIs R i t (xi t)) ∧
    CXiVal (Wc D i) (rank_Wc i) σ dδ U₂ dict₂ ι x₀ xi

abbrev IsConstOf (t : T0) (cst : GA D (Wc D i) → ℂ) : Prop :=
  IsFrameConst U (Vc D i) (Wc D i) (rank_Wc i) dict ι e F ik φ th x₀ (R.ωP i t) (R.vacP i) cst

def TwistFactorAt : Prop :=
  Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi →
    ∀ c0 cb : GA D (Wc D i) → ℂ, IsConstOf R i U dict ι e F ik φ th x₀ A.μ0 c0 →
      (∀ h, c0 h = cb h * cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h) →
      ∀ (t : T0) (ct : GA D (Wc D i) → ℂ), IsConstOf R i U dict ι e F ik φ th x₀ t ct →
        ∃ ζ : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
          ∀ h, ct h = D.what₂.embLL ζ * cb h * cXi (dδ t) (U₂ t) (dict₂ t) h

def TwistFactorNormAt : Prop :=
  Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi →
    (∀ h, cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h = 1) →
    ∀ c0 : GA D (Wc D i) → ℂ, IsConstOf R i U dict ι e F ik φ th x₀ A.μ0 c0 →
      ∀ (t : T0) (ct : GA D (Wc D i) → ℂ), IsConstOf R i U dict ι e F ik φ th x₀ t ct →
        ∃ ζ : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
          ∀ h, ct h = D.what₂.embLL ζ * c0 h * cXi (dδ t) (U₂ t) (dict₂ t) h

theorem TwistFactorAt.norm (hT : TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi) :
    TwistFactorNormAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi :=
  fun hTi h1 c0 hc0 t ct hct => hT hTi c0 c0 hc0 (fun h => by rw [h1 h, mul_one]) t ct hct

end Row

def TwistFactor {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  ∀ (i : Fin D.R.m) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (U : Unf Xo c σ D.R.r) (dict : GA D (Wc D i) → Σ k, Frame (U.X k).Ψ D.R.r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (g : ℕ)
    (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (dδ : T0 → DeltaDat Xo c (Vc D i).rank)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) D.R.r)
    (dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r)
    (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ),
    TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi

end GlobalTheory.IndefiniteRowSideFullHecke.WeilTwistColumns
