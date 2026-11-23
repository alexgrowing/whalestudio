import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LamT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj MeasureTheory
open GlobalTheory.CM GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def SecTie {Xo : Moduli Dw l} {S : Type} [CommRing S] {t' : SAB H (Sp S)} {x x' : Sp S ⟶ Xo.X}
    (m : SABMap t' Xo.univ.t x) (th : LB.Sec t'.PP.L) (s : LB.Sec (PPx x')) : Prop :=
  ∃ (w : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m.φ)) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m.φ)),
    RigIso m w ∧ IsoMaps w th s1 ∧
    ∀ g : t'.G.left ⟶ Gx x', g ≫ (snd (Over.mk x') Xo.univ.t.G).left = m.φ →
      g ≫ (fst (Over.mk x') Xo.univ.t.G).left = t'.G.hom →
      ∀ j (h : (Xo.univ.t.PP.L.pull m.φ).U j ≤ g ⁻¹ᵁ (PPx x').U (fun _ => j PUnit.unit)),
        s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))

structure FibKey (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) where
  T : PAT H (Sp S)
  m : SABMap T.t Xo.univ.t x
  g_pos : 1 ≤ T.g
  th : LB.Sec T.t.PP.L
  th_ne : ∀ s : Sp S, ∃ q : T.t.G.left, T.t.G.hom q = s ∧ q ∈ Out.nonzeroLocus th
  v : Fin T.g → (epsR S ⟶ T.t.G)
  basis : IsLieBasis v

abbrev FibKey.key {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (Φ : FibKey Xo S x) : KeyIn S :=
  ⟨Φ.T.pol, Φ.g_pos, Φ.T.t.PP.rig, Φ.T.t.PP.rigGen, Φ.th, Φ.th_ne, Φ.v, Φ.basis⟩

structure CMPt (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] : Type 1 where
  K : Type
  [fK : Field K]
  [nfK : NumberField K]
  [algK : Algebra c.F K]
  x : Sp K ⟶ Xo.X
  Φ : FibKey Xo K x
  B : PAT H (Sp (𝓞 K))
  m' : SABMap Φ.T.t B.t (spMap (algebraMap (𝓞 K) K))
  oa : B.pol.OAct (𝓞 E)
  AΨ : Out.PolAV (Sp (𝓞 K))
  oaΨ : AΨ.OAct (𝓞 E)
  A' : Out.PolAV (Sp (𝓞 K))
  oa' : A'.OAct (𝓞 E)
  φΨ : Fin Dw.p → (AΨ.A ⟶ B.pol.A)
  φ' : Fin Dw.q → (A'.A ⟶ B.pol.A)
  hΨ : Fin Dw.p → 𝓞 E
  h' : Fin Dw.q → 𝓞 E
  xΨ : KeyIn K
  x' : KeyIn K
  φΨg : xΨ.P.A.left ⟶ AΨ.A.left
  φ'g : x'.P.A.left ⟶ A'.A.left
  τΨ : Fin xΨ.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}
  τ' : Fin x'.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) ≠ H.rt0}
  ℓΨ : Fin xΨ.P.g → MLine K
  ℓ' : Fin x'.P.g → MLine K
  Tl : MLine K
  LamL : MLine K
  e : (Σ b : E →+* ℂ, Fin (Dw.mult b)) ≃ Fin Φ.T.g
  src : Fin Φ.T.g → (Fin Dw.p × Fin xΨ.P.g) ⊕ (Fin Dw.q × Fin x'.P.g)
  U : Matrix (Fin Φ.T.g) (Fin Φ.T.g) K
  ℓ : Fin Φ.T.g → MLine K
  y : FrPt Xo c K

attribute [instance] CMPt.fK CMPt.nfK CMPt.algK

variable {Xo : Moduli Dw l} {c : Coeff l}

namespace CMPt

variable [StarRing (𝓞 E)] (z : CMPt Xo c)

abbrev obj : LamF.LamObj c Dw.p Dw.q :=
  LamF.LamObj.mk (c := c) (nΨ := Dw.p) (n' := Dw.q) z.K z.B.pol z.oa z.AΨ z.oaΨ z.A' z.oa' z.φΨ z.φ' z.hΨ z.h' z.Φ.key z.xΨ
    z.x' z.m'.φ z.φΨg z.φ'g z.τΨ z.τ' z.ℓΨ z.ℓ' z.Tl z.LamL

abbrev letters : LamF.LamLetters z.obj := ⟨Dw.mult, z.e, z.src, z.U, z.ℓ⟩

def Good (f : ℕ) (La : ℝ) : Prop :=
  LamF.LamObjGood z.obj f La ∧ z.letters.IsGood ∧ z.oa.act = z.B.t.act.act ∧ z.y.x = z.x ∧
    SecTie z.Φ.m z.Φ.th z.y.s ∧
    ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ w : epsR z.K ⟶ z.Φ.T.t.G,
      z.letters.IsLetter (z.e ⟨τ, i⟩) w ∧ z.y.u τ i = w.left ≫ z.Φ.m.φ

end CMPt

def IsFrPoly (f : Rul Xo c) {K : Type} [CommRing K] [Algebra c.F K] (y : FrPt Xo c K)
    (G : MvPolynomial (FrVar Dw.mult) K) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (φ : K →ₐ[c.F] S) (z z' : FrPt Xo c S)
    (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S), (∀ b, IsUnit (Y b).det) → FrMap φ y z →
    FrChg (fun b => (Y b).transpose) 1 z z' → evR Xo c f z' = evalFr (MvPolynomial.map φ.toRingHom G) Y

def IsMetricAt (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x))
    (uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ) : Prop :=
  ∃ (Φ : FibKey Xo ℂ x) (u : HolUnif Φ.key.P.A Φ.key.P.L Φ.key.P.g) (Hm : Matrix (Fin Φ.key.P.g) (Fin Φ.key.P.g) ℂ)
    (χ : u.Λ → ℂ) (θ : (Fin Φ.key.P.g → ℂ) → ℂ) (Fd : Set (Fin Φ.key.P.g → ℂ))
    (w : ∀ b : E →+* ℂ, Fin (Dw.mult b) → (epsR ℂ ⟶ Φ.key.P.A))
    (W : ∀ b : E →+* ℂ, Fin (Dw.mult b) → Fin Φ.key.P.g → ℂ),
    SecTie Φ.m Φ.th s ∧ u.IsAH Hm χ ∧ u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧
    IsAddFundamentalDomain u.Λ Fd volume ∧
    N = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧
    (∀ b i, (w b i).left ≫ Φ.m.φ = uu b i ∧ u.IsDiff (W b i) (w b i)) ∧
    ∀ b i k, Gr b i k = Real.pi * hermForm Hm (W b k) (W b i)

def IsMetric {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ)) (N : ℝ)
    (Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ) : Prop :=
  IsMetricAt y.x y.s y.u N Gr

def LieInt (T : CDVR) (io : c.F →+* T.Fr) {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X}
    (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)) : Prop :=
  ∃ ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G),
    (∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧
    (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w →
      ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧
    ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = u τ i ∧
      u' ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left

def SecInt (T : CDVR) {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x x' : Sp T.Fr ⟶ Xo.X}
    (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) (s : LB.Sec (PPx x')) : Prop :=
  ∃ θ : LB.Sec G.PP.L,
    (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
      σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧
    ∃ (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)) (σ : LB.Sec t'.PP.L) (θ2 : LB.Sec (G.PP.L.pull m2.φ)),
      RigIso m2 w2 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧ SecTie m1 σ s

structure LocMod [StarRing (𝓞 E)] (z : CMPt Xo c) (T : CDVR) (iK : z.K →+* T.Fr) where
  ρ : 𝓞 z.K →+* T.V
  hρ : (algebraMap T.V T.Fr).comp ρ = iK.comp (algebraMap (𝓞 z.K) z.K)
  G : PAT H (Sp T.V)
  t' : PAT H (Sp T.Fr)
  n : SABMap G.t z.B.t (spMap ρ)
  n' : SABMap t'.t z.Φ.T.t (spMap iK)
  m1 : SABMap t'.t Xo.univ.t (spMap iK ≫ z.x)
  m2 : SABMap t'.t G.t (spMap (algebraMap T.V T.Fr))
  h1 : m1.φ = n'.φ ≫ z.Φ.m.φ
  h2 : m2.φ ≫ n.φ = n'.φ ≫ z.m'.φ

theorem integral_of (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr)
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} :
    letI := io.toAlgebra
    ∀ (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      LieInt T io m1 m2 y.u → SecInt T m1 m2 y.s → Integral T io y := by
  intro m1 m2 hL hS
  obtain ⟨θ, hθ, w2, σ, θ2, hr2, hm2, hp, w1, s1, hr1, hm1, hg1⟩ := hS
  unfold Integral
  exact ⟨G, t', m1, m2, hL, θ, hθ, w1, w2, σ, s1, θ2, hr1, hr2, hm1, hm2, hp, hg1⟩

def embAlg {K : Type} [Field K] [Algebra c.F K] (σ : K →+* ℂ) : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K)) :=
  { (σ : K →+* ℂ) with commutes' := fun _ => rfl }

end GlobalTheory.LamT
