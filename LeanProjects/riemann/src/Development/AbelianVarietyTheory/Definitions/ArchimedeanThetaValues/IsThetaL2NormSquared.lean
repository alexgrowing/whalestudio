import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt

def DlogTan {K₁ : Type} [Field K₁] {D₀ : ReciprocityTheory.ChartRestriction.G.Out.DegPre K₁} (v : ReciprocityTheory.ChartRestriction.G.Out.GtPt D₀ (epsR K₁))
    (χ : D₀.X) (y : K₁) : Prop :=
  ∀ j, ⊤ ≤ LB.wchart D₀.P.L (ReciprocityTheory.ChartRestriction.G.Out.DegPre.gtφT D₀ (epsR K₁) v.b χ) j →
    TrivSqZeroExt.snd (valR (A := DualNumber K₁) (𝟙 _) _ ((v.s χ).s j).val) =
      TrivSqZeroExt.fst (valR (A := DualNumber K₁) (𝟙 _) _ ((v.s χ).s j).val) * y

noncomputable def xiVal {E : Type} [Field E] [NumberField E] {K₁ : Type} [Field K₁] {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] (τK : E →+* K₁) (ξ : Module.Dual ℤ X) (χ : X) : K₁ :=
  ∑ i, τK ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (NumberField.integralBasis E) i) *
    ((ξ ((NumberField.RingOfIntegers.basis E i) • χ) : ℤ) : K₁)

noncomputable def pairE {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (ξ : Module.Dual ℤ X) (x : X) : E :=
  ∑ i, (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (NumberField.integralBasis E) i *
    ((ξ ((NumberField.RingOfIntegers.basis E i) • x) : ℤ) : E)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

section Fam

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
  (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ))

def AnLie (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)) : Prop :=
  y.x = Fu.u i Pm ∧ ∀ τ k, IsDerivAt0 (fun w => (Fu.ex i Pm w).left) (z τ k) (y.u τ k)

def AnGen (θ : (Fin g → ℂ) → ℂ) (κ : ℂ) : Prop :=
  ∃ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u i Pm) (fun w => (Fu.ex i Pm w).left) θ fr ∧
    ∀ j z (pt : Sp ℂ ⟶ Gx y.x), pt ≫ gxFst y.x = (Fu.ex i Pm z).left → pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = κ * θ z * fr j z

def IsThetaL2NormSquared (v : ℝ) : Prop :=
  ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
            (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
            Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (Fu.Di i).EF a b) ∧
            (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
            (∀ j z, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
            (∀ j j' z, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
              fr j z = valAt' (Fu.ex i Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
                (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
            (∀ j, ⊤ ≤ (Fu.ex i Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
                (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
            (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
                Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
            (∀ j z (pt : Sp ℂ ⟶ Gx y.x),
              pt ≫ gxFst y.x = (Fu.ex i Pm z).left →
              pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
              ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z) ∧
            MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
            (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
              (MeasureTheory.volume Fd).toReal = v

def IsRiem (Hm : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    ∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (Fu.Di i).EF a b

end Fam

structure UnfWit (U : Unf Xo c σ r) where
  g : ℕ
  e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)
  F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)
  ik : U.Comp → Fin F.n
  φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ
  iso : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))
  Pm : ∀ k, (U.X k).dom → ((F.Di (ik k)).La →+ (Fin g → ℂ))
  Pm_eq : ∀ k x a j, Pm k x a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2
  period : ∀ k x, IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) (Pm k x)
  lie : ∀ k x, AnLie F (ik k) (Pm k x) (U.un k x) (fun τ i => Pi.single (e.symm ⟨τ, i⟩) 1)
  norm : ∀ k (x : (U.X k).dom), (∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) → IsThetaL2NormSquared F (ik k) (Pm k x) (U.un k x) 1

section Hol

variable [Algebra (FractionRing ℂ) ℂ] {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {a : ArcIn Dw l β ℂ (σ.comp β)} {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty} (Ha : HolArc Y σ a χ W Fu)

def AnVec (ν : Out.GtPt a.D₀ (epsR ℂ)) (z₀ : Fin g → ℂ) : Prop :=
  IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left)) z₀ ν.b.left ∧
    ∀ x j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j →
      valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val =
        TrivSqZeroExt.inl (chiVal (Ha.ex₀ 0) x j) +
          TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (Ha.ex₀ z) x j) 0 z₀)

structure ThetaDat (th : a.D₀.P.L.Sec) where
  bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fu.Di Ha.i).La
  S : Finset (Fin g)
  h : Matrix (Fin g) (Fin g) ℂ
  τ : ℂ → Matrix (Fin g) (Fin g) ℂ
  c₁ : Fin g → ℂ
  c₂ : Fin g → ℂ
  κ : ℂ
  sympl : ∀ u v, (Fu.Di Ha.i).EF (bas u) (bas v) = -omegaStd u v
  ker : ∀ u, Ha.y (bas u) = 0 ↔ ∀ k ∈ S, u (.inr k) = 0
  orth : ∀ u, (∀ v', Ha.y v' = 0 → (Fu.Di Ha.i).EF (bas u) v' = 0) ↔
    (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0
  per : ∀ w k, h.mulVec (Ha.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
    h.mulVec (Ha.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1)
  pos : ∀ w, Ha.T < w.im → (τ w).IsSymm ∧ ((τ w).map Complex.im).PosDef
  half₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2
  half₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2
  frame : ∀ w, Ha.T < w.im → ∃ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w))
    (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr
  κ_ne : κ ≠ 0
  c₁_S : ∀ k ∈ S, c₁ k = 0
  onB : ∀ w : ℂ, Ha.T < w.im → IsFnInRigFrame a.D₀ (fun z => (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left)) th
    (fun z => κ * thetaCharOff S (τ w) c₁ c₂ (h.mulVec z))

def AnFr {th : a.D₀.P.L.Sec} (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)) (w : ℂ)
    (y : FrPt Xo c (CAt σ)) : Prop :=
  AnLie Fu Ha.i (Ha.Pw w) y z ∧
    AnGen Fu Ha.i (Ha.Pw w) y (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) Θ.κ

def NormOne : Prop :=
  ∀ w : ℂ, Ha.T < w.im → ∀ Hm, IsRiem Fu Ha.i (Ha.Pw w) Hm →
    ∀ v, (hermForm Hm (Ha.N v) (Ha.N v)).re * w.im = a.be (Ha.y v) (Ha.y v)

end Hol

section Freq

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X)

def LevelPar (N : ℕ) (s : E) : Prop :=
  cc s = s ∧ ∀ x y : X, ∃ m : ℤ, Algebra.trace ℚ E (2 * s * pairE ξ x * cc (pairE ξ y)) = (N : ℚ) * m

def IsBePar (be : LinearMap.BilinForm ℤ X) (s : E) : Prop :=
  cc s = s ∧ ∀ x y : X, Algebra.trace ℚ E (2 * s * pairE ξ x * cc (pairE ξ y)) = (be x y : ℚ)

def BetaAt (N : ℕ) (be : LinearMap.BilinForm ℤ X) (ν₀ : E) (jj : ℤ) : Prop :=
  cc ν₀ = ν₀ ∧ ∀ s, IsBePar ξ be s → Algebra.trace ℚ E (ν₀ * s) = jj ∧
    ∀ ν : E, cc ν = ν → (∀ τ : E →+* ℂ, 0 ≤ (τ ν).re) →
      (∀ s', LevelPar ξ N s' → ∃ m : ℤ, Algebra.trace ℚ E (ν * s') = m) → Algebra.trace ℚ E (ν * s) = jj → ν = ν₀

end Freq

def TransvIn (X : Data E r) (N : ℕ) (la : Wt X.Ψ r) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ s : E, cc s = s →
    (∀ v ∈ X.Λ, ∃ u ∈ X.Λ, (transvMat X.Gm ξ (s * X.κ0)).mulVec v - v = (N : E) • u) →
    ∃ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ (s * X.κ0) ∧ X.χ la γ = 1

variable {K₁ : Type} [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)]

def ajAt (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (F : Rul Xo c) (x : ArcLt Dw → ℂ) : ℂ :=
  ∑ μ ∈ (arcNum (evR Xo c F d.yF)).support,
    ι (((arcNum (evR Xo c F d.yF)).coeff μ).coeff d.jj) * ∏ v ∈ μ.support, x v ^ μ v

def InvBl (x : ArcLt Dw → ℂ) : Prop :=
  ∀ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩).det ≠ 0

end GlobalTheory.ArcQ
