import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

def mulDeg {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (n : ℕ) : DegPre R :=
  { D with
    c := fun y => D.c (n • y)
    c_add := fun a b => by rw [nsmul_add, D.c_add]
    psi := fun y => D.psi (n • y)
    psi_gen := fun y => D.psi_gen (n • y) }

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def lowMap {l : Geo.Tor.Level H} (c : Coeff l) {A : Type} [CommRing A] (b : c.F →+* A) : Sp A ⟶ Sp (KA (LowDat.lowLevel l)) :=
  spMap (b.comp (IntermediateField.inclusion (LowDat.ka_le l c)).toRingHom)

abbrev LowObj (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) {A : Type} [CommRing A] (b : c.F →+* A) :=
  Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (lowMap c b)

def IsAbPart {A : Type} [CommRing A] [IsDomain A] (t : SAB H (Sp A)) (Q : DegPre A) [Module (𝓞 E) Q.X]
    (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (φB : t.G.left ⟶ Q.P.A.left) : Prop :=
  IsGrpPullback t.G Q.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (t.act.act x).left ≫ φB = φB ≫ (oQ.onB.act x).left) ∧
    ∃ w : LB.Iso t.PP.L (Q.P.L.pull φB), w.IsGen

structure LowBase (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) where

  W : Type
  [ring : CommRing W]
  [dom : IsDomain W]
  [reg : IsRegularLocalRing W]

  b : c.F →+* W
  ft : b.EssFiniteType

  o : LowObj D' c b

  D : DegPre W
  [mod : Module (𝓞 E) D.X]

  oa : letI := H.starRing; D.OAct (𝓞 E)
  even : D.PsiEven
  bimult : D.TauBimult
  gen : ∀ y, PsiUnitOn D y Set.univ
  w0 : letI := H.starRing; TraceFormTwistIso D oa H.w0

  φB : o.t.G.left ⟶ D.P.A.left
  ab : IsAbPart o.t D oa φB
  fineRed : ∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b →
    ∀ (o' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o' o (spMap f₁)) (m₂ : ObjMap o' o (spMap f₂))
      (x : D.X → (Sp A ⟶ o'.t.G.left)), (∀ y, x y ≫ m₁.toSABMap.φ ≫ φB = spMap f₁ ≫ (D.c y).left) →
      (∀ y, x y ≫ m₂.toSABMap.φ ≫ φB = spMap f₂ ≫ (D.c y).left) → (∀ y, x y ≫ o'.t.G.hom = 𝟙 _) → f₁ = f₂
  fineEps : ∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o' : LowObj D' c (f.comp b)) (m₁ : ObjMap o' o (spMap f))
      (m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f))) (x : D.X → (Sp (DualNumber k) ⟶ o'.t.G.left)),
      (∀ y, x y ≫ m₁.toSABMap.φ ≫ φB = spMap f ≫ (D.c y).left) →
      (∀ y, x y ≫ m₂.toSABMap.φ ≫ φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (D.c y).left) →
      (∀ y, x y ≫ o'.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f
  dim : letI := ((residue W).comp b).toAlgebra
    ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧
      a + t = D'.dim + Module.finrank (𝓞 E) D.X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))

attribute [instance] LowBase.ring LowBase.dom LowBase.reg LowBase.mod

def DivFrom {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V]
    (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I]
    (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) : Prop :=
  ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g)),
    (∀ y, (((g y)⁻¹ : (FractionRing V)ˣ) : FractionRing V) =
      ∏ k, algebraMap V (FractionRing V) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y))) ∧
    (∀ y : Q.X, hD.xe y = e y) ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (oQ.onB.act x).left ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) ≫ (L.oa.onB.act x).left)

variable {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}
  {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

structure Canon (C : MonoFam Xo c φ R) where

  D' : Datum H
  hp : D'.p + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.p
  hq : D'.q + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.q

  L : LowBase D' c

  N : ℕ

  ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)

  e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X
  cone : ∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)

  ψ : MvPolynomial (Fin C.m ⊕ Fin N) L.W →+* R
  compl : GlobalTheory.TChart.IsComplAt ψ
  ψ_loc : IsLocalHom (ψ.comp MvPolynomial.C)
  base : (ψ.comp MvPolynomial.C).comp L.b = C.b
  bd : ∀ i, ψ (MvPolynomial.X (.inl i)) = C.s i
  tor : ∀ k, IsUnit (ψ (MvPolynomial.X (.inr k)))
  data : DivFrom L C.P.D.toPre C.P.oD (ψ.comp MvPolynomial.C) (fun k => ψ (MvPolynomial.X k))
    (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e

def PointRigidB (C : MonoFam Xo c φ R) (τ₀ : Gens C.P.D.toPre) {N : ℕ} (s : Fin C.m ⊕ Fin N → R) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) → SepAtB C.P.D.toPre τ₀ s ev k₀ →
    (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀

def HasRigidCoords (C : MonoFam Xo c φ R) : Prop :=
  ∃ (N : ℕ) (s : Fin C.m ⊕ Fin N → R) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X))
    (τ₀ : Gens C.P.D.toPre), (∀ i, s (.inl i) = C.s i) ∧ (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) ∧
    (∀ k, IsUnit (s (.inr k))) ∧
    TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
      (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) ∧
    PointRigidB C τ₀ s

def IsTautB {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)) : Prop :=
  IsTaut C ∧ HasRigidCoords C

def Through {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (C : MonoFam Xo c φ V) (C₁ : MonoFam Xo c φ R)
    (θ : R →+* V) : Prop :=
  ∃ (yo : Sp (Localization.Away (∏ i, C₁.s i)) ⟶ Xo.XF c)
    (κ : Sp (FractionRing V) ⟶ Sp (Localization.Away (∏ i, C₁.s i))),
    (∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, C₁.s i)),
      g ≫ spMap (algebraMap R (Localization.Away (∏ i, C₁.s i))) = jK R → g ≫ yo = C₁.y) ∧
    κ ≫ spMap (algebraMap R (Localization.Away (∏ i, C₁.s i))) = jK V ≫ spMap θ ∧ κ ≫ yo = C.y

end GlobalTheory.UCanon
