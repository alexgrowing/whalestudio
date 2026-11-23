import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam.Pad
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor

section Lin

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def horVal (K : Matrix (m ⊕ n) m ℂ) (C : Matrix n (m ⊕ n) ℂ) : ℂ :=
  (Matrix.fromRows (Classical.epsilon fun R : Matrix m (m ⊕ n) ℂ => R * K = 1) C).det

variable {K : Matrix (m ⊕ n) m ℂ} {C : Matrix n (m ⊕ n) ℂ} {R : Matrix m (m ⊕ n) ℂ} {S : Matrix (m ⊕ n) n ℂ}

theorem det_mul_det (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) :
    (Matrix.fromRows R C).det * (Matrix.fromCols K S).det = 1 := by
  rw [← Matrix.det_mul, Matrix.fromRows_mul_fromCols, hR, hS, h, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_one, _root_.one_mul]

theorem horVal_mul (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) :
    horVal K C * (Matrix.fromCols K S).det = 1 := by

  have hR0 : Classical.epsilon (fun R : Matrix m (m ⊕ n) ℂ => R * K = 1) * K = 1 :=
    Classical.epsilon_spec (p := fun R : Matrix m (m ⊕ n) ℂ => R * K = 1) ⟨R, hR⟩
  unfold horVal
  exact det_mul_det h hR0 hS

theorem horVal_eq (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) : horVal K C = (Matrix.fromRows R C).det := by
  have h1 := horVal_mul h hR hS
  have h2 := det_mul_det h hR hS
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h2) (h1.trans h2.symm)

theorem horVal_ne_zero (h : C * K = 0) (hR : R * K = 1) (hS : C * S = 1) : horVal K C ≠ 0 :=
  left_ne_zero_of_mul_eq_one (horVal_mul h hR hS)

end Lin

section Hol

def HolTan {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} (B : Set V)
    (v : V → (Sp (DualNumber ℂ) ⟶ X)) : Prop :=
  ∀ (U : X.Opens) (f : Γ(X, U)), DifferentiableOn ℂ
    (fun b => (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (A := DualNumber ℂ) (v b) U f).snd) {b ∈ B | ⊤ ≤ v b ⁻¹ᵁ U}

def HolAlong {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (N : Set (CxPts p σ))
    (φ : CxPts p σ → ℂ) : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (x : V → CxPts p σ),
    IsOpen B → IsHolTo B (fun b => (x b).1) → Set.MapsTo x B N → DifferentiableOn ℂ (fun b => φ (x b)) B

def logDom (n a : ℕ) : Set (Fin n → ℂ) := {s | ∀ k : Fin n, if (k : ℕ) < a then (s k).re < 0 else ‖s k‖ < 1}

def logExp (a : ℕ) {n : ℕ} (s : Fin n → ℂ) : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.exp (s k) else s k

end Hol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Lattice

scoped instance decEqLetter : DecidableEq (Letter Dw) := Classical.decEq _

abbrev Idx (Dw : Datum H) (τ : E →+* ℂ) : Type := Fin (Dw.mult (conjEmb τ)) ⊕ Fin (Dw.mult τ)

def IsPerBasis (Di : Datum H) {J : Type} [Fintype J] [DecidableEq J] (x : J → Di.La) (hm : Matrix J J E) : Prop :=
  LinearIndependent (𝓞 E) x ∧ (∀ v, ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x)) ∧
    (∀ (a : 𝓞 E) k k', ((Di.EF (a • x k) (x k') : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * hm k k')) ∧ hm.det ≠ 0

def IsIsom (Di : Datum H) (gm : Di.La ≃ₗ[𝓞 E] Di.La) : Prop := ∀ a b, Di.EF (gm a) (gm b) = Di.EF a b

def IsLev (l : Level H) (Di : Datum H) (gm : Di.La ≃ₗ[𝓞 E] Di.La) : Prop :=
  ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Di.La), ∃ e, gm a = a + l.M • e

variable {Di : Datum H}

def perMat {J : Type} (x : J → Di.La) (Q : Di.La →+ (Letter Dw → ℂ)) (ρ : E →+* ℂ) : Matrix (Fin (Dw.mult ρ)) J ℂ :=
  Matrix.of fun i k => Q (x k) ⟨ρ, i⟩

variable (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E)

def kerMat (Q : Di.La →+ (Letter Dw → ℂ)) : Matrix (Idx Dw τ) (Fin (Dw.mult (conjEmb τ))) ℂ :=
  ((hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ)⁻¹ * (perMat x Q (conjEmb τ))ᵀ

def perVal (Q : Di.La →+ (Letter Dw → ℂ)) : ℂ := horVal (kerMat c σ τ x hm Q) (perMat x Q τ)

def GoodPer (Q : Di.La →+ (Letter Dw → ℂ)) : Prop :=
  (∀ (a : 𝓞 E) v (z : Letter Dw), Q (a • v) z = Formalism.L2.PjFree.relab c σ z.1 (a : E) * Q v z) ∧
    perMat x Q τ * kerMat c σ τ x hm Q = 0 ∧
    (∃ R : Matrix (Fin (Dw.mult (conjEmb τ))) (Idx Dw τ) ℂ, R * kerMat c σ τ x hm Q = 1) ∧
    ∃ S : Matrix (Idx Dw τ) (Fin (Dw.mult τ)) ℂ, perMat x Q τ * S = 1

variable {c σ τ x hm}

theorem GoodPer.perVal_ne_zero {Q : Di.La →+ (Letter Dw → ℂ)} (h : GoodPer c σ τ x hm Q) : perVal c σ τ x hm Q ≠ 0 := by
  obtain ⟨-, h1, ⟨R, hR⟩, ⟨S, hS⟩⟩ := h
  exact horVal_ne_zero h1 hR hS

end Lattice

variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (σ : c.F →+* ℂ)

abbrev CxFr : Type := Σ x : CxPts (genStr Z) σ, EigFrame Z σ (x.1 ≫ genι Z)

variable {Z σ}

def Inner (x : CxPts (genStr Z) σ) : Prop := x.1 (IsLocalRing.closedPoint ℂ) ∉ genBd Z

def Chg (a a' : CxFr Z σ) (ρ : E →+* ℂ) (M : Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) ℂ) : Prop :=
  a.1 = a'.1 ∧ ∀ i, IsCombAtG Z.t (a'.1.1 ≫ genι Z) (a.2.v ρ) (M i) (a'.2.v ρ i)

def HolFam {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (a : V → CxFr Z σ) : Prop :=
  IsHolTo B (fun b => (a b).1.1) ∧ ∀ ρ i, HolTan B fun b => (a b).2.v ρ i

def Dirs {g : ℕ} (a : CxFr Z σ) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left)) (W : Letter Dw → Fin g → ℂ) : Prop :=
  ∀ z : Letter Dw, IsDerivAt0 e (W z) (a.2.v z.1 z.2)

abbrev Fam (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) {g : ℕ} (e : Fin g ≃ Letter Dw) : Type 1 :=
  FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) fun j => Formalism.L2.PjFree.relab c σ (e j).1

def Per {g : ℕ} {e : Fin g ≃ Letter Dw} (Fu : Fam Xo c σ e) (a : CxFr Z σ) (i : Fin Fu.n)
    (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) : Prop :=
  ∃ (P : (Fu.Di i).La →+ (Fin g → ℂ)) (W : Letter Dw → Fin g → ℂ) (y : Sp ℂ ⟶ Xo.XF c),
    IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P ∧ y ≫ pullback.fst _ _ = Fu.u i P ∧
    y ≫ Z.jQ = a.1.1 ∧
    (∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ)) ∧
    ∀ v, P v = ∑ z, Q v z • W z

open Classical in

def horOf {g : ℕ} {e : Fin g ≃ Letter Dw} (Fu : Fam Xo c σ e) (τ : E →+* ℂ) (x : ∀ i, Idx Dw τ → (Fu.Di i).La)
    (hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E) (a : CxFr Z σ) : ℂ :=
  if h : ∃ iQ : Σ i : Fin Fu.n, (Fu.Di i).La →+ (Letter Dw → ℂ), Per Fu a iQ.1 iQ.2 then
    perVal c σ τ (x h.choose.1) (hm h.choose.1) h.choose.2 else 0

def LogGrowth (h : CxFr Z σ → ℂ) : Prop :=
  ∀ x₀ : CxPts (genStr Z) σ, ∃ (N : Set (CxPts (genStr Z) σ)) (φ : CxPts (genStr Z) σ → ℂ), IsOpen N ∧ x₀ ∈ N ∧
    HolAlong N φ ∧ (∀ x ∈ N, φ x ≠ 0 ↔ Inner x) ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ),
      IsOpen B → HolFam B a → (∀ b ∈ B, (a b).1 ∈ N) → ∀ b₀ ∈ B, ∃ (C : ℝ) (k : ℕ), ∀ᶠ b in 𝓝 b₀, Inner (a b).1 →
        ‖h (a b)‖ ≤ C * (1 + |Real.log ‖φ (a b).1‖|) ^ k ∧ ‖(h (a b))⁻¹‖ ≤ C * (1 + |Real.log ‖φ (a b).1‖|) ^ k

def HorFn (τ : E →+* ℂ) (h : CxFr Z σ → ℂ) : Prop :=
  (∀ a, Inner a.1 → h a ≠ 0) ∧
  (∀ a a' M N, Inner a.1 → Chg a a' τ M → Chg a a' (conjEmb τ) N → h a' * M.det = h a * N.det) ∧
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ),
    IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → DifferentiableOn ℂ (fun b => h (a b)) B) ∧
  LogGrowth h

abbrev ExpMaps (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) : Type :=
  ∀ x : CxPts (genStr Z) σ, (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)

def IsExpChart {n g : ℕ} (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) : Prop :=
  e.target = Metric.ball 0 1 ∧ (∀ k, HolAlong e.source fun x => e x k) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧
  (∀ x ∈ e.source, ∀ v w, ex x (v + w) = ex x v * ex x w) ∧
  IsHolTo (e.target ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun zw => (ex (e.symm zw.1) zw.2).left) ∧
  ∀ x ∈ e.source, (∀ w, ∃! v, IsTanAtG Z.t (x.1 ≫ genι Z) v ∧ IsDerivAt0 (fun u => (ex x u).left) w v) ∧
    ∀ v, IsTanAtG Z.t (x.1 ≫ genι Z) v → ∃! w, IsDerivAt0 (fun u => (ex x u).left) w v

def IsLogChart {n g r : ℕ} (a : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g)
    (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ) : Prop :=
  IsExpChart e ex ∧ (∀ x ∈ e.source, Inner x ↔ ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0) ∧
  ContinuousOn lam (logDom n a) ∧
  (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧
    (∀ w, ex (e.symm (logExp a s)) w = 1 ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧
    ∀ j, ∑ m, ρ j m • lam s m = Pi.single j 1) ∧
  ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) →
    ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k

end GlobalTheory.ShFam.Hor
