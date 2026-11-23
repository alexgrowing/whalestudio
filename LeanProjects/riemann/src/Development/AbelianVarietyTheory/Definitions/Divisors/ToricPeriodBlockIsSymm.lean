import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex Matrix
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl

section Classical

variable {g : ℕ}

def cv (M : Fin g → ℤ) : Fin g → ℂ := fun i => (M i : ℂ)

def perV (τ : Matrix (Fin g) (Fin g) ℂ) (M N : Fin g → ℤ) : Fin g → ℂ := cv M + τ *ᵥ cv N

def Half (a : Fin g → ℂ) : Prop := ∀ i, a i = 0 ∨ a i = 1 / 2

def autV (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ cv M - b ⬝ᵥ cv N) - Real.pi * Complex.I * (cv N ⬝ᵥ τ *ᵥ cv N) -
    2 * Real.pi * Complex.I * (cv N ⬝ᵥ z))

def trFac (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ) (M N : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (cv N ⬝ᵥ cv M) + Real.pi * Complex.I * (cv N ⬝ᵥ cv M) / (m : ℂ) ^ 2 +
    2 * Real.pi * Complex.I * (a ⬝ᵥ cv M - b ⬝ᵥ cv N) + 2 * Real.pi * Complex.I * (cv N ⬝ᵥ z) +
    Real.pi * Complex.I * (cv N ⬝ᵥ τ *ᵥ cv N) / (m : ℂ) ^ 2)

def trF (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ) (M N : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  trFac τ a b m M N z * thetaChar τ a b ((m : ℂ) • z + (m : ℂ)⁻¹ • perV τ M N)

def NF (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ)
    (W : Fin g → Fin g → ℂ) : Prop :=
  τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ Half a ∧ Half b ∧ c ≠ 0 ∧ (∀ z, z ∈ u.Λ ↔ ∃ M N, z = perV τ M N) ∧
    u.IsRig x.rig ∧ u.IsFn x.th (fun z => c * thetaChar τ a b z) ∧ ∀ j, u.IsDiff (W j) (x.v (j.cast hg.symm))

def FnT {P : PolAV (Sp ℂ)} (u : HolUnif P.A P.L g) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))))
    (f : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (i : P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i →
    valR (ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z)).left ((LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))).U fun _ => i)
      (t.f fun _ => i) = f z * u.fr i z ^ k

end Classical

structure AB (B : NumB ℂ) (g : ℕ) where

  τ : Matrix (Fin g) (Fin g) ℂ

  a : Fin g → ℂ

  b : Fin g → ℂ

  c : ℂ
  symm : τ.IsSymm
  pos : (τ.map Complex.im).PosDef
  ha : Half a
  hb : Half b
  hc : c ≠ 0

  ex : (Fin g → ℂ) → B.A
  ex_add : ∀ z w, ex (z + w) = ex z * ex w
  onto : Function.Surjective ex
  ker : ∀ z, ex z = 1 ↔ ∃ M N, z = perV τ M N

  fr : (Fin g → ℂ) → ℂˣ
  fr_zero : fr 0 = 1
  fr_per : ∀ M N z, (fr z : ℂ) = autV τ a b M N z * fr (z + perV τ M N)
  th : ∀ z, B.th (ex z) = c * thetaChar τ a b z * fr z

def AB.Cub {B : NumB ℂ} {g : ℕ} (d : AB B g) : Prop := ∀ x y z,
  B.θ (d.ex x) (d.ex y) (d.ex z) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) = d.fr (x + y + z) * d.fr x * d.fr y * d.fr z

def AB.Sym {B : NumB ℂ} {g : ℕ} (d : AB B g) : Prop := ∀ x, B.σ (d.ex x) * d.fr x = d.fr (-x)

def co {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (χ : X) : Fin r → ℂ := fun l => (bX.repr χ l : ℂ)

structure CD (N : NumD ℂ) (g r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) extends AB N.toNumB g where
  cub : toAB.Cub
  sym : toAB.Sym

  t12 : Matrix (Fin g) (Fin r) ℂ

  t22 : Matrix (Fin r) (Fin r) ℂ

  b2 : Fin r → ℂ
  toricPeriodBlock_isSymm : t22.IsSymm
  hb2 : Half b2
  c_eq : ∀ χ, N.c χ = ex (t12 *ᵥ co bX χ)
  ψ_eq : ∀ χ, (N.ψ χ : ℂ) * fr (t12 *ᵥ co bX χ) =
    Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ t22 *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2))

namespace CD

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

def full (S : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (Matrix.fromBlocks d.τ d.t12 d.t12ᵀ (d.t22 + S)).submatrix σ σ

def aF : Fin g → ℂ := fun j => Sum.elim d.a 0 (σ j)

def bF : Fin g → ℂ := fun j => Sum.elim d.b d.b2 (σ j)

end CD

def zP {g' r g : ℕ} {A : Type} (σ : Fin g ≃ Fin g' ⊕ Fin r) (Z : Fin g → A) : Fin g' → A := fun i => Z (σ.symm (Sum.inl i))

def tP {g' r g : ℕ} {A : Type} (σ : Fin g ≃ Fin g' ⊕ Fin r) (Z : Fin g → A) : Fin r → A := fun l => Z (σ.symm (Sum.inr l))

namespace CD

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

def IsPt (Z : Fin g → ℂ) (h : N.Gt) : Prop :=
  h.b = d.ex (zP σ Z) ∧ ∀ χ, (h.s χ : ℂ) * d.fr (d.t12 *ᵥ co bX χ + zP σ Z) =
    Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ Z)) * d.fr (d.t12 *ᵥ co bX χ) * d.fr (zP σ Z)

def Rep (k : ℕ) (M Nn : Fin g → ℤ) (p : N.QT k) : Prop :=
  p.1.1.toAdd = ∑ l, tP σ Nn l • bX l ∧ d.IsPt σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn) p.1.2

def fj (S : Matrix (Fin r) (Fin r) ℂ) (χ : N.X) (Z : Fin g → ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ (d.t22 + S) *ᵥ co bX χ) +
    2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ (tP σ Z + d.b2))) * thetaChar d.τ d.a d.b (zP σ Z + d.t12 *ᵥ co bX χ)

def term (S : Matrix (Fin r) (Fin r) ℂ) (m : ℕ) (M Nn : Fin g → ℤ) (χ : N.X) (Z : Fin g → ℂ) : ℂ :=
  trFac (d.full σ S) (d.aF σ) (d.bF σ) m M Nn Z * d.fj σ S χ ((m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn)

end CD

def bmat {N : NumD ℂ} {r k : ℕ} (bX : Module.Basis (Fin r) ℤ N.X) (β : N.Form k) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun l l' => (β.be (bX l) (bX l') : ℂ)

section Geo

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def ptB (ν : NumOf D ℂ N) (d : AB N.toNumB g) (z : Fin g → ℂ) : Sp ℂ ⟶ (DegPre.BF D ℂ).left :=
  (lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z))).left

def IsD (ν : NumOf D ℂ N) (d : AB N.toNumB g) (W : Fin g → ℂ) (b : TE R ℂ ⟶ D.P.A) : Prop :=
  ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U →
    valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left U f =
      TrivSqZeroExt.inl (valF (ptB ν d 0) U f) + TrivSqZeroExt.inr (fderiv ℂ (fun z => valF (ptB ν d z) U f) 0 W)

structure Geo (ν : NumOf D ℂ N) (d : AB N.toNumB g) where

  frG : D.P.L.ι → (Fin g → ℂ) → ℂ
  hol : ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valF (ptB ν d z) U f) {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U}
  fr_hol : ∀ i, DifferentiableOn ℂ (frG i) {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ D.P.L.U i}
  fr_compat : ∀ i j z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j) →
    frG i z = valF (ν.eA (d.ex z)).left (D.P.L.U i ⊓ D.P.L.U j) (D.P.L.g i j).val * frG j z
  fr_eq : ∀ z, (d.fr z : ℂ) * ν.rg = frG (ν.J (ν.eA (d.ex z)).left) z
  dif : ∀ b : TE R ℂ ⟶ D.P.A, redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left → ∃ W, IsD ν d W b

def KeyOK (κ : Rule) (ν : NumOf D ℂ N) (d : AB N.toNumB D.P.g) : Prop :=
  ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (b : Fin D.P.g → (TE R ℂ ⟶ D.P.A)) (MB : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (k₀ : ℂ),
    IsLieBasis vB → (∀ i, (b i).left =
      spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left) →
    (∀ i, IsD ν d ((2 * Real.pi * Complex.I : ℂ)⁻¹ • MB i) (b i)) → BKey κ ν vB k₀ → MB.det ≠ 0 ∧ k₀ * d.c ^ 8 = MB.det ^ 4

end Geo

def AllC (P : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ},
    NumOf D ℂ N → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R), D.PsiEven → D.TauBimult →
    ∀ [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N), P ν

def AllCD (P : ∀ {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}, CD N g' r bX → (Fin g ≃ Fin g' ⊕ Fin r) → Prop) :
    Prop :=
  ∀ (N : NumD ℂ) (g' r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r), P d σ

end GlobalTheory.MBLow.Cl

end
