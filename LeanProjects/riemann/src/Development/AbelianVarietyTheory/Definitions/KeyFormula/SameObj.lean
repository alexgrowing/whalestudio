import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyEq

def Val (x : KeyIn ℂ) (t : ℂ) : Prop :=
  ∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
    charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8

def Eqv (x : KeyIn ℂ) : Prop :=
  ∀ (f : ℂ →+* ℂ) (x' : KeyIn ℂ) (t t' : ℂ), KeyPB x' x f → Val x t → Val x' t' → t' = f t

def Nrm (x : KeyIn ℂ) {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) : Prop :=
  ∃ (h : x.P.g = g) (M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ), c ≠ 0 ∧
    NormalAt x (τ.submatrix (Fin.cast h) (Fin.cast h)) M (fun i => a (i.cast h)) (fun i => b (i.cast h)) c

def HasPer (x : KeyIn ℂ) {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∃ a b : Fin g → ℂ, charHalf g a b ∧ Nrm x τ a b

def frac {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (m n : Fin g → ℤ) : Fin g → ℂ :=
  (k : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))

def trl {S : Scheme.{0}} (A : Over S) [GrpObj A] (p : 𝟙_ (Over S) ⟶ A) : A ⟶ A := (toUnit A ≫ p) * 𝟙 A

def IsTrl (x' x : KeyIn ℂ) (p : 𝟙_ (Over (Sp ℂ)) ⟶ x.P.A) (ν : ℂˣ) : Prop :=
  ∃ (φ : x'.P.A ≅ x.P.A) (hg : x'.P.g = x.P.g) (w : LB.Iso x'.P.L (x.P.L.pull (φ.hom ≫ trl x.P.A p).left))
    (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ 2).left, 𝟙 x.P.A.left] ![1, -4]))
    (rp : LB.Gen (x.P.L.pull p.left)),
    p ^ 2 = 1 ∧ IsMonHom φ.hom ∧ w.IsGen ∧ mu.IsGen ∧ rp.IsGen ∧
    (∀ i, x'.v i ≫ φ.hom = x.v (i.cast hg)) ∧
    (∀ (z : x'.P.A.left) (j : x.P.L.ι) (k : x'.P.L.ι), (φ.hom ≫ trl x.P.A p).left z ∈ x.P.L.U j → z ∈ x'.P.L.U k →
      gs (φ.hom ≫ trl x.P.A p).left z (x.P.L.U j) (x.th.f j) =
        (gw w (𝟙 _) z j k).val * gs (𝟙 _) z (x'.P.L.U k) (x'.th.f k)) ∧
    (∀ (q : (𝟙_ (Over (Sp ℂ))).left) J J', Good x.P.L q J → Good x'.P.L q J' →
      val rp (𝟙 _) q J = gw w (eSec x'.P.A) q (J (𝟙 _ ≫ p.left)) (J' (𝟙 _ ≫ eSec x'.P.A)) * val x'.rig (𝟙 _) q J') ∧
    (∀ (q : (𝟙_ (Over (Sp ℂ))).left) J, Good x.P.L q J → val mu (eSec x.P.A) q J = val x.rig (𝟙 _) q J ^ (-3 : ℤ)) ∧
    ∀ (q : (𝟙_ (Over (Sp ℂ))).left) J, Good x.P.L q J →
      val mu p.left q J = gm (𝟙 _) q ⊤ (show Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ from unitOn ν) * val x.rig (𝟙 _) q J * val rp (𝟙 _) q J ^ (-4 : ℤ)

variable {S : Type} [CommRing S]

def ExpAt (P : Out.PolAV (Sp S)) (s : S →+* ℂ) {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (e : (Fin g → ℂ) → (Sp ℂ ⟶ P.A.left)) : Prop :=
  ∃ (Q : Out.PolAV (Sp ℂ)) (u : HolUnif Q.A Q.L g) (φ : Q.A.left ⟶ P.A.left), Q.g = g ∧
    IsGrpPullback Q.A P.A (spMap s) φ ∧ LBIso Q.L (P.L.pull φ) ∧
    (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
    ∀ z, e z = (u.ex z).left ≫ φ

def FibU (P : Out.PolAV (Sp S)) (s : S →+* ℂ) {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (e : (Fin g → ℂ) → (Sp ℂ ⟶ P.A.left)) : Prop :=
  ∃ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ P.A.left) (a b : Fin g → ℂ),
    charHalf g a b ∧ Wit x h u τ a b ∧ IsGrpPullback x.P.A P.A (spMap s) φ ∧ LBIso x.P.L (P.L.pull φ) ∧
    ∀ z, e z = (u.ex z).left ≫ φ

def SameObj (P : Out.PolAV (Sp S)) {I : Type} (lev : I → (𝟙_ (Over (Sp S)) ⟶ P.A)) (s s' : S →+* ℂ) : Prop :=
  ∃ (Q Q' : Out.PolAV (Sp ℂ)) (φ : Q.A.left ⟶ P.A.left) (φ' : Q'.A.left ⟶ P.A.left) (ψ : Q.A ≅ Q'.A),
    IsGrpPullback Q.A P.A (spMap s) φ ∧ LBIso Q.L (P.L.pull φ) ∧
    IsGrpPullback Q'.A P.A (spMap s') φ' ∧ LBIso Q'.L (P.L.pull φ') ∧ IsMonHom ψ.hom ∧
    (letI := Q.isAb.comm; letI := Q'.isAb.comm;
      LBIso (abelian₂ Q.A Q.L) ((abelian₂ Q'.A Q'.L).pull (ψ.hom ⊗ₘ ψ.hom).left)) ∧
    ∀ (a : I) (q : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A), q.left ≫ φ = spMap s ≫ (lev a).left →
      (q ≫ ψ.hom).left ≫ φ' = spMap s' ≫ (lev a).left

def TwoLev {X : Scheme.{0}} (A : Over X) [GrpObj A] {C : Type} [CommGroup C] (i : C →* (𝟙_ (Over X) ⟶ A)) : Prop :=
  (∀ c, i c ≫ Out.mulA A 2 = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ X),
      (∀ x : Over.mk t ⟶ A, x ≫ Out.mulA A 2 = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧
        ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1

def Versal : Prop :=
  ∀ (g : ℕ) (τ₀ : Matrix (Fin g) (Fin g) ℂ), 1 ≤ g → τ₀.IsSymm → (τ₀.map Complex.im).PosDef →
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra ℂ S) (y : KeyIn S), Algebra.Smooth ℂ S ∧
      ∀ᶠ τ in nhdsWithin τ₀ {τ | τ.IsSymm}, ∃ (s : S →ₐ[ℂ] ℂ) (x : KeyIn ℂ), KeyPB x y s.toRingHom ∧ HasPer x τ

end GlobalTheory.KeyEq
end
