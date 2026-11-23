import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Development.AutomorphicArithmetic.CommutativeAlgebra.LevDefs

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt)
open scoped TensorProduct

universe u

namespace UpperTheory.Gal.G3

section Defs

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {R : Type} [CommRing R] [Algebra ℚ R]
  {gb : GBase D.toG R}

def AdmK (N' N : ℕ) (h : G.GAf) : Prop := ∀ u ∈ L.KN N', h * u * h⁻¹ ∈ L.KN N

def mul (h : G.GAf) : AfP p := (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)

def IsMult (a : AfP p) (c : ℕ) : Prop := ∃ t t' : AfP p, IsIntAf t ∧ IsIntAf t' ∧ t * t' = 1 ∧ a = (c : AfP p) * t

def Ind {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k] {t : Sp k ⟶ S}
    (I : Int.Geo.TIso o t) : Prop := ∀ y, toUnit _ ≫ o.eta y = I.ev N y

def Rel {S : Scheme.{0}} {s : S ⟶ Sp R} {N N' : ℕ} {o' : GObj gb N' s} {o : GObj gb N s} {k : Type} [Field k] {t : Sp k ⟶ S}
    (I : Int.Geo.TIso o' t) (J : Int.Geo.TIso o t) (ψ : o'.A ⟶ o.A) (h : G.GAf) : Prop :=
  ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La,
    I.ev n x ≫ ψ = J.ev n y ↔ ∃ v ∈ LaHat D, L.actG h (inAf D x) = inAf D y + n • v

def Wit (h : G.GAf) {N N' : ℕ} (X' : GenModel gb N') (X : GenModel gb N) (π : X'.X ⟶ X.X)
    (Φ : X'.univ.A.left ⟶ X.univ.A.left) : Prop :=
  π ≫ X.s = X'.s ∧ ∃ (o : GObj gb N X'.s) (ψ : X'.univ.A ⟶ o.A) (φ : GObjMap o X.univ π),
    IsTrans L h X'.univ o ψ ∧ Φ = ψ.left ≫ φ.φ

theorem Wit.w {L : Link D G} {h : G.GAf} {N N' : ℕ} {X' : GenModel gb N'} {X : GenModel gb N} {π : X'.X ⟶ X.X}
    {Φ : X'.univ.A.left ⟶ X.univ.A.left} (H : Wit L h X' X π Φ) : Φ ≫ X.univ.A.hom = X'.univ.A.hom ≫ π := by
  obtain ⟨-, o, ψ, φ, -, rfl⟩ := H
  rw [Category.assoc, φ.cart.1.w, ← Category.assoc, Over.w]

variable (D) in

def IsSys (f : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k : ℕ) : Prop :=
  c.Coprime p ∧ k.Coprime p ∧ c ∣ k ^ 2 ∧
  (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, f n (a • x) = a • f n x + n • z) ∧
  (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, f (n * m) x = f n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) ∧
  (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (f n x) (f n y) - c * u n * D.EF x y) ∧
  (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, f n y = k • x + n • z)

end Defs

def NuInt : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (h : G.GAf), Integ L h → IsIntAf (mul h)

def MultBasic : Prop := ∀ (p : ℕ) [Fact p.Prime],
  (∀ (a : AfP p) (c c' : ℕ), c.Coprime p → c'.Coprime p → IsMult a c → IsMult a c' → c = c') ∧
  (∀ (a a' : AfP p) (c c' : ℕ), IsMult a c → IsMult a' c' → IsMult (a * a') (c * c')) ∧
  ∀ (D : Datum p) (G : HTGroup p) (L : Link D G), ∀ u ∈ L.KN 1, IsMult (mul u) 1

def KNBasic : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (N : ℕ),
  (∀ k ∈ L.KN 1, AdmK L N N k) ∧ (∀ g : G.GAf, ∃ c : ℕ, c.Coprime p ∧ AdmK L (N * c) N g) ∧
  ∀ M : ℕ, 0 < N → 0 < M → (L.KN M).relIndex (L.KN N) ≠ 0

def SysOf : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (h : G.GAf), Integ L h →
  ∃ (f : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k : ℕ), IsSys D f u c k ∧ IsMult (mul h) (k ^ 2 / c) ∧
    (∀ v ∈ LaHat D, k • L.actG h⁻¹ v ∈ LaHat D) ∧ ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, L.actG h (inAf D (f n x)) = k • inAf D x + n • w

def AdmOf : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (h : G.GAf) (k N : ℕ), Integ L h → 0 < k →
  (∀ v ∈ LaHat D, k • L.actG h⁻¹ v ∈ LaHat D) → AdmK L (N * k) N h

def KNCong : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (N : ℕ), 0 < N → N.Coprime p →
  ∀ u ∈ L.KN 1, (∀ x : D.La, ∃ w ∈ LaHat D, L.actG u (inAf D x) = inAf D x + N • w) → u ∈ L.KN N

def GSimOf : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), ∀ u ∈ L.KN 1,
  ∃ g : UpperTheory.Lev.GSim D.toG, ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, L.actG u (inAf D x) = inAf D (g.f n x) + n • w

def RelComp : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S : Scheme.{0}) (s : S ⟶ Sp R) (N₁ N₂ N₃ : ℕ) (o₁ : GObj gb N₁ s) (o₂ : GObj gb N₂ s) (o₃ : GObj gb N₃ s)
  (k : Type) [Field k] (t : Sp k ⟶ S) (I₁ : Int.Geo.TIso o₁ t) (I₂ : Int.Geo.TIso o₂ t) (I₃ : Int.Geo.TIso o₃ t)
  (ψ₁ : o₁.A ⟶ o₂.A) (ψ₂ : o₂.A ⟶ o₃.A) (h₁ h₂ : G.GAf), IsMonHom ψ₁ → IsMonHom ψ₂ → Integ L h₂ →
  Rel L I₁ I₁ (𝟙 _) 1 ∧ (Rel L I₁ I₂ ψ₁ h₁ → Rel L I₂ I₃ ψ₂ h₂ → Rel L I₁ I₃ (ψ₁ ≫ ψ₂) (h₂ * h₁))

def TateDiff : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S : Scheme.{0}) (s : S ⟶ Sp R) (N : Lv p) (o : GObj gb N.1 s) (k : Type) [Field k] [IsAlgClosed k]
  (t : Sp k ⟶ S) (I J : Int.Geo.TIso o t), Ind o I → Ind o J → ∃ u ∈ L.KN N.1, Rel L I J (𝟙 _) u

def TateTwist : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S : Scheme.{0}) (s : S ⟶ Sp R) (N : Lv p) (o : GObj gb N.1 s) (k : Type) [Field k]
  (t : Sp k ⟶ S) (I : Int.Geo.TIso o t), Ind o I → ∀ u ∈ L.KN N.1, ∃ J : Int.Geo.TIso o t, Ind o J ∧ Rel L I J (𝟙 _) u

def FullOf : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S : Scheme.{0}) (s : S ⟶ Sp R) (N : ℕ) (o : GObj gb N s) (k : Type) [Field k] [IsAlgClosed k]
  (t : Sp k ⟶ S) (J : TateIsoO D k (Over.mk t ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))),
  ∃ I : Int.Geo.TIso o t, ∀ n, 0 < n → n.Coprime p → ∀ x, I.ev n x = J.ev n x

def RelArith : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S : Scheme.{0}) (s : S ⟶ Sp R) (N N' : ℕ) (o' : GObj gb N' s) (o : GObj gb N s) (K : Type) [Field K]
  (t : Sp K ⟶ S) (I : Int.Geo.TIso o' t) (J : Int.Geo.TIso o t) (ψ : o'.A ⟶ o.A) (h : G.GAf) (f : ℕ → D.La →+ D.La) (u : ℕ → ℤ)
  (c k : ℕ), IsMonHom ψ → Integ L h → IsSys D f u c k →
  (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, L.actG h (inAf D (f n x)) = k • inAf D x + n • w) →
  (∀ n, 0 < n → n.Coprime p → ∀ x, J.ev n x = I.ev (n * k) (f (n * k) x) ≫ ψ) → Rel L I J ψ h

def TransSelf : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S : Scheme.{0}) (s : S ⟶ Sp R) (N : Lv p),
  (∀ (o : GObj gb N.1 s), ∀ u ∈ L.KN N.1, IsTrans L u o o (𝟙 _)) ∧
  ∀ (c : ℕ) (hN : 0 < N.1) (hc : 0 < c) (o : GObj gb (N.1 * c) s), IsTrans L 1 o (o.forgetMul hN hc) (𝟙 o.A)

def TransComp : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S : Scheme.{0}) (s : S ⟶ Sp R) (N₁ : ℕ) (N₂ N₃ : Lv p) (o₁ : GObj gb N₁ s) (o₂ : GObj gb N₂.1 s)
  (o₃ : GObj gb N₃.1 s) (ψ₁ : o₁.A ⟶ o₂.A) (ψ₂ : o₂.A ⟶ o₃.A) (h₁ h₂ : G.GAf), Integ L h₂ → AdmK L N₂.1 N₃.1 h₂ →
  IsTrans L h₁ o₁ o₂ ψ₁ → IsTrans L h₂ o₂ o₃ ψ₂ → IsTrans L (h₂ * h₁) o₁ o₃ (ψ₁ ≫ ψ₂)

def HomPull : Prop := ∀ (G₀ : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase G₀ R) (S S' : Scheme.{0}) (s : S ⟶ Sp R)
  (s' : S' ⟶ Sp R) (f : S' ⟶ S) (N₁ N₂ : ℕ) (o₁ : GObj gb N₁ s) (o₂ : GObj gb N₂ s) (o₁' : GObj gb N₁ s') (o₂' : GObj gb N₂ s')
  (m₁ : GObjMap o₁' o₁ f) (m₂ : GObjMap o₂' o₂ f) (ψ : o₁.A ⟶ o₂.A), ∃ ψ' : o₁'.A ⟶ o₂'.A, ψ'.left ≫ m₂.φ = m₁.φ ≫ ψ.left ∧
    (IsMonHom ψ → IsMonHom ψ') ∧
    ((∀ c, o₁.act.act c ≫ ψ = ψ ≫ o₂.act.act c) → ∀ c, o₁'.act.act c ≫ ψ' = ψ' ≫ o₂'.act.act c) ∧
    ∀ c : ℕ, Nonempty (LBIso (Hecke.lbPow o₁.P c) (o₂.P.pull (Hecke.sq2 ψ))) →
      Nonempty (LBIso (Hecke.lbPow o₁'.P c) (o₂'.P.pull (Hecke.sq2 ψ')))

def TatePull : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
  (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (N : ℕ) (o : GObj gb N s) (o' : GObj gb N s')
  (m : GObjMap o' o f) (k : Type) [Field k] (t : Sp k ⟶ S'),
  (∀ I : Int.Geo.TIso o (t ≫ f), ∃ I' : Int.Geo.TIso o' t, (Ind o I → Ind o' I') ∧ ∀ n x, (I'.ev n x).left ≫ m.φ = (I.ev n x).left) ∧
  ∀ I' : Int.Geo.TIso o' t, ∃ I : Int.Geo.TIso o (t ≫ f), (Ind o' I' → Ind o I) ∧ ∀ n x, (I'.ev n x).left ≫ m.φ = (I.ev n x).left

def TransPull : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S), f ≫ s = s' → ∀ (N₁ N₂ : ℕ)
  (o₁ : GObj gb N₁ s) (o₂ : GObj gb N₂ s) (o₁' : GObj gb N₁ s') (o₂' : GObj gb N₂ s') (m₁ : GObjMap o₁' o₁ f)
  (m₂ : GObjMap o₂' o₂ f) (ψ : o₁.A ⟶ o₂.A) (h : G.GAf), IsTrans L h o₁ o₂ ψ →
  ∃ ψ' : o₁'.A ⟶ o₂'.A, IsTrans L h o₁' o₂' ψ' ∧ ψ'.left ≫ m₂.φ = m₁.φ ≫ ψ.left

def TransOfMap : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S : Scheme.{0}) (s : S ⟶ Sp R) (N : Lv p) (o o' : GObj gb N.1 s) (m : GObjMap o o' (𝟙 S)),
  ∃ θ : o.A ⟶ o'.A, θ.left = m.φ ∧ IsTrans L 1 o o' θ

def Rigid : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
  (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S), f ≫ s = s' → ∀ (N : Lv p) (o : GObj gb N.1 s)
  (o' : GObj gb N.1 s') (m m' : GObjMap o' o f), m.φ = m'.φ

def IsogFEt : Prop := ∀ (R : Type) [CommRing R] [Algebra ℚ R] (S : Scheme.{0}) (_ : S ⟶ Sp R) (A A' : Over S) [GrpObj A]
  [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ (ψ : A ⟶ A') (ψ' : A' ⟶ A) (d : ℕ),
  0 < d → IsMonHom ψ → IsMonHom ψ' → ψ ≫ ψ' = (𝟙 A) ^ d → ψ' ≫ ψ = (𝟙 A') ^ d →
  IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left

def TransKer : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S : Scheme.{0}) (s : S ⟶ Sp R) (N' N : Lv p) (o : GObj gb N'.1 s) (o₁ o₂ : GObj gb N.1 s)
  (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A) (h : G.GAf), Integ L h → AdmK L N'.1 N.1 h → IsTrans L h o o₁ ψ₁ → IsTrans L h o o₂ ψ₂ →
  ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S),
    (∀ a : Over.mk t ⟶ o.A, a ≫ ψ₁ = 1 ↔ a ≫ ψ₂ = 1) ∧
    ∀ (a : Over.mk t ⟶ o.A) (y : D.La), a ≫ ψ₁ = toUnit _ ≫ o₁.eta y ↔ a ≫ ψ₂ = toUnit _ ≫ o₂.eta y

def QuotUniq : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (A A₁ A₂ : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj A₁]
  [IsCommMonObj A₁] [GrpObj A₂] [IsCommMonObj A₂], IsAbelianScheme A → IsAbelianScheme A₁ → IsAbelianScheme A₂ →
  ∀ (ψ₁ : A ⟶ A₁) (ψ₂ : A ⟶ A₂), IsMonHom ψ₁ → IsMonHom ψ₂ → IsFinite ψ₁.left → Etale ψ₁.left → Surjective ψ₁.left →
  IsFinite ψ₂.left → Etale ψ₂.left → Surjective ψ₂.left →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp k) (a : Over.mk t ⟶ A), a ≫ ψ₁ = 1 ↔ a ≫ ψ₂ = 1) →
  ∃ θ : A₁ ⟶ A₂, IsIso θ ∧ IsMonHom θ ∧ ψ₁ ≫ θ = ψ₂

def PolUniq : Prop := ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'],
  IsAbelianScheme A → IsAbelianScheme A' → ∀ (ψ : A ⟶ A'), IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left →
  ∀ P Q : LB (G2 A').left, P.IsLB → Q.IsLB →
  (∃ t : (P.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) →
  (∃ t : (Q.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) →
  LBIso (P.pull (Hecke.sq2 ψ)) (Q.pull (Hecke.sq2 ψ)) → LBIso P Q

def MapOfIso : Prop := ∀ (G₀ : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase G₀ R) (S : Scheme.{0}) (s : S ⟶ Sp R)
  (N : ℕ) (o o' : GObj gb N s) (θ : o.A ⟶ o'.A), IsIso θ → IsMonHom θ → (∀ c, o.act.act c ≫ θ = θ ≫ o'.act.act c) →
  LBIso o.P (o'.P.pull (Hecke.sq2 θ)) → (∀ y, o.eta y ≫ θ = o'.eta y) → ∃ m : GObjMap o o' (𝟙 S), m.φ = θ.left

def TransUniqPt : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ Sp R) (N' N : Lv p) (o : GObj gb N'.1 s)
  (o₁ o₂ : GObj gb N.1 s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A) (h : G.GAf), Integ L h → AdmK L N'.1 N.1 h →
  IsTrans L h o o₁ ψ₁ → IsTrans L h o o₂ ψ₂ → ∃ m : GObjMap o₁ o₂ (𝟙 _), ψ₁.left ≫ m.φ = ψ₂.left

def TransDeep : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (h : G.GAf), Integ L h → ∃ k : ℕ, k.Coprime p ∧ (∀ N, AdmK L (N * k) N h) ∧ ∀ (N : Lv p) (S : Scheme.{0}) [IsLocallyNoetherian S]
  (s : S ⟶ Sp R) (o' : GObj gb (N.1 * k) s), ∃ (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L h o' o ψ

def TransIso : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S : Scheme.{0}) (s : S ⟶ Sp R) (N' N : ℕ) (o' : GObj gb N' s) (o : GObj gb N s) (ψ : o'.A ⟶ o.A),
  ∀ u ∈ L.KN 1, IsTrans L u o' o ψ → IsIso ψ

def TransOrbit : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ Sp R) (N' N : Lv p) (o₁ o₂ : GObj gb N'.1 s)
  (o : GObj gb N.1 s) (ψ₁ : o₁.A ⟶ o.A) (ψ₂ : o₂.A ⟶ o.A), IsTrans L 1 o₁ o ψ₁ → IsTrans L 1 o₂ o ψ₂ →
  ∃ u ∈ L.KN N.1, ∃ θ : o₁.A ⟶ o₂.A, IsTrans L u o₁ o₂ θ ∧ θ ≫ ψ₂ = ψ₁

def TransFree : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ Sp R) (N : Lv p) (o : GObj gb N.1 s),
  ∀ u ∈ L.KN 1, IsTrans L u o o (𝟙 _) → u ∈ L.KN N.1

def GenSm : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [Field R] [Algebra ℚ R] (gb : GBase D.toG R) (N : Lv p)
  (X : GenModel gb N.1), Smooth X.s ∧ IsSeparated X.s ∧ QuasiCompact X.s ∧ (D.CompactB → IsProjOver X.s)

def PowSm : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [Field R] [Algebra ℚ R] (gb : GBase D.toG R) (N : Lv p)
  (X : GenModel gb N.1) (k : ℕ), Smooth ((GlobalTheory.KS.pow X.univ.A k).hom ≫ X.s) ∧ IsSeparated ((GlobalTheory.KS.pow X.univ.A k).hom ≫ X.s) ∧
    (D.CompactB → IsProjOver ((GlobalTheory.KS.pow X.univ.A k).hom ≫ X.s))

def EtDesc : Prop := ∀ {W Z Y B : Scheme.{0}} [IsReduced W] (c : W ⟶ Z) [IsFinite c] [Etale c] [Surjective c] (pZ : Z ⟶ B)
  (pY : Y ⟶ B) [IsSeparated pY] (f : W ⟶ Y), f ≫ pY = c ≫ pZ →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x y : sp Ω ⟶ W), x ≫ c = y ≫ c → x ≫ f = y ≫ f) → Epi c ∧ ∃ g : Z ⟶ Y, c ≫ g = f

def PtEq : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (N₁ N₂ N : Lv p) (X₁ : GenModel gb N₁.1) (X₂ : GenModel gb N₂.1) (X : GenModel gb N.1) (h₁ h₂ g u : G.GAf)
  (π₁ : X₁.X ⟶ X.X) (Φ₁ : X₁.univ.A.left ⟶ X.univ.A.left) (π₂ : X₂.X ⟶ X.X) (Φ₂ : X₂.univ.A.left ⟶ X.univ.A.left),
  Wit L h₁ X₁ X π₁ Φ₁ → Wit L h₂ X₂ X π₂ Φ₂ → Integ L h₁ → Integ L h₂ → AdmK L N₁.1 N.1 h₁ → AdmK L N₂.1 N.1 h₂ →
  u ∈ L.KN N.1 → h₁ = u * (h₂ * g) → ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ Sp R) (x : Sp k ⟶ X₁.X) (y : Sp k ⟶ X₂.X),
  x ≫ X₁.s = s → y ≫ X₂.s = s → ∀ (ox : GObj gb N₁.1 s) (oy : GObj gb N₂.1 s) (mx : GObjMap ox X₁.univ x) (my : GObjMap oy X₂.univ y)
  (θ : ox.A ⟶ oy.A), IsTrans L g ox oy θ → x ≫ π₁ = y ≫ π₂ ∧ mx.φ ≫ Φ₁ = θ.left ≫ my.φ ≫ Φ₂

def PtOrbit : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (N' N : Lv p) (X' : GenModel gb N'.1) (X : GenModel gb N.1) (π : X'.X ⟶ X.X)
  (Φ : X'.univ.A.left ⟶ X.univ.A.left), Wit L 1 X' X π Φ → ∀ (k : Type) [Field k] [IsAlgClosed k] (x y : Sp k ⟶ X'.X),
  x ≫ π = y ≫ π → ∃ (ox oy : GObj gb N'.1 (x ≫ X'.s)) (mx : GObjMap ox X'.univ x) (my : GObjMap oy X'.univ y),
    y ≫ X'.s = x ≫ X'.s ∧ ∃ u ∈ L.KN N.1, ∃ θ : ox.A ⟶ oy.A, IsTrans L u ox oy θ ∧ θ.left ≫ my.φ ≫ Φ = mx.φ ≫ Φ

def WitUniq : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [Field R] [Algebra ℚ R]
  (gb : GBase D.toG R) (N' N : Lv p) (X' : GenModel gb N'.1) (X : GenModel gb N.1) (h : G.GAf), Integ L h → AdmK L N'.1 N.1 h →
  ∀ π Φ π' Φ', Wit L h X' X π Φ → Wit L h X' X π' Φ' → π = π' ∧ Φ = Φ'

def WitComp : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (N₁ N₂ N₃ : Lv p) (X₁ : GenModel gb N₁.1) (X₂ : GenModel gb N₂.1) (X₃ : GenModel gb N₃.1) (h h' : G.GAf),
  (∀ u ∈ L.KN N₁.1, Wit L u X₁ X₁ (𝟙 _) (𝟙 _)) ∧ (Integ L h' → AdmK L N₂.1 N₃.1 h' →
  ∀ π Φ π' Φ', Wit L h X₁ X₂ π Φ → Wit L h' X₂ X₃ π' Φ' → Wit L (h' * h) X₁ X₃ (π ≫ π') (Φ ≫ Φ'))

def WitCart : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (N' N : ℕ) (X' : GenModel gb N') (X : GenModel gb N), ∀ u ∈ L.KN 1, ∀ π Φ, Wit L u X' X π Φ →
  IsPullback Φ X'.univ.A.hom X.univ.A.hom π

def WitForget : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [Field R] [Algebra ℚ R]
  (gb : GBase D.toG R) (N M : Lv p), N.1 ∣ M.1 → ∀ (X : GenModel gb N.1) (X' : GenModel gb M.1),
  ∃ π Φ, Wit L 1 X' X π Φ ∧ IsFinite π ∧ Etale π ∧ Surjective π

def WitDeep : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [Field R] [Algebra ℚ R]
  (gb : GBase D.toG R) (X : ∀ N : Lv p, GenModel gb N.1) (N' N : Lv p) (h : G.GAf), Integ L h →
  ∃ M : Lv p, N'.1 ∣ M.1 ∧ AdmK L M.1 N.1 h ∧ ∃ π Φ, Wit L h (X M) (X N) π Φ

def DescMap : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [Field R] [Algebra ℚ R]
  (gb : GBase D.toG R) (M N' N : Lv p) (XM : GenModel gb M.1) (X' : GenModel gb N'.1) (X : GenModel gb N.1) (h : G.GAf),
  Integ L h → AdmK L N'.1 N.1 h → AdmK L M.1 N'.1 1 → ∀ c Φc π₁ Φ₁, Wit L 1 XM X' c Φc → IsFinite c → Etale c → Surjective c →
  Wit L h XM X π₁ Φ₁ → ∃ (π : X'.X ⟶ X.X) (Φ : X'.univ.A.left ⟶ X.univ.A.left), c ≫ π = π₁ ∧ Φc ≫ Φ = Φ₁ ∧
    π ≫ X.s = X'.s ∧ Φ ≫ X.univ.A.hom = X'.univ.A.hom ≫ π

def HomDesc : Prop := ∀ (S S' : Scheme.{0}) [IsReduced S'] (c : S' ⟶ S) [IsFinite c] [Etale c] [Surjective c] (A B : Over S)
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (A' B' : Over S') [GrpObj A'] [IsCommMonObj A'] [GrpObj B']
  [IsCommMonObj B'], IsAbelianScheme A → IsAbelianScheme B → IsAbelianScheme B' → ∀ (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left),
  IsGrpPullback A' A c a → IsGrpPullback B' B c b → ∀ (ψ : A ⟶ B) (ψ' : A' ⟶ B'), ψ'.left ≫ b = a ≫ ψ.left → IsMonHom ψ' →
  IsMonHom ψ ∧ ∀ (χ' : B' ⟶ A') (d : ℕ), IsMonHom χ' → Surjective ψ'.left → IsFinite ψ'.left → ψ' ≫ χ' = (𝟙 A') ^ d →
    χ' ≫ ψ' = (𝟙 B') ^ d → ∃ χ : B ⟶ A, χ'.left ≫ a = b ≫ χ.left ∧ ψ ≫ χ = (𝟙 A) ^ d ∧ χ ≫ ψ = (𝟙 B) ^ d

def PolDesc : Prop := ∀ (G₀ : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase G₀ R) (S S' : Scheme.{0}) (s : S ⟶ Sp R)
  (s' : S' ⟶ Sp R) (c : S' ⟶ S) [IsFinite c] [Etale c] [Surjective c] (N₁ N₂ : ℕ) (o₁ : GObj gb N₁ s) (o₂ : GObj gb N₂ s)
  (o₁' : GObj gb N₁ s') (o₂' : GObj gb N₂ s') (m₁ : GObjMap o₁' o₁ c) (m₂ : GObjMap o₂' o₂ c) (ψ : o₁.A ⟶ o₂.A)
  (ψ' : o₁'.A ⟶ o₂'.A), IsMonHom ψ → ψ'.left ≫ m₂.φ = m₁.φ ≫ ψ.left → ∀ e : ℕ,
  Nonempty (LBIso (Hecke.lbPow o₁'.P e) (o₂'.P.pull (Hecke.sq2 ψ'))) → Nonempty (LBIso (Hecke.lbPow o₁.P e) (o₂.P.pull (Hecke.sq2 ψ)))

def TransDesc : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S S' : Scheme.{0}) [IsReduced S'] (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (c : S' ⟶ S) [IsFinite c] [Etale c]
  [Surjective c], c ≫ s = s' → ∀ (N₁ N₂ : ℕ) (o₁ : GObj gb N₁ s) (o₂ : GObj gb N₂ s) (o₁' : GObj gb N₁ s') (o₂' : GObj gb N₂ s')
  (m₁ : GObjMap o₁' o₁ c) (m₂ : GObjMap o₂' o₂ c) (ψ : o₁.A ⟶ o₂.A) (ψ' : o₁'.A ⟶ o₂'.A) (h : G.GAf),
  ψ'.left ≫ m₂.φ = m₁.φ ≫ ψ.left → IsTrans L h o₁' o₂' ψ' → IsTrans L h o₁ o₂ ψ

def TransCancel : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
  (gb : GBase D.toG R) (S : Scheme.{0}) (s : S ⟶ Sp R) (M N' N : Lv p) (o : GObj gb M.1 s) (o₁ : GObj gb N'.1 s)
  (o₂ : GObj gb N.1 s) (θ : o.A ⟶ o₁.A) (χ : o₁.A ⟶ o₂.A) (h : G.GAf), Integ L h → AdmK L M.1 N.1 h → IsTrans L 1 o o₁ θ →
  IsTrans L h o o₂ (θ ≫ χ) → IsTrans L h o₁ o₂ χ

def WitEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [Field R] [Algebra ℚ R]
  (gb : GBase D.toG R) (X : ∀ N : Lv p, GenModel gb N.1) (N' N : Lv p) (h : G.GAf), Integ L h → AdmK L N'.1 N.1 h →
  ∃ π Φ, Wit L h (X N') (X N) π Φ

def WitOne : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [Field R] [Algebra ℚ R]
  (gb : GBase D.toG R) (X : ∀ N : Lv p, GenModel gb N.1) (N' N : Lv p), AdmK L N'.1 N.1 1 →
  ∀ π Φ, Wit L 1 (X N') (X N) π Φ → IsFinite π ∧ Etale π ∧ Surjective π

def WitTrans : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [Field R] [Algebra ℚ R]
  (gb : GBase D.toG R) (X : ∀ N : Lv p, GenModel gb N.1) (N' N : Lv p), ∀ π Φ, Wit L 1 (X N') (X N) π Φ →
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x y : Sp k ⟶ (X N').X), x ≫ π = y ≫ π →
  ∃ u ∈ L.KN N.1, ∀ π' Φ', Wit L u (X N') (X N') π' Φ' → x ≫ π' = y ∧
    ∀ a : Sp k ⟶ (X N').univ.A.left, a ≫ (X N').univ.A.hom = x → a ≫ Φ' ≫ Φ = a ≫ Φ

def WitFree : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [Field R] [Algebra ℚ R]
  (gb : GBase D.toG R) (X : ∀ N : Lv p, GenModel gb N.1) (N' N : Lv p), L.KN N'.1 ≤ L.KN N.1 → ∀ u ∈ L.KN N.1, ∀ π Φ,
  Wit L u (X N') (X N') π Φ → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ (X N').X), x ≫ π = x → u ∈ L.KN N'.1

def TwFEt : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) (i j : X.ι) (a : X.admitted i j 1),
  FEt (X.tr i j 1 a.1 a.2) ((X.K i).relIndex (X.K j))

def SigmaFEt : Prop := ∀ {Y Z : Scheme.{0}} (s : Y ⟶ Z) (d : ℕ) (I : Type) [Finite I], FEt s d →
  FEt (Sigma.desc fun _ : I => s) (Nat.card I * d)

def TwMem : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {F : Type} [Field F] (T : Th.{u} B F)
  (m i j : X.ι) (a : X.admitted i j 1), X.K m ≤ X.K i → (∀ k ∈ X.K j, ∀ u ∈ X.K m, k * u * k⁻¹ ∈ X.K m) →
  ∀ (I A : Type) [Fintype I] [Fintype A] (e : I → G) (he : ∀ c, X.admitted i j (e c)) (r : A → G), (∀ x, r x ∈ X.K j) →
  (∀ k ∈ X.K j, ∃! x, k * (r x)⁻¹ ∈ X.K i) →
  ∀ (ht : (Sigma.desc fun c : I => X.tr i j (e c) (he c).1 (he c).2) ≫ X.q j = (Sigma.desc fun _ : I => X.tr i j 1 a.1 a.2) ≫ X.q j) tr,
  T.IsTr (X.q j) _ (Sigma.desc fun _ : I => X.tr i j 1 a.1 a.2) tr →
  ∀ x, X.pl T m j 1 (tr (T.pull _ ht x)) = ∑ c, ∑ y, X.pl T m j (e c * r y) x

def SumFn : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {F : Type} [Field F] (T : Th.{u} B F)
  (m j : X.ι) (A : Type) [Fintype A] (e : A → G), (∀ a, X.admitted m j (e a)) → ∀ f : G → F,
  (∀ y, f y = (Nat.card {a : A // e a * y ∈ X.K j} : ℕ)) → (∀ g, f g ≠ 0 → X.admitted m j g⁻¹) ∧
    ((∀ k ∈ X.K j, ∀ g, f (k * g) = f g) → X.IsFn j f) ∧
    ∀ x, ∑ a, X.pl T m j (e a) x = ∑ᶠ y : G ⧸ X.K j, f y.out • X.pl T m j y.out⁻¹ x

def MemOp : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [Field R] [Algebra ℚ R]
  (gb : GBase D.toG R) (k : ℕ) (T : KS L gb k) (N : Lv p) (J : Type) (g : J → Mem L N) (j : J) (F : Type) [Field F] [CharZero F]
  (Θ : Th.{u} (Sp R) F), Θ.Good → ∀ f : G.GAf → F,
  (∀ y, f y = (Nat.card {k : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K // (g j).h * (k.out : G.GAf) * y ∈ L.KN N.1} : ℕ)) →
  T.X.IsFn (T.lev N) f ∧ ∀ tr, Θ.IsTr (T.tower N g).q ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j) tr →
    tr ∘ₗ Θ.pull ((T.tower N g).t j) ((T.tower N g).comm j) = T.X.hecke Θ (T.lev N) f

end UpperTheory.Gal.G3

end
