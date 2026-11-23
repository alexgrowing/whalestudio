import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGen

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.GalV (HTower Splits)
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD TjE KSOKE)
open scoped TensorProduct
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.Int.Geo

structure CoverOn {k A : Type} [Field k] [Field A] (H : HTower k) (θ : H.Γ → A) {O : Type} [CommRing O] [Algebra O k] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of O)) (π : H.Z ⟶ Y) : Type 1 where
  smooth : Smooth p
  proj : IsProjOver p
  ov : π ≫ p = H.q ≫ gen O k
  Δ : Type
  [grp : Group Δ]
  [fin : Finite Δ]
  a : Δ → (H.Z ⟶ H.Z)
  finπ : IsFinite (pullback.lift π H.q ov)
  etπ : Etale (pullback.lift π H.q ov)
  one : a 1 = 𝟙 _
  mul : ∀ g h, a (g * h) = a g ≫ a h
  spl : Splits (pullback.lift π H.q ov) (pullback.lift π H.q ov) a
  fix : ∀ δ, ∃ g, IsIso (H.s g) ∧ H.t g = H.s g ≫ a δ ∧ θ g = 1
  dim : ∃ d, SmoothOfRelativeDimension d p

def CoverOn.toCover {k A : Type} [Field k] [Field A] {H : HTower k} {θ : H.Γ → A} {O : Type} [CommRing O] [Algebra O k] {Y : Scheme.{0}}
    {p : Y ⟶ Spec (CommRingCat.of O)} {π : H.Z ⟶ Y} (C : CoverOn H θ p π) : Cover H θ O :=
  { C with Y := Y, p := p, π := π }

structure MIn : Prop where
  ex : GlobalTheory.EtaleLevelHecke.ModelExists
  proj : GlobalTheory.EtaleLevelHecke.ModelProj
  cmp : GlobalTheory.EtaleLevelHecke.GenCmp
  finModel : FiniteEtaleModels.FinModel
  placeOf : FiniteEtaleModels.PlaceOf
  cong : crystallineComparison.Mod.CongKS
  corr : crystallineComparison.Mod.CorrBC

def SplitQ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → ∀ (q : ℕ) [Fact q.Prime],
    Nonempty ((D.O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[q]))

def BaseEx : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.a = 1 → D.m = 1 → ∀ (E : Type) [Field E] [NumberField E] (e : D.F ≃+* E) (gb : GBase D.toG E), IsStd e gb →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (𝔴 : Ideal (𝓞 D.F)) (r : ℤ), IsPl e w 𝔴 → ES.uIdeal D r ≤ 𝔴 → ∀ N₀ : ℕ, 3 ≤ N₀ → N₀.Coprime q →
    ∃ (f : ℕ) (b : Base D (Ow w)), Match b gb (algebraMap (Ow w) E) ∧ Std f b N₀ r 𝔴 ∧ (q : 𝓞 E) ∈ w.asIdeal ∧ Ideal.absNorm w.asIdeal = q ^ f

def PowProj : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime q →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (o : Obj b N s) (k : ℕ), (IsProjOver s → IsProjOver ((GlobalTheory.KS.pow o.A k).hom ≫ s)) ∧
    ∀ d, SmoothOfRelativeDimension d s → ∃ d', SmoothOfRelativeDimension d' ((GlobalTheory.KS.pow o.A k).hom ≫ s)

def SiteEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (e : D.F ≃+* E)
    (gb : GBase D.toG E), IsStd e gb → ∀ (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)), IsPl e w 𝔴 →
    AtPrime D q r 𝔴 → LevOK D q r 𝔴 𝔫 → Nonempty (Site gb w q r 𝔴 𝔫)

def GenEx : Prop :=
  ∀ (A : Type) [CommRing A] [IsDedekindDomain A] [CharZero A] (𝔞 : Ideal A) (N : ℕ), 0 < N →
    ((N : A) ∈ 𝔞 → ∃ a, IsGen a N 𝔞) ∧ ∀ (a : A) (t : ℕ), IsGen a N 𝔞 → IsGen (t * a) (N * t) 𝔞

def NumEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (N : ℕ), 0 < N →
    ((N : 𝓞 D.F) ∈ 𝔫 → ∃ c a, S.Num N c a) ∧ ∀ c a (t : ℕ), S.Num N c a → S.Num (N * t) (c * t) (t * a)

def LatGen : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (a : 𝓞 D.F) (N : ℕ) (𝔞 : Ideal (𝓞 D.F)), 0 < N → IsGen a N 𝔞 →
    (∀ y : D.La, (∃ z, algebraMap (𝓞 D.F) D.O a • y = N • z) ↔ y ∈ wSub D 𝔞 1) ∧
    ∀ x : D.La, (∀ c ∈ 𝔞, ∃ z, algebraMap (𝓞 D.F) D.O c • x = N • z) → ∃ y z, x = algebraMap (𝓞 D.F) D.O a • y + N • z

def GPull : Prop :=
  ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase G R) (N : ℕ) (X X' : Scheme.{0}) (s : X ⟶ Sp R) (e : X' ⟶ X)
    (o : GObj gb N s), ∃ o' : GObj gb N (e ≫ s), Nonempty (GObjMap o' o e)

def PowCart : Prop :=
  ∀ (X Y Z : Scheme.{0}) (A : Over X) (B : Over Y) (C : Over Z) (f : X ⟶ Y) (g : Y ⟶ Z) (φ : A.left ⟶ B.left) (χ : B.left ⟶ C.left)
    (u : φ ≫ B.hom = A.hom ≫ f) (v : χ ≫ C.hom = B.hom ≫ g) (k : ℕ),
    (IsPullback φ A.hom B.hom f → IsPullback (GlobalTheory.KS.powMap f φ u k) (GlobalTheory.KS.pow A k).hom (GlobalTheory.KS.pow B k).hom f) ∧
    GlobalTheory.KS.powMap f φ u k ≫ (GlobalTheory.KS.pow B k).hom = (GlobalTheory.KS.pow A k).hom ≫ f ∧
    ∀ w, GlobalTheory.KS.powMap f φ u k ≫ GlobalTheory.KS.powMap g χ v k = GlobalTheory.KS.powMap (f ≫ g) (φ ≫ χ) w k

def QObj : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R) (gb : GBase D.toG R') (β : R →+* R'), Match b gb β → ∀ (N N₀ c : ℕ), N = N₀ * c → 0 < N → N₀.Coprime q →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R') (o : GObj gb N s), ∃ o₀ : Obj b N₀ (s ≫ spMap β), Nonempty (QMap o o₀ (𝟙 X) c)

def QComp : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R) (gb : GBase D.toG R') (N N₀ c : ℕ) (X X₁ X₂ : Scheme.{0}) (s : X ⟶ Sp R') (s₁ : X₁ ⟶ Sp R) (s₂ : X₂ ⟶ Sp R)
    (o : GObj gb N s) (u₁ : Obj b N₀ s₁) (u₂ : Obj b N₀ s₂) (f : X ⟶ X₁) (g : X₁ ⟶ X₂),
    (∀ (n : QMap o u₁ f c) (m : ObjMap u₁ u₂ g), ∃ n' : QMap o u₂ (f ≫ g) c, n'.φ = n.φ ≫ m.φ) ∧
    (∀ (n' : QMap o u₂ (f ≫ g) c) (m : ObjMap u₁ u₂ g), ∃ n : QMap o u₁ f c, n'.φ = n.φ ≫ m.φ) ∧
    (IsIso f → ∀ (n : QMap o u₁ f c) (n' : QMap o u₂ (f ≫ g) c), ∃ m : ObjMap u₁ u₂ g, n'.φ = n.φ ≫ m.φ) ∧
    ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (o' : GObj gb N s') (e : X' ⟶ X) (m : GObjMap o' o e) (n : QMap o u₁ f c),
      ∃ n' : QMap o' u₁ (e ≫ f) c, n'.φ = m.φ ≫ n.φ

def QUniq : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R) (gb : GBase D.toG R') (N N₀ c : ℕ), 3 ≤ N₀ → N₀.Coprime q → ∀ (X X₁ : Scheme.{0}) (s : X ⟶ Sp R') (s₁ : X₁ ⟶ Sp R)
    (o : GObj gb N s) (u : Obj b N₀ s₁) (f : X ⟶ X₁) (n n' : QMap o u f c), n.φ = n'.φ

def QIso : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R) (gb : GBase D.toG R') (N N' N₀ c c' : ℕ) (X X₁ : Scheme.{0}) (s : X ⟶ Sp R') (s₁ : X₁ ⟶ Sp R)
    (o' : GObj gb N' s) (o : GObj gb N s) (u : Obj b N₀ s₁) (f : X ⟶ X₁) (ψ : o'.A ⟶ o.A), IsIso ψ → IsMonHom ψ →
    (∀ x : D.O, o'.act.act x ≫ ψ = ψ ≫ o.act.act x) → Nonempty (LBIso (Hecke.lbPow o'.P 1) (o.P.pull (Hecke.sq2 ψ))) →
    (∀ y : D.La, o'.eta (c' • y) ≫ ψ = o.eta (c • y)) → ∀ n : QMap o u f c, ∃ n' : QMap o' u f c', n'.φ = ψ.left ≫ n.φ

def QLev : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R) (gb : GBase D.toG R') (N N₀ c : ℕ) (a : 𝓞 D.F) (𝔞 : Ideal (𝓞 D.F)), 0 < N → IsGen a N 𝔞 → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R') (s₀ : X ⟶ Sp R)
    (o : GObj gb N s) (o₀ : Obj b N₀ s₀) (n : QMap o o₀ (𝟙 X) c), ∃ l, IsEtLev o₀ 𝔞 1 l ∧
      ∀ y : D.La, (o.eta (algebraMap (𝓞 D.F) D.O a • y)).left ≫ n.φ = (l y).left

def ClsEx : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R) (gb : GBase D.toG R') (β : R →+* R'), Match b gb β → ∀ (N N₀ c : ℕ) (a : 𝓞 D.F) (𝔞 : Ideal (𝓞 D.F)), N = N₀ * c → 0 < N → 3 ≤ N₀ →
    N₀.Coprime q → IsGen a N 𝔞 → ∀ (Y : EtModel b N₀ 𝔞 1) (X : Scheme.{0}) (s : X ⟶ Sp R') (o : GObj gb N s),
    Nonempty (Cls Y β o c a) ∧ ∀ C C' : Cls Y β o c a, C.j = C'.j ∧ C.m.φ = C'.m.φ

def TrEta : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
    (h : G.GAf) (X : Scheme.{0}) (s : X ⟶ Sp R) (N' N : Lv p) (o' : GObj gb N'.1 s) (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L h o' o ψ → ∀ (n c' c : ℕ), N'.1 = n * c' → N.1 = n * c → ∀ x y : D.La,
    (∃ v ∈ LaHat D, L.actG h (inAf D x) = inAf D y + n • v) → o'.eta (c' • x) ≫ ψ = o.eta (c • y)

def TrEtaPt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
    (h : G.GAf) (X : Scheme.{0}) (s : X ⟶ Sp R) (N' N : Lv p) (o' : GObj gb N'.1 s) (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L h o' o ψ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : Sp Ω ⟶ X) (x : D.La),
    (toUnit (Over.mk z) ≫ o'.eta x ≫ ψ = 1 ↔ ∃ v ∈ LaHat D, L.actG h (inAf D x) = N'.1 • v) ∧
    (N' = N → ∀ y : D.La, toUnit (Over.mk z) ≫ o'.eta x ≫ ψ = toUnit (Over.mk z) ≫ o.eta y → ∃ v ∈ LaHat D, L.actG h (inAf D x) = inAf D y + N.1 • v)

def MultUnit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), (∀ u ∈ L.KN 1, ∃ t' : AfP p, IsIntAf (((u : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) ∧ IsIntAf t' ∧
      (((u : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) * t' = 1) ∧
    ∀ (c c' : ℕ) (t t' : AfP p), c.Coprime p → c'.Coprime p → IsIntAf t → IsIntAf t' → t * t' = 1 → (c : AfP p) = c' * t → c = c'

def TrBack : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
    (h : G.GAf) (X : Scheme.{0}) (s : X ⟶ Sp R) (N' N : Lv p) (o' : GObj gb N'.1 s) (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L h o' o ψ → ∀ c : ℕ, c.Coprime p → (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = c • v) →
    ∃ ψ' : o.A ⟶ o'.A, IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 o'.A) ^ c ∧ ψ' ≫ ψ = (𝟙 o.A) ^ c

def TrUnit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
    (h : G.GAf) (X : Scheme.{0}) (s : X ⟶ Sp R) (N' N : Lv p) (o' : GObj gb N'.1 s) (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L h o' o ψ → h ∈ L.KN 1 → IsIso ψ ∧ Nonempty (LBIso (Hecke.lbPow o'.P 1) (o.P.pull (Hecke.sq2 ψ)))

def TrTj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
    (h : G.GAf) (X : Scheme.{0}) (s : X ⟶ Sp R) (N' N : Lv p) (o' : GObj gb N'.1 s) (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L h o' o ψ → ∀ (q : ℕ) (r : ℤ) (𝔴 : Ideal (𝓞 D.F)) (i : ℕ) (h₀ u : G.GAf), AtPrime D q r 𝔴 → IsTjElt L q r 𝔴 i h₀ → Integ L h₀ →
    u ∈ L.KN 1 → h = h₀ * u → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : Sp Ω ⟶ X),
    (∀ g : Over.mk z ⟶ o'.A, g ≫ ψ = 1 → (∃ e : ℕ, ∀ x ∈ uId D q r ^ e, g ≫ o'.act.act (algebraMap (𝓞 D.F) D.O x) = 1) →
      ∀ x ∈ 𝔴, g ≫ o'.act.act (algebraMap (𝓞 D.F) D.O x) = 1) ∧
    Nat.card {g : Over.mk z ⟶ o'.A // g ≫ ψ = 1 ∧ ∀ x ∈ 𝔴, g ≫ o'.act.act (algebraMap (𝓞 D.F) D.O x) = 1} = Ideal.absNorm 𝔴 ^ i

def CongCRT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (q : ℕ) (r : ℤ) (N₀ : ℕ) (𝔞 : Ideal (𝓞 D.F)), N₀.Coprime q → (∃ e : ℕ, uId D q r ^ e ≤ 𝔞) → ∀ g : G.GAf, Integ L g →
    (CongId L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) g ↔ L.CongOne N₀ g ∧ CongId L 𝔞 g) ∧
    ∀ (a : 𝓞 D.F) (N : ℕ), 0 < N → N.Coprime p → IsGen a N 𝔞 → (CongId L 𝔞 g ↔ ∀ y : D.La, ∃ v ∈ LaHat D,
      L.actG g (inAf D (algebraMap (𝓞 D.F) D.O a • y)) = inAf D (algebraMap (𝓞 D.F) D.O a • y) + N • v)

def GrpLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (M : ℕ), 0 < M → M.Coprime p → ∀ h₁ h₂ : G.GAf, Integ L h₁ → Integ L h₂ →
    (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₁ v' = M • v) → (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₂ v' = M • v) →
    (∀ x : D.La, (∃ v ∈ LaHat D, L.actG h₁ (inAf D x) = M • v) ↔ ∃ v ∈ LaHat D, L.actG h₂ (inAf D x) = M • v) → h₁ * h₂⁻¹ ∈ L.KN 1

def GrpCong : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (𝔫 : Ideal (𝓞 D.F)) (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ h u : G.GAf, Integ L h → CongId L 𝔫 h → u ∈ K₀ →
    h * u * h⁻¹ ∈ L.KN 1 → h * u * h⁻¹ ∈ K₀

def BaseInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k) (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ (N' N : Lv p) (t c : ℕ) (a : 𝓞 D.F), N'.1 = N.1 * t → S.Num N.1 c a →
    ∀ (C' : S.Cl (T.M N').univ (c * t) (t * a)) (C : S.Cl (T.M N).univ c a), ∀ u ∈ K₀, ∀ W : Wit T u N' N,
    W.π ≫ C.j = C'.j ∧ W.ψ.left ≫ W.φ.φ ≫ C.m.φ = C'.m.φ

def PiInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k) (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ (N' N : Lv p) (t c : ℕ) (a : 𝓞 D.F), N'.1 = N.1 * t → S.Num N.1 c a →
    ∀ (C' : S.Cl (T.M N').univ (c * t) (t * a)) (C : S.Cl (T.M N).univ c a), ∀ u ∈ K₀, ∀ x y, T.X.tr (T.lev N') (T.lev N) u x y ≫ S.pi T C = S.pi T C'

def BaseSep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k) (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ (N : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num N.1 c a → ∀ (C : S.Cl (T.M N).univ c a), ∀ u ∈ L.KN S.N₀, ∀ (W : Wit T u N N) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : Sp Ω ⟶ (T.M N).X),
    z ≫ W.π ≫ C.j = z ≫ C.j → u ∈ K₀

def PiZero : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k), ∀ (N : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num N.1 c a → ∀ (C : S.Cl (T.M N).univ c a),
    ∃ (ρ : T.X.Z (T.lev ⟨S.N₀, S.std.three, S.cop⟩) ⟶ (GlobalTheory.KS.pow S.M.univ.A k).left)
      (e : ρ ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s = T.X.q _ ≫ gen (Ow w) E), IsOpenImmersion (pullback.lift ρ _ e) ∧
      IsClosedImmersion (pullback.lift ρ _ e) ∧
      ∀ x y, T.X.tr (T.lev N) _ 1 x y ≫ ρ = S.pi T C ≫ GlobalTheory.KS.powMap S.π S.mπ.φ S.mπ.cart.1.w k

def PiFet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k), ∀ (N : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num N.1 c a → ∀ (C : S.Cl (T.M N).univ c a),
    ∃ e : S.pi T C ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s = T.X.q _ ≫ gen (Ow w) E,
      IsFinite (pullback.lift _ _ e) ∧ Etale (pullback.lift _ _ e)

def PiSep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k) (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ (N : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num N.1 c a → ∀ (C : S.Cl (T.M N).univ c a), ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z z' : Sp Ω ⟶ T.X.Z (T.lev N)),
    z ≫ S.pi T C = z' ≫ S.pi T C → ∃ u ∈ K₀, ∃ x y, z' = z ≫ T.X.tr _ _ u x y

def SplitOf : Prop :=
  ∀ (W X : Scheme.{0}) (c : W ⟶ X) [IsFinite c] [Etale c] (Δ : Type) [Finite Δ] (a : Δ → (W ⟶ W)), (∀ δ, a δ ≫ c = c) →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z z' : Sp Ω ⟶ W), z ≫ c = z' ≫ c → ∃! δ, z' = z ≫ a δ) → Splits c c a

def KSCover : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k) (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ (N : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num N.1 c a → ∀ (C : S.Cl (T.M N).univ c a), L.KN N.1 ≤ K₀ → ∀ (J A : Type) [Field A] (g : J → Mem L N) (θ : J → A), Deck g θ K₀ →
    Nonempty (CoverOn (T.tower N g) θ ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) (S.pi T C))

def TjIsog : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k) (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ (i : ℕ) (h : G.GAf), IsTjElt L q r 𝔴 i h → Integ L h → ∀ u ∈ K₀, ∀ (N' N : Lv p) (c' c : ℕ),
    N'.1 = S.N₀ * c' → N.1 = S.N₀ * c → ∀ (W : Wit T (h * u) N' N) (s₀ : (T.M N').X ⟶ Sp (Ow w)) (o₁ o₂ : Obj S.b S.N₀ s₀)
    (n₁ : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N').univ o₁ (𝟙 _) c') (n₂ : QMap (D := datAt S.atq S.sp) (gb := gb) W.o o₂ (𝟙 _) c),
    ∃ ψ₀ : o₁.A ⟶ o₂.A, n₁.φ ≫ ψ₀.left = W.ψ.left ≫ n₂.φ ∧ ES.IsPIsog (q ^ (S.f * i)) o₁ o₂ ψ₀ ∧ ES.IsTj (D := datAt S.atq S.sp) r 𝔴 i o₁ o₂ ψ₀

def LiftEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k) (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ (i : ℕ) (h : G.GAf), i ≤ D.n → IsTjElt L q r 𝔴 i h → Integ L h → ∀ (Tj : TjD S.M r 𝔴 i (q ^ (S.f * i))) (Lj : TjE S.Y S.mπ Tj), ∀ (N' N : Lv p) (t c : ℕ) (a : 𝓞 D.F), N'.1 = N.1 * t → S.Num N.1 c a →
    ∀ (C' : S.Cl (T.M N').univ (c * t) (t * a)) (C : S.Cl (T.M N).univ c a), ∀ u ∈ K₀, ∀ W : Wit T (h * u) N' N, Nonempty (Lift S T Lj W C' C)

def LiftSep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k) (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ (i : ℕ) (h : G.GAf), i ≤ D.n → IsTjElt L q r 𝔴 i h → Integ L h → ∀ (Tj : TjD S.M r 𝔴 i (q ^ (S.f * i))) (Lj : TjE S.Y S.mπ Tj), ∀ (N' N : Lv p) (t c : ℕ) (a : 𝓞 D.F), N'.1 = N.1 * t → S.Num N.1 c a →
    ∀ (C' : S.Cl (T.M N').univ (c * t) (t * a)) (C : S.Cl (T.M N).univ c a), Ideal.absNorm 𝔴 ^ i ∣ N'.1 →
    ∀ u₁ ∈ K₀, ∀ u₂ ∈ K₀, ∀ v₁ ∈ K₀, ∀ v₂ ∈ K₀, ∀ (W₁ : Wit T (h * u₁) N' N) (W₂ : Wit T (h * u₂) N' N) (V₁ : Wit T v₁ N' N') (V₂ : Wit T v₂ N' N')
    (l₁ : Lift S T Lj W₁ C' C) (l₂ : Lift S T Lj W₂ C' C) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : Sp Ω ⟶ (T.M N').X),
    z ≫ V₁.π ≫ l₁.y = z ≫ V₂.π ≫ l₂.y → h * (u₁ * v₁ * (u₂ * v₂)⁻¹) * h⁻¹ ∈ K₀

def Count : Prop :=
  ∀ (Γ : Type) [Group Γ] (K₀ H K : Subgroup Γ), K ≤ H → H ≤ K₀ → K.relIndex K₀ ≠ 0 → ∀ (F : Type) (κ : K₀ ⧸ K.subgroupOf K₀ → F),
    Nat.card F = H.relIndex K₀ → (∀ x y : K₀, κ (x : K₀ ⧸ K.subgroupOf K₀) = κ y → (x : Γ)⁻¹ * y ∈ H) →
    ∀ ζ : F, Nat.card {x // κ x = ζ} = K.relIndex H

def TjLies : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k) (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ (N : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num N.1 c a → ∀ (C : S.Cl (T.M N).univ c a), L.KN N.1 ≤ K₀ → ∀ [𝔴.IsMaximal] (J : Type) (g : J → Mem L N) (j : J) (i : ℕ), i ≤ D.n → (g j).K = K₀ →
    IsTjElt L q r 𝔴 i (g j).h → Ideal.absNorm 𝔴 ^ i ∣ (g j).M.1 →
    (K₀ ⊓ K₀.comap (MulAut.conj (g j).h).toMonoidHom).relIndex K₀ = Nat.card (crystallineComparison.Gr (𝓞 D.F ⧸ 𝔴) (Fin D.n → 𝓞 D.F ⧸ 𝔴) i) →
    ∀ (Tj : TjD S.M r 𝔴 i (q ^ (S.f * i))) (Lj : TjE S.Y S.mπ Tj),
    0 < (L.KN (g j).M.1).relIndex (K₀ ⊓ K₀.comap (MulAut.conj (g j).h).toMonoidHom) ∧
    ∃ (κ : (T.tower N g).Y j ⟶ (GlobalTheory.KS.pow Lj.o.A k).left) (e : (T.tower N g).s j ≫ S.pi T C = κ ≫ Lj.ksP k),
      κ ≫ Lj.ksR k = (T.tower N g).t j ≫ S.pi T C ∧
      FEt (pullback.lift _ κ e) ((L.KN (g j).M.1).relIndex (K₀ ⊓ K₀.comap (MulAut.conj (g j).h).toMonoidHom))

def KSSm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (R : Type) [Field R] [Algebra ℚ R]
    (gb : GBase D.toG R) (k : ℕ) (T : KS L gb k) (N : Lv p), Smooth (T.X.q (T.lev N)) ∧ IsProjOver (T.X.q (T.lev N))

end UpperTheory.Gal.Int.Geo

end
