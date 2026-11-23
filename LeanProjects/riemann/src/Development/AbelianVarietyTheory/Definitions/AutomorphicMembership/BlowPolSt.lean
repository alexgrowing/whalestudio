import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef

section Fun

variable {O : Type} [CommRing O]

def comb (a : ℕ) (ψ : InvFun O) (b : ℕ) (φ : InvFun O) : InvFun O where
  toFun n B := a * ψ.toFun n B + b * φ.toFun n B
  inv n m r hr B := by rw [ψ.inv n m r hr, φ.inv n m r hr]
  zero B := by rw [ψ.zero, φ.zero]; simp

def resInt (O : Type) [CommRing O] [Module.Finite ℤ O] (φ : InvFun ℤ) : InvFun O where
  toFun n B := φ.eval (Fin n → O) B
  inv n m r hr B := φ.eval_comp (r := r.restrictScalars ℤ) hr B
  zero B := by
    rw [φ.eval_eq (n := 0) (r := 0) fun a => ⟨0, Subsingleton.elim _ _⟩]
    exact φ.zero _

def IsTame (φ : InvFun O) : Prop :=
  (∀ (n k : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) ∧
    ∀ n B, 0 ≤ φ.toFun n B

end Fun

section Cones

variable {R : Type} [CommRing R] [IsDomain R]

def FormAt (Dg : DegPre R) {W : Type} [CommRing W] (f : R →+* W) (ϖ : W) (be : LinearMap.BilinForm ℤ Dg.X) : Prop :=
  ∀ y, ∃ (r : R) (n : ℕ), PsiCoord Dg y r ∧ be y y = 2 * n ∧ Associated (f r) (ϖ ^ n)

def InCone (Dg : DegPre R) {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ Dg.X) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W)
    (be : LinearMap.BilinForm ℤ Dg.X), (∀ y z, be y z = be z y) → FormAt Dg f ϖ be →
    ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ toReal be = ∑ i, c i • toReal (γ i)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HasCones (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (Z : Model Xo c β) : Prop :=
  ∀ z : Z.X, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R))
    (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
    IsCN R ∧ ξ (closedPoint R) = z ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified ∧ P.TorsionIso ∧
    Cn P.D.toPre.X m γ ∧ InCone P.D.toPre γ

def ConeZ (E : Type) [Field E] [NumberField E] (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  IsCone id φ γ

def ConeO (H : Host E) (φ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop := IsCone H.bar φ γ

def PolRay (ψ φ : InvFun (𝓞 E)) (k : ℕ) (Z : Model Xo c β) : Prop :=
  ∃ b N T₀ : ℕ, 0 < b ∧ 0 < N ∧ ∀ T, T₀ ≤ T → ∃ BD, IsPol (comb (N * T) ψ b φ) (N * T * k) Z BD

def GenTor (Z : Model Xo c β) : Prop :=
  SmoothOfRelativeDimension D.dim (genStr Z) ∧ FinalTheorems.Snc (genBdIdeal Z) ∧ ∀ x ∈ genBd Z, HasToricChart Z x

def Refines (H : Host E) (q : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) : Prop :=
  IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ ∧ IsTwInv H φ ∧ IsPosFn H φ ∧ IsTame φ ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ →
        (resInt (𝓞 E) φs).LinearOn γ ∧ ∀ N ∈ 𝒩, IsFine N γ

end Cones

abbrev GMod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} (Xo : Moduli D l)
    (c : Coeff l) : Type 1 := Model Xo c (algebraMap (𝓞 c.F) c.F)

def SiegLocSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l, ∃ (g : ℕ) (φs : InvFun ℤ), Module.finrank ℚ E * min D.p D.q ≤ g ∧ IsPolFan id g φs ∧
      IsTame φs ∧ ∀ (l : Level H) (c : Coeff l), (∀ p : ℕ, p.Prime → l.GoodAt p) →
        ∃ (I : Type) (_ : Finite I) (R : I → Type) (_ : ∀ i, CommRing (R i)) (a : I → 𝓞 c.F) (b : ∀ i, 𝓞 c.F →+* R i)
          (ω : ∀ i, R i →+* c.F) (C : ∀ i, Model (Xo l) c (ω i)), IsCover (algebraMap (𝓞 c.F) c.F) R a b ω ∧
          ∀ i, HasCones (ConeZ E φs) (C i) ∧ PolRay (comb 0 (resInt _ φs) 0 (resInt _ φs)) (resInt _ φs) 1 (C i)

def PolGlueSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (I : Type) (_ : Finite I) (R : I → Type) (_ : ∀ i, CommRing (R i)) (a : I → 𝓞 c.F)
    (b : ∀ i, 𝓞 c.F →+* R i) (ω : ∀ i, R i →+* c.F) (C : ∀ i, Model Xo c (ω i)) (ψ φ : InvFun (𝓞 E)) (k : ℕ)
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop),
    IsTwInv H ψ → IsTwInv H φ → IsCover (algebraMap (𝓞 c.F) c.F) R a b ω →
    (∀ i, HasCones Cn (C i) ∧ PolRay ψ φ k (C i)) → ∃ Z : GMod Xo c, HasCones Cn Z ∧ PolRay ψ φ k Z

def PhiDivZSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs →
    HasCones (ConeZ E φs) Z → ∀ a b : ℕ, ∃ BD, IsPhiDiv (comb a (comb 0 (resInt _ φs) 0 (resInt _ φs)) b (resInt _ φs)) Z BD

def PhiDivOSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)),
    Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeO H φ) Z →
    ∀ a d b : ℕ, ∃ BD, IsPhiDiv (comb a (comb d (resInt _ φs) 0 φ) b φ) Z BD

def UniformSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ (Xo : ∀ l : Level H, Moduli D l) (ψ φ : InvFun (𝓞 E)) (k : ℕ)
      (Z : ∀ (l : Level H) (c : Coeff l), (∀ p : ℕ, p.Prime → l.GoodAt p) → GMod (Xo l) c), IsTwInv H ψ → IsTwInv H φ →
      (∀ l c hg, PolRay ψ φ k (Z l c hg) ∧ ∀ a b, ∃ BD, IsPhiDiv (comb a ψ b φ) (Z l c hg) BD) →
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∀ l c hg, ∃ BD, IsPol (comb a ψ b φ) (a * k) (Z l c hg) BD

def RefineSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ),
    Module.finrank ℚ E * q ≤ g → IsPolFan id g φs → (∀ N ∈ 𝒩, 0 < N) → ∃ φ, Refines H q φs 𝒩 φ

def GenFanSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min D.p D.q) φ → NoSelfInt H.bar (min D.p D.q) φ →
      ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), ∃ (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d k : ℕ),
        0 < d ∧ GenTor Y ∧ HasCones (ConeO H φ) Y ∧ IsPol (comb 0 φ d φ) k Y BD

def GenMapSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E))
    (d k : ℕ) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs →
    Refines H (min D.p D.q) φs 𝒩 φ → IsPol (comb d (resInt _ φs) 0 φ) k X DX → HasCones (ConeO H φ) Y →
    ∃ ρ : gen Y ⟶ gen X, Y.jQ ≫ ρ = X.jQ

def IsBlowOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X)
    (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n : ℕ) : Prop :=
  0 < n ∧ Z.j ≫ π = X.j ∧ π ≫ X.s = Z.s ∧ Y.jQ ≫ e.hom = Z.jQ ∧ EX.idealSheaf = J.comap π ∧
    EX.idealSheaf.comap (e.hom ≫ genι Z) = (BY.idealSheaf ^ n).comap (genι Y) ∧
    J = ((BY.idealSheaf ^ n).comap (genι Y)).map (e.hom ≫ genι Z ≫ π) ∧
    ∀ L : LB X.X, GlobalTheory.IsAmpleLB L → ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow (L.pull π) T) (GlobalTheory.CechPic.dual EX.lb))

def BlowExSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (k : ℕ) (ρ : gen Y ⟶ gen X),
    Y.jQ ≫ ρ = X.jQ → GlobalTheory.IsAmpleLB (polOf Y k BY) → (∀ x ∈ BY.idealSheaf.support, x ∉ abLocus Y.t.G) →
    ∃ (Z : GMod Xo c) (π : _) (e : _) (J : _) (EX : _) (n : ℕ), IsBlowOf X Z Y BY π e J EX n

def BlowOrdSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : _) (e : _) (J : _) (EX : _)
    (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X),
    Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X →
    X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n →
    IsPhiDiv (comb 0 φ (n * d') φ) Z EX ∧ HasCones (ConeO H φ) Z

def BlowPolSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : _) (e : _) (J : _) (EX : _)
    (n k b : ℕ) (ψ φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), IsPol ψ k X DX → IsBlowOf X Z Y BY π e J EX n → 0 < b →
    IsPhiDiv (comb 0 φ b φ) Z EX → GenTor Y → PolRay ψ φ k Z ∧ GenTor Z

def ConeArcSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l), (∀ p : ℕ, p.Prime → l.GoodAt p) →
    ∀ (X : GMod (Xo l) c) (ψ : InvFun (𝓞 E)) (k : ℕ) (DX : EffCartierData X.X), IsTame ψ → IsPol ψ k X DX → X.N4

def DomSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l, ∃ (s : Sys Xo) (𝒩 : Finset ℕ), (∀ N ∈ 𝒩, 0 < N) ∧
      ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Z : GMod (Xo l) c),
        HasCones (fun _ _ _ _ _ γ => ∀ N ∈ 𝒩, IsFine N γ) Z → DomAll s hg Z

end GlobalTheory.TorRef
