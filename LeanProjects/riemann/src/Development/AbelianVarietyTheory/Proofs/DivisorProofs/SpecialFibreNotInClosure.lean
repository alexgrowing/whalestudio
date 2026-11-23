import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

section Open

variable {S : Scheme.{0}} {X T : Over S}

def InOpen (U : X.left.Opens) (w : T ⟶ X) : Prop := w.left ⁻¹ᵁ U = ⊤

theorem inOpen_top (w : T ⟶ X) : InOpen ⊤ w := rfl

theorem InOpen.comp {U : X.left.Opens} {w : T ⟶ X} (h : InOpen U w) {T' : Over S} (u : T' ⟶ T) :
    InOpen U (u ≫ w) := by
  unfold InOpen at h ⊢
  rw [Over.comp_left, Scheme.Hom.comp_preimage, h]
  rfl

def CubeIn [GrpObj X] (U : X.left.Opens) (z a b c : T ⟶ X) : Prop :=
  ∀ i j k : ℕ, i ≤ 1 → j ≤ 1 → k ≤ 1 → InOpen U (z * a ^ i * b ^ j * c ^ k)

end Open

section Field

variable {C : Type} [Field C]

def CubeFn (A : Over (Sp C)) : Type 1 :=
  ∀ (S : Type) [CommRing S] (t : Sp S ⟶ Sp C),
    (Over.mk t ⟶ A) → (Over.mk t ⟶ A) → (Over.mk t ⟶ A) → (Over.mk t ⟶ A) → Sˣ

def CubeFn.IsNatural {A : Over (Sp C)} [GrpObj A] (Θ : CubeFn A) (V : A.left.Opens) : Prop :=
  ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (t : Sp S ⟶ Sp C) (t' : Sp S' ⟶ Sp C)
    (z a b c : Over.mk t ⟶ A) (z' a' b' c' : Over.mk t' ⟶ A),
    z'.left = spMap φ ≫ z.left → a'.left = spMap φ ≫ a.left → b'.left = spMap φ ≫ b.left →
    c'.left = spMap φ ≫ c.left → CubeIn V z a b c →
    (Θ S' t' z' a' b' c' : S') = φ (Θ S t z a b c : S)

def CubeFn.GivesWeil [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)) (Θ : CubeFn A.A) (V : A.A.left.Opens) :
    Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ x y z : Pts A.A, x ^ N = 1 → y ^ N = 1 →
    (∀ i j : ℕ, InOpen V (z * x ^ i * y ^ j)) →
    weil A N x y = (∏ i ∈ Finset.range N, Θ C (𝟙 _) z (y ^ i) y x) /
      ∏ i ∈ Finset.range N, Θ C (𝟙 _) z (x ^ i) x y

def HasCubeFn [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)) : Prop :=
  ∀ V : A.A.left.Opens, (∃ g : LB.Gen (A.L.pull V.ι), g.IsGen) →
    ∃ Θ : CubeFn A.A, Θ.IsNatural V ∧ Θ.GivesWeil A V

example {A : Over (Sp C)} [GrpObj A] (V : A.left.Opens) :
    CubeFn.IsNatural (A := A) (fun _ _ _ _ _ _ _ => 1) V := by
  intro S S' _ _ φ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp

end Field

section Ring

variable (p : ℕ) (O : Type) [CommRing O]

def LocalUnits : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra O R] [Algebra.Smooth O R] (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B]
    [Module.Finite O B] [Module.Flat O B] (θ : R →ₐ[O] B) (ψ : B →ₐ[O] O) (f g : R) (c : O), c ≠ 0 →
    f * g = algebraMap O R c → ∃ u : Bˣ, θ f = algebraMap O B (ψ (θ f)) * u

def SpecialFibreNotInClosure : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra O R] [Algebra.Smooth O R] (f : R), f ≠ 0 →
    (∃ q : PrimeSpectrum R, (p : R) ∈ q.asIdeal) →
    ∃ (q : PrimeSpectrum R) (g : R) (c : O), (p : R) ∈ q.asIdeal ∧ g ∉ q.asIdeal ∧ c ≠ 0 ∧
      f ∣ algebraMap O R c * g

end Ring

section AtPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

def MeetsSpecial (U : P.G.left.Opens) : Prop :=
  ∃ x : P.G.left, x ∈ U ∧ (p : O) ∈ PrimeSpectrum.asIdeal (R := O) (P.G.hom x)

def HasTrivialisingOpen : Prop :=
  ∃ U : P.G.left.Opens, MeetsSpecial P U ∧ ∃ g : LB.Gen (P.A.L.pull (P.gen ⁻¹ᵁ U).ι), g.IsGen

def TranslatesInto : Prop :=
  ∀ U : P.G.left.Opens, MeetsSpecial P U → ∀ (J : Type) [Finite J] (a : J → (specO O O ⟶ P.G)),
    ∃ z : specO O O ⟶ P.G, ∀ i, InOpen U (z * a i)

def IsGeneric (z : specO O O ⟶ P.G) (z' : Pts P.A.A) : Prop :=
  z'.left ≫ P.gen = spMap (algebraMap O C) ≫ z.left

def CubeValuesIntegral : Prop :=
  ∀ (U : P.G.left.Opens) (Θ : CubeFn P.A.A), Θ.IsNatural (P.gen ⁻¹ᵁ U) →
    ∀ (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] [Module.Finite O B] [Module.Flat O B],
    Nonempty (B →ₐ[O] O) → ∀ z a b c : specO O B ⟶ P.G, CubeIn U z a b c →
    ∃ (d : Cˣ) (u : Bˣ), ∀ (ψ : B →ₐ[O] O) (z' a' b' c' : Pts P.A.A),
      IsGeneric P (ptMap ψ ≫ z) z' → IsGeneric P (ptMap ψ ≫ a) a' → IsGeneric P (ptMap ψ ≫ b) b' →
      IsGeneric P (ptMap ψ ≫ c) c' →
      (Θ C (𝟙 _) z' a' b' c' : C) = d * algebraMap O C (ψ u)

variable [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

def WeilIntegralOn (B : Type) [CommRing B] [Algebra O B] : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ x y : specO O B ⟶ P.Gt, x ^ N = 1 → y ^ N = 1 →
    ∃ u : B, ∀ ψ : B →ₐ[O] O,
      algebraMap O C (ψ u) = (weil P.A N (P.toA (ptMap ψ ≫ x)) (P.toA (ptMap ψ ≫ y)) : C)

def WeilIntegralLocal : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] [Module.Finite O B] [Module.Flat O B],
    WeilIntegralOn P B

def WeilIntegralFinite : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] [Module.Flat O B], WeilIntegralOn P B

theorem toA_isGeneric (x : specO O O ⟶ P.Gt) : IsGeneric P (P.toG x) (P.toA x) :=
  (P.eq_toA_iff x _).1 rfl

end AtPoint

end GlobalTheory.WeilIntegral
