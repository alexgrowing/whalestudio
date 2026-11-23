import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}}

structure BChart (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z) (d : ℕ) (V : Z.Opens) where
  affine : IsAffineOpen V
  n : ℕ
  x : Fin n → Γ(Z, V)
  t : Fin d → Γ(Z, V)
  etale : (MvPolynomial.eval₂Hom (strV q V) (Sum.elim x t) : MvPolynomial (Fin n ⊕ Fin d) K →+* Γ(Z, V)).Etale
  ker : RingHom.ker (i.app V).hom = Ideal.span (Set.range t)
  C : Fin d → Y.Opens
  C_aff : ∀ k, IsAffineOpen (C k)
  C_le : ∀ k, C k ≤ π ⁻¹ᵁ V
  C_cover : π ⁻¹ᵁ V ≤ ⨆ k, C k
  u : ∀ k, Fin d → Γ(Y, C k)
  surj : ∀ k, Function.Surjective (MvPolynomial.eval₂Hom (π.appLE V (C k) (C_le k)).hom (u k))
  rel : ∀ k, RingHom.ker (MvPolynomial.eval₂Hom (π.appLE V (C k) (C_le k)).hom (u k)) =
    Ideal.span (insert (MvPolynomial.X k - 1) (Set.range fun j => MvPolynomial.C (t j) - MvPolynomial.C (t k) * MvPolynomial.X j))
  inter : ∀ k j, C k ⊓ C j = Y.basicOpen (u k j)

structure Blow (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z) (D : E.LineData Y) (d : ℕ) where
  closed : IsClosedImmersion i
  f : ∀ {V : Scheme.{0}} (a : V ⟶ D.Y), Γ(V, ⊤)
  f_nat : ∀ {V' V : Scheme.{0}} (g : V' ⟶ V) (a : V ⟶ D.Y), f (g ≫ a) = g.appTop.hom (f a)
  f_u : ∀ {V : Scheme.{0}} (a b : V ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f), f a = (D.u a b h : Γ(V, ⊤)) * f b

  U : Z.Opens
  U_eq : (U : Set Z) = (Set.range i)ᶜ
  iso : IsIso (π ∣_ U)
  unit : ∀ {V : Scheme.{0}} (a : V ⟶ D.Y), ⊤ ≤ (a ≫ D.f ≫ π) ⁻¹ᵁ U → IsUnit (f a)
  loc : sSup (𝒱D D) = ⊤
  ι : Type
  [fin : Fintype ι]
  V : ι → Z.Opens
  cover : ⊤ ≤ i ⁻¹ᵁ (⨆ α, V α)
  c : ∀ α, BChart q i π d (V α)
  σ : ∀ α k, ((c α).C k : Scheme.{0}) ⟶ D.Y
  σ_f : ∀ α k, σ α k ≫ D.f = ((c α).C k).ι
  f_σ : ∀ α k, f (σ α k) = ((c α).C k).topIso.inv.hom ((π.appLE (V α) ((c α).C k) ((c α).C_le k)).hom ((c α).t k))

def HodgeKill : Prop := ∀ (K : Type) [Field K] [CharZero K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) [IsProper q]
  [Smooth q] (i : W ⟶ Z) (π : Y ⟶ Z) [IsProper π] (D : E.LineData Y) (d : ℕ), 0 < d → Nonempty (Blow q i π D d) →
  ∀ e : Hdg (π ≫ q) 1 2, IsDlogFirstChernClass (π ≫ q) D e → ∀ (a n a' n' : ℕ) (c : Hdg q a n) (y : Hdg q a' n'),
    (pullH π rfl a n c = 0 ∨ ∃ (a₀ n₀ : ℕ) (ha : 1 + a₀ = a) (hn : 2 + n₀ = n) (w : Hdg (π ≫ q) a₀ n₀),
      pullH π rfl a n c = cupH (π ≫ q) ha hn e w) →
    pullH i rfl a' n' y = 0 → cupH q rfl rfl c y = 0

def CupLaws : Prop := ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)),
  (∀ {a a' c i j n : ℕ} (ha : a + a' = c) (h : i + j = n), ∃ b : Hdg q a i →ₗ[K] Hdg q a' j →ₗ[K] Hdg q c n,
    ∀ x y, b x y = cupH q ha h x y) ∧
  (∀ {a₁ a₂ a₃ a₁₂ a₂₃ c i j k ij jk n : ℕ} (h₁ : a₁ + a₂ = a₁₂) (h₂ : a₁₂ + a₃ = c) (h₃ : a₂ + a₃ = a₂₃) (h₄ : a₁ + a₂₃ = c)
    (g₁ : i + j = ij) (g₂ : ij + k = n) (g₃ : j + k = jk) (g₄ : i + jk = n) (x : Hdg q a₁ i) (y : Hdg q a₂ j) (z : Hdg q a₃ k),
    cupH q h₂ g₂ (cupH q h₁ g₁ x y) z = cupH q h₄ g₄ x (cupH q h₃ g₃ y z)) ∧
  (∀ {a a' c i j n : ℕ} (ha : a + a' = c) (ha' : a' + a = c) (h : i + j = n) (h' : j + i = n) (x : Hdg q a i) (y : Hdg q a' j),
    cupH q ha h x y = (-1 : ℤ) ^ (i * j) • cupH q ha' h' y x) ∧
  (∀ {a n : ℕ} (x : Hdg q a n), cupH q (Nat.zero_add a) (Nat.zero_add n) (oneH q) x = x) ∧
  (∀ (Y : Scheme.{0}) (p : Y ⟶ Spec (CommRingCat.of K)) (u : Y ⟶ X) (hu : u ≫ q = p) {a a' c i j n : ℕ} (ha : a + a' = c)
    (h : i + j = n) (x : Hdg q a i) (y : Hdg q a' j),
    pullH u hu c n (cupH q ha h x y) = cupH p ha h (pullH u hu a i x) (pullH u hu a' j y)) ∧
  (∀ (a n : ℕ) (x : Hdg q a n), pullH (𝟙 X) (Category.id_comp q) a n x = x) ∧
  ∀ (Y Y' : Scheme.{0}) (p : Y ⟶ Spec (CommRingCat.of K)) (p' : Y' ⟶ Spec (CommRingCat.of K)) (u : Y ⟶ X) (hu : u ≫ q = p)
    (v : Y' ⟶ Y) (hv : v ≫ p = p') (w : Y' ⟶ X) (hw : w ≫ q = p'), v ≫ u = w → ∀ (a n : ℕ) (x : Hdg q a n),
    pullH v hv a n (pullH u hu a n x) = pullH w hw a n x

def Slant : Prop := ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K))
  (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X')
  (hP : IsPullback p₁ p₂ q q') (a i a' j c n : ℕ) (ha : a + a' = c) (h : i + j = n) (φ : Module.Dual K (Hdg q a i)),
  ∃ sl : Hdg (p₁ ≫ q) c n →ₗ[K] Hdg q' a' j,
    (∀ u v, sl (cupH _ ha h (pullH p₁ rfl a i u) (pullH p₂ hP.w.symm a' j v)) = φ u • v) ∧
    ∀ (b i' b' j' : ℕ) (hb : b + b' = c) (h' : i' + j' = n), (b, i') ≠ (a, i) → ∀ (u : Hdg q b i') (v : Hdg q' b' j'),
      sl (cupH _ hb h' (pullH p₁ rfl b i' u) (pullH p₂ hP.w.symm b' j' v)) = 0

section Rel

universe w v u

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (Q : ObjectProperty C)

def RelNull : ∀ (n : ℕ), CH.Cn F n → Prop
  | 0, z => z = 0
  | n + 1, z => ∃ b ∈ relS F Q n, CH.d F n b = z

end Rel

def On (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) : ObjectProperty (Thick (smFun Z q)) :=
  fun T => ∃ w : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ W,
    w ≫ i = pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T

abbrev G (q : Z ⟶ Spec (CommRingCat.of K)) (a : ℕ) : Thick (smFun Z q) ⥤ ModuleCat.{0} K :=
  sq (thFil (smFun Z q) (a : ℤ)) (thFil (smFun Z q) ((a : ℤ) + 1))

def clsH (q : Z ⟶ Spec (CommRingCat.of K)) {a n : ℕ} (z : CH.Cn (G q a) n) (hz : CH.d (G q a) n z = 0) : Hdg q a n :=
  (CH.cx (G q a)).cls z hz

def cupC (q : Z ⟶ Spec (CommRingCat.of K)) {a a' c i j n : ℕ} (ha : a + a' = c) (h : i + j = n) :
    CH.Cn (G q a) i →ₗ[K] CH.Cn (G q a') j →ₗ[K] CH.Cn (G q c) n :=
  (grOk (smFun Z q) ha).pair.cupC h

def pullC {p : Z ⟶ Spec (CommRingCat.of K)} {q : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z) (hu : u ≫ p = q) (a n : ℕ) :
    CH.Cn (G p a) n →ₗ[K] CH.Cn (G q a) n :=
  ((smS u hu).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ)) (b' := thFil _ ((a : ℤ) + 1))
    (fun _ _ hx => hx) fun _ _ hx => hx).pullC n

def RelLift : Prop := ∀ (K : Type) [Field K] (W Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) [Mono i] (a n : ℕ)
  (y : Hdg q a n), pullH i rfl a n y = 0 →
  ∃ (z : CH.Cn (G q a) n) (hz : CH.d (G q a) n z = 0), z ∈ relS (G q a) (On q i) n ∧ clsH (a := a) q z hz = y

def RelInj : Prop := ∀ (K : Type) [Field K] [CharZero K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) [IsProper q]
  [Smooth q] (i : W ⟶ Z) (π : Y ⟶ Z) [IsProper π] (D : E.LineData Y) (d : ℕ), 0 < d → Nonempty (Blow q i π D d) →
  ∀ (a n : ℕ) (z : CH.Cn (G q a) n), CH.d (G q a) n z = 0 → z ∈ relS (G q a) (On q i) n →
    RelNull (G (π ≫ q) a) (On (π ≫ q) (pullback.snd i π)) n (pullC π rfl a n z) → RelNull (G q a) (On q i) n z

def RelKill : Prop := ∀ (K : Type) [Field K] [CharZero K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) [IsProper q]
  [Smooth q] (i : W ⟶ Z) (π : Y ⟶ Z) [IsProper π] (D : E.LineData Y) (d : ℕ), 0 < d → Nonempty (Blow q i π D d) →
  ∀ (r : CH.Cn (G (π ≫ q) 1) 2) (hr : CH.d (G (π ≫ q) 1) 2 r = 0), IsDlogFirstChernClass (π ≫ q) D (clsH (a := 1) (π ≫ q) r hr) →
  ∀ (a n : ℕ) (z : CH.Cn (G (π ≫ q) a) n), CH.d (G (π ≫ q) a) n z = 0 → z ∈ relS (G (π ≫ q) a) (On (π ≫ q) (pullback.snd i π)) n →
    RelNull (G (π ≫ q) (1 + a)) (On (π ≫ q) (pullback.snd i π)) (2 + n) (cupC (π ≫ q) (a := 1) (a' := a) rfl rfl r z)

end CrystallineSemistableComparison.Onto

end
