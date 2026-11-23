import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Pairings

variable {S : Scheme.{0}} {A B G G' : Over S} [GrpObj A] [GrpObj B] [GrpObj G] [GrpObj G']

def lamPull (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) : LB (A ⊗ B).left :=
  cubeLB G ![fst A B ≫ f₁, snd A B ≫ f₂] L

def LamEq (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') : Prop :=
  LBIso (lamPull L f₁ f₂) (lamPull L' g₁ g₂)

def WeilEqAt (k : ℕ) (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') :
    Prop :=
  ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ B), x ^ k = 1 → y ^ k = 1 → ∀ c : Γ(T.left, ⊤)ˣ,
    Out.WeilIs G L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs G' L' k (x ≫ g₁) (y ≫ g₂) c

def WeilEq (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') : Prop :=
  ∀ k : ℕ, 0 < k → WeilEqAt k L f₁ f₂ L' g₁ g₂

end Pairings

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev Zw (H : Host E) : Subalgebra ℤ (𝓞 E) := Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))

def wz (H : Host E) : Zw H := ⟨H.w0, Algebra.self_mem_adjoin_singleton ℤ H.w0⟩

structure CMCurve (H : Host E) (R : Type) [CommRing R] (ω : R) where

  P : Out.PolAV (Sp R)
  dim : P.g = 1

  act : OAct (Zw H) P.A

  v : epsR R ⟶ P.A
  basis : IsLieBasis (G := P.A) ![v]
  eigen : (v ≫ act.act (wz H)).left = spMap (epsScaleR ω) ≫ v.left

variable {H : Host E}

structure IsPrincipal {S : Scheme.{0}} (t : SAB H S) : Prop where
  proper : IsProper t.G.hom
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L

def SigAt (H : Host E) (p q : ℕ) {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G)
    {k : Type} [Field k] (x : Sp k ⟶ S) (ρ : k) : Prop :=
  ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → LieMult act x τ p) ∧ (τ H.rt ≠ ρ → LieMult act x τ q)

def HasSig (H : Host E) (p q : ℕ) {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (act : OAct (𝓞 E) G)
    (ρ : R) : Prop :=
  ρ ^ 2 = -(H.d : R) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (β : R →+* k), SigAt H p q act (spMap β) (β ρ)

def herm (D : Datum H) (x y : D.La) : Zw H :=
  ((D.EF (H.w0 • x) y - D.EF x y : ℤ) : Zw H) + ((D.EF x y : ℤ) : Zw H) * wz H

open Classical in

def posSign (D : Datum H) : ℤˣ := if (0 < H.rt0.im ↔ D.q = 0) then 1 else -1

structure IsTensorMap {R : Type} [CommRing R] {ω : R} (C : CMCurve H R ω) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (h : La → La → Zw H) (t : SAB H (Sp R)) (φ : La → (C.P.A ⟶ t.G)) : Prop where
  hom : ∀ x, IsMonHom (φ x)
  add : ∀ x y, φ (x + y) = φ x * φ y
  lin : ∀ (a : 𝓞 E) x, φ (a • x) = φ x ≫ t.act.act a
  bal : ∀ (b : Zw H) x, φ ((b : 𝓞 E) • x) = C.act.act b ≫ φ x

  onto : ∀ (T : Over (Sp R)) (y : T ⟶ t.G), ∃ (n : ℕ) (x : Fin n → La) (c : Fin n → (T ⟶ C.P.A)),
    y = (List.ofFn fun i => c i ≫ φ (x i)).prod

  inj : ∀ (T : Over (Sp R)) (n : ℕ) (x : Fin n → La) (c : Fin n → (T ⟶ C.P.A)),
    (List.ofFn fun i => c i ≫ φ (x i)).prod = 1 →
      ∀ ℓ : La →ₗ[Zw H] Zw H, (List.ofFn fun i => c i ≫ C.act.act (ℓ (x i))).prod = 1

  pol : ∀ x y, LamEq t.PP.L (φ x) (φ y) C.P.L (C.act.act (h x y)) (𝟙 C.P.A)

def IsTensorSgn (ε : ℤˣ) (D : Datum H) {R : Type} [CommRing R] {ω : R} (C : CMCurve H R ω)
    (t : SAB H (Sp R)) : Prop :=
  ∃ φ : D.La → (C.P.A ⟶ t.G), IsTensorMap C (fun x y => (((ε : ℤ) : Zw H)) * herm D x y) t φ

def IsTensor (D : Datum H) {R : Type} [CommRing R] {ω : R} (C : CMCurve H R ω) (t : SAB H (Sp R)) : Prop :=
  IsTensorSgn (posSign D) D C t

example (D : Datum H) {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G) {k : Type} [Field k]
    (x : Sp k ⟶ S) (ρ : k) : SigAt H D.p D.q act x ρ ↔ DetCond D act x ρ := Iff.rfl

example (D : Datum H) (x : D.La) : herm D x x = ((D.EF (H.w0 • x) x : ℤ) : Zw H) := by
  simp [herm, D.alt]

theorem cmHost_bar_halfIntegerGenerator (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  have hr : H.bar H.rt = -H.rt := by
    have h2 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exfalso
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h3 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
      rw [← H.bar_eq, h] at h3
      have him : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h3.symm
      have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun a : 𝓞 E => φ (a : E)) H.rt_sq
        simpa using this
      have h5 := congrArg Complex.re h4
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      simp [sq, him] at h5
      nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
    · exact h
  have h2 : (2 : 𝓞 E) * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [hr, sub_eq_add_neg, map_ofNat] using this
  have : (2 : 𝓞 E) * (H.bar H.w0 - (1 - H.w0)) = 0 := by linear_combination h2 + H.two_weight_eq_one_add_root
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left two_ne_zero)

theorem herm_conj (D : Datum H) (x y : D.La) : (herm D y x : 𝓞 E) = H.bar (herm D x y : 𝓞 E) := by
  have hb : H.bar H.w0 = 1 - H.w0 := cmHost_bar_halfIntegerGenerator H
  have sk : ∀ a b, D.EF a b = - D.EF b a := fun a b => by
    have := D.alt (a + b)
    simp only [map_add, LinearMap.add_apply, D.alt] at this
    linarith
  have h1 : D.EF (H.w0 • y) x = D.EF (H.w0 • x) y - D.EF x y := by
    rw [D.adj, hb, sk y, sub_smul, one_smul, map_sub, LinearMap.sub_apply]; ring
  simp only [herm, wz, h1, sk y x]
  simp [hb]
  ring

end GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms
