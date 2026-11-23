import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.ThickQuot

section Ring

variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {𝔟 : Ideal B}
  (h𝔟 : δ.IsSubDPIdeal 𝔟)
include h𝔟

theorem isSubDPIdeal_inf : δ.IsSubDPIdeal (𝔟 ⊓ J) := by
  rw [inf_eq_left.mpr h𝔟.isSubideal]; exact h𝔟

def qdp : DividedPowers (J.map (Ideal.Quotient.mk 𝔟)) :=
  DividedPowers.Quotient.dividedPowers δ (isSubDPIdeal_inf δ h𝔟)

theorem qdp_apply {n : ℕ} {a : B} (ha : a ∈ J) :
    (qdp δ h𝔟).dpow n (Ideal.Quotient.mk 𝔟 a) = Ideal.Quotient.mk 𝔟 (δ.dpow n a) :=
  DividedPowers.Quotient.dpow_apply δ (isSubDPIdeal_inf δ h𝔟) ha

theorem qdp_isDPMorphism : IsDPMorphism δ (qdp δ h𝔟) (Ideal.Quotient.mk 𝔟) :=
  DividedPowers.Quotient.isDPMorphism δ (isSubDPIdeal_inf δ h𝔟)

theorem lift_list (l : List (ℕ × (B ⧸ 𝔟))) (hl : ∀ p ∈ l, p.2 ∈ J.map (Ideal.Quotient.mk 𝔟)) :
    ∃ l' : List (ℕ × B), (∀ p ∈ l', p.2 ∈ J) ∧ l'.map Prod.fst = l.map Prod.fst ∧
      Ideal.Quotient.mk 𝔟 ((l'.map fun p ↦ δ.dpow p.1 p.2).prod) =
        (l.map fun p ↦ (qdp δ h𝔟).dpow p.1 p.2).prod := by
  induction l with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2, h3⟩ := ih fun q hq ↦ hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨a, ha, hpa⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (hl p List.mem_cons_self)
    refine ⟨(p.1, a) :: l', ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ha
      · exact h1 q hq
    · simp [h2]
    · simp only [List.map_cons, List.prod_cons, map_mul, h3]
      rw [← hpa, qdp_apply δ h𝔟 ha]

theorem isLev_qdp {n : ℕ} (hn : IsLev δ n) : IsLev (qdp δ h𝔟) n := by
  rw [isLev_iff_prod] at hn ⊢
  intro l hl hs
  obtain ⟨l', h1, h2, h3⟩ := lift_list δ h𝔟 l hl
  rw [← h3, hn l' h1 (h2 ▸ hs), map_zero]

theorem isDPNilpotent_quotient (hδ : IsNilDP δ) : IsNilDP (qdp δ h𝔟) := by
  rw [isDPNilpotent_iff_exists_isLevel] at hδ ⊢
  obtain ⟨n, hn⟩ := hδ
  exact ⟨n, isLev_qdp δ h𝔟 hn⟩

end Ring

section Thick

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  (T : Thick κ t) {𝔟 : Ideal T.B} (h𝔟 : T.δ.IsSubDPIdeal 𝔟)
include h𝔟

def quot : Thick κ t where
  B := T.B ⧸ 𝔟
  J := T.J.map (Ideal.Quotient.mk 𝔟)
  δ := qdp T.δ h𝔟
  nil := isDPNilpotent_quotient T.δ h𝔟 T.nil
  dp := by
    have : algebraMap R (T.B ⧸ 𝔟) = (Ideal.Quotient.mk 𝔟).comp (algebraMap R T.B) := rfl
    rw [this]
    exact (qdp_isDPMorphism T.δ h𝔟).comp _ T.dp
  B₀ := T.B₀
  π := Ideal.Quotient.lift 𝔟 T.π fun a ha ↦ (T.ker a).2 (h𝔟.isSubideal ha)
  surj := Ideal.Quotient.lift_surjective_of_surjective _ _ T.surj
  ker b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.lift_mk, T.ker, Ideal.mem_quotient_iff_mem h𝔟.isSubideal]
  x := T.x
  w := by
    convert T.w using 2
    exact RingHom.ext fun _ ↦ rfl

def proj : T ⟶ quot T h𝔟 where
  φ := Ideal.Quotient.mkₐ R 𝔟
  φ₀ := RingHom.id T.B₀
  comm _ := rfl
  dp := qdp_isDPMorphism T.δ h𝔟
  pt := by
    show spMap (RingHom.id T.B₀) ≫ T.x = T.x
    rw [spMap_id, Category.id_comp]

def desc {S : Thick κ t} (a : T ⟶ S) (ha : ∀ b ∈ 𝔟, a.φ b = 0) : quot T h𝔟 ⟶ S where
  φ := Ideal.Quotient.liftₐ 𝔟 a.φ ha
  φ₀ := a.φ₀
  comm b := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact a.comm c
  dp := by
    refine ⟨?_, fun {n} y hy ↦ ?_⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      obtain ⟨c, hc, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
      exact Thick.Hom.mem a hc
    · obtain ⟨c, hc, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
      have e1 : (quot T h𝔟).δ.dpow n (Ideal.Quotient.mk 𝔟 c) = Ideal.Quotient.mk 𝔟 (T.δ.dpow n c) :=
        qdp_apply T.δ h𝔟 hc
      rw [e1]
      exact a.dp.2 c hc
  pt := a.pt

end Thick

section Main

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem exists_quotient : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (T : Thick κ t) (𝔟 : Ideal T.B), T.δ.IsSubDPIdeal 𝔟 → ∃ (G : Thick κ t) (q : T ⟶ G), Function.Surjective q.φ ∧ (∀ b, q.φ b = 0 ↔ b ∈ 𝔟) ∧ G.J = T.J.map (q.φ : T.B →+* G.B) ∧ (∀ n, IsLev T.δ n → IsLev G.δ n) ∧ ∀ (S : Thick κ t) (a : T ⟶ S), (∀ b ∈ 𝔟, a.φ b = 0) → ∃! g : G ⟶ S, q ≫ g = a := by
  intro R _ I κ X t T 𝔟 h𝔟
  refine ⟨quot T h𝔟, proj T h𝔟, Ideal.Quotient.mkₐ_surjective R 𝔟, fun b ↦ Ideal.Quotient.eq_zero_iff_mem,
    rfl, fun n hn ↦ isLev_qdp T.δ h𝔟 hn, fun S a ha ↦
      ⟨desc T h𝔟 a ha, Thick.hom_ext fun _ ↦ rfl, fun g hg ↦ Thick.hom_ext fun b ↦ ?_⟩⟩
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact congrArg (fun f : T ⟶ S ↦ f.φ c) hg

end Main

end GlobalTheory.ThickQuot
