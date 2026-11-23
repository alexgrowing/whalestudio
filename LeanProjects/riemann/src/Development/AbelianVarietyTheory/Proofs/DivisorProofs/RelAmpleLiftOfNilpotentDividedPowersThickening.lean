import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleLiftSquareZeroThickening
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleNilThickening

theorem exists_pow_eq_bot_of_isNilDP {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I}
    (h : IsNilDP κ) : ∃ N : ℕ, I ^ N = ⊥ := by
  obtain ⟨N, hN⟩ := h
  have hlen : ∀ l : List R, ((l.map fun x => ((1 : ℕ), x)).map Prod.fst).sum = l.length := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega
  have hprod : ∀ l : List R, (∀ x ∈ l, x ∈ I) →
      ((l.map fun x => ((1 : ℕ), x)).map fun p => κ.dpow p.1 p.2).prod = l.prod := by
    intro l hl; induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [κ.dpow_one (hl a (by simp)), ih fun x hx => hl x (by simp [hx])]
  have hl : ∀ l : List R, (∀ x ∈ l, x ∈ I) → N ≤ l.length → l.prod = 0 := by
    intro l hl' hle
    rw [← hprod l hl']
    exact hN _ (by simpa using hl') (by rw [hlen]; exact hle)
  have key : ∀ k : ℕ, ∀ y ∈ I ^ k, ∀ l : List R, (∀ x ∈ l, x ∈ I) → N ≤ k + l.length → l.prod * y = 0 := by
    intro k
    induction k with
    | zero => intro y _ l hl' hle; rw [hl l hl' (by omega), zero_mul]
    | succ k ih =>
      intro y hy l hl' hle
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on (C := fun y => l.prod * y = 0) hy ?_ ?_
      · intro a ha b hb
        have := ih a ha (b :: l) (by simpa [hb] using hl') (by simp; omega)
        rw [List.prod_cons] at this
        rw [← this]; ring
      · intro y z hy hz; rw [mul_add, hy, hz, add_zero]
  refine ⟨N, eq_bot_iff.2 fun y hy => ?_⟩
  have := key N y hy [] (fun x hx => by cases hx) (Nat.le_add_right N _)
  simpa using this

end GlobalTheory.AmpleNilThickening

namespace GlobalTheory.AmpleNilThickening

theorem relAmple_of_pow_eq_bot : ∀ (n : ℕ) (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π ^ n = ⊥ →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (β : X₀.left ⟶ X.left), IsPullback β X₀.hom X.hom (spMap π) →
      LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L₀ : LB X₀.left), L.IsLB → L₀.IsLB → LBIso L₀ (L.pull β) →
      Out.RelAmple X₀ L₀ → Out.RelAmple X L := by
  intro n
  induction n with
  | zero =>
    intro R R₀ _ _ π hπ hn X X₀ β hβ hX L L₀ hL hL₀ hw hA
    have h2 : RingHom.ker π ^ 2 = ⊥ := eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ h2 X X₀ β hβ hX L L₀ hL hL₀ hw hA
  | succ n ih =>
    intro R R₀ _ _ π hπ hn X X₀ β hβ hX L L₀ hL hL₀ hw hA
    by_cases h0 : n = 0
    · subst h0
      have h2 : RingHom.ker π ^ 2 = ⊥ := eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
      exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ h2 X X₀ β hβ hX L L₀ hL hL₀ hw hA
    set I := RingHom.ker π with hI
    let J : Ideal R := I ^ n
    let q : R →+* R ⧸ J := Ideal.Quotient.mk J
    have hJI : J ≤ RingHom.ker π := Ideal.pow_le_self h0
    let π₁ : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π fun a ha => (RingHom.mem_ker).1 (hJI ha)
    have hfac : π = π₁.comp q := RingHom.ext fun _ => rfl
    have hπ₁ : Function.Surjective π₁ := fun y => by
      obtain ⟨x, hx⟩ := hπ y
      exact ⟨q x, hx⟩
    have hker₁ : RingHom.ker π₁ ^ n = ⊥ := by
      have hle : RingHom.ker π₁ ≤ I.map q := by
        intro z hz
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
        have hx : x ∈ I := RingHom.mem_ker.2 (RingHom.mem_ker.1 hz)
        exact Ideal.mem_map_of_mem q hx
      refine eq_bot_iff.2 ((Ideal.pow_right_mono hle n).trans ?_)
      rw [← Ideal.map_pow]
      exact (Ideal.map_quotient_self J).le
    have hsq : RingHom.ker q ^ 2 = ⊥ := by
      rw [Ideal.mk_ker, ← pow_mul]
      exact eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    have hcomp : spMap π = spMap π₁ ≫ spMap q := by
      rw [hfac]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    let f : Sp (R ⧸ J) ⟶ Sp R := spMap q
    let X₁ : Over (Sp (R ⧸ J)) := Over.mk (pullback.snd X.hom f)
    have hw' : β ≫ X.hom = (X₀.hom ≫ spMap π₁) ≫ f := by
      rw [hβ.w, hcomp, Category.assoc]
    let β₀ : X₀.left ⟶ X₁.left := pullback.lift β (X₀.hom ≫ spMap π₁) hw'
    have hβ₀ : β₀ ≫ pullback.fst X.hom f = β := pullback.lift_fst _ _ _
    have hpb : IsPullback β₀ X₀.hom X₁.hom (spMap π₁) := by
      refine IsPullback.of_right (h₁₂ := pullback.fst X.hom f) (h₂₂ := f) (v₁₃ := X.hom) ?_
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback X.hom f)
      rw [hβ₀, ← hcomp]
      exact hβ
    have hX₁ : LocallyOfFiniteType X₁.hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom f))
    let L₁ : LB X₁.left := L.pull (pullback.fst X.hom f)
    have hL₁ : L₁.IsLB := LB.isLB_pull hL _
    have hw₁ : LBIso L₀ (L₁.pull β₀) :=
      LBIso.trans hL₀ (LB.isLB_pull hL β) (LB.isLB_pull hL₁ β₀) hw
        (GlobalTheory.GenSpread.lbIso_pull_pull hL β₀ hβ₀.symm)
    have hA₁ : Out.RelAmple X₁ L₁ := ih (R ⧸ J) R₀ π₁ hπ₁ hker₁ X₁ X₀ β₀ hpb hX₁ L₁ L₀ hL₁ hL₀ hw₁ hA
    exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero R (R ⧸ J) q Ideal.Quotient.mk_surjective hsq X X₁
      (pullback.fst X.hom f) (IsPullback.of_hasPullback X.hom f) hX L L₁ hL hL₁
      (lbIso_refl hL₁) hA₁

theorem relAmple_of_isNilDP : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (β : X₀.left ⟶ X.left), IsPullback β X₀.hom X.hom (spMap π) →
      LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L₀ : LB X₀.left), L.IsLB → L₀.IsLB → LBIso L₀ (L.pull β) →
      Out.RelAmple X₀ L₀ → Out.RelAmple X L := by
  intro R R₀ _ _ I κ hκ π hπ hker X X₀ β hβ hX L L₀ hL hL₀ hw hA
  obtain ⟨N, hN⟩ := exists_pow_eq_bot_of_isNilDP hκ
  exact relAmple_of_pow_eq_bot N R R₀ π hπ (hker ▸ hN) X X₀ β hβ hX L L₀ hL hL₀ hw hA

end GlobalTheory.AmpleNilThickening
