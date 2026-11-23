import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

theorem ne_zero_of_ord_pos {K : Type} [Field K] [Algebra ℂ K] (E : Place (algebraMap ℂ K)) {e : K}
    (he : 0 < E.ord e) : e ≠ 0 := by
  rintro rfl
  simp [Place.ord] at he

theorem graphIdeal_ne_top_of_hom {K κ κ' F : Type} [Field K] [Field κ] [Field κ'] [Field F]
    [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (h1 : ∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a)
    (h2 : ∀ a, algebraMap ℂ K a ∈ R) (h4 : E.Contains R)
    (α : E.ring →+* F) (β : κ' →+* F) (hα : ∀ r : R, α ⟨r, h4 _ r.2⟩ = β (ρ (π r)))
    (hpos : ∀ x : E.ring, 0 < E.ord (x : K) → α x = 0) :
    graphIdeal (κ' := κ') E R π ρ ≠ ⊤ := by
  letI : Algebra ℂ F := (β.comp (algebraMap ℂ κ')).toAlgebra
  let j : placeAlg E →+* E.ring :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let α' : placeAlg E →ₐ[ℂ] F :=
    { α.comp j with
      commutes' := fun a => by
        have := hα ⟨algebraMap ℂ K a, h2 a⟩
        rw [h1, ρ.commutes] at this
        exact this }
  let β' : κ' →ₐ[ℂ] F := { β with commutes' := fun _ => rfl }
  let Φ := Algebra.TensorProduct.lift α' β' (fun _ _ => Commute.all _ _)
  let Ψ : tens (κ' := κ') (placeAlg E) →+* F :=
    (Φ.comp (tensEquiv (κ' := κ') (placeAlg E)).symm.toAlgHom).toRingHom
  have hΨ : ∀ w, Ψ (tensEquiv (placeAlg E) w) = Φ w := fun w => by
    simp [Ψ]
  intro htop
  have hle : graphIdeal (κ' := κ') E R π ρ ≤ RingHom.ker Ψ := by
    rw [graphIdeal, Ideal.span_le]
    rintro b (⟨e, he, hb⟩ | ⟨a, hb⟩)
    · have hmem : e ∈ E.ring := (E.ord_nonneg_iff (ne_zero_of_ord_pos E he)).1 he.le
      have hb' : b = tensEquiv (κ' := κ') (placeAlg E) (⟨e, hmem⟩ ⊗ₜ 1) :=
        Subtype.ext (by rw [hb]; rfl)
      rw [SetLike.mem_coe, RingHom.mem_ker, hb', hΨ]
      simp only [Φ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact hpos ⟨e, hmem⟩ he
    · have hb' : b = tensEquiv (κ' := κ') (placeAlg E)
          (⟨a, h4 _ a.2⟩ ⊗ₜ 1 - 1 ⊗ₜ ρ (π a)) :=
        Subtype.ext (by rw [hb, coe_tensEquiv, map_sub]; rfl)
      rw [SetLike.mem_coe, RingHom.mem_ker, hb', hΨ]
      simp only [Φ, map_sub, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul]
      rw [sub_eq_zero]
      exact hα a
  have h1mem : (1 : tens (κ' := κ') (placeAlg E)) ∈ graphIdeal (κ' := κ') E R π ρ :=
    htop ▸ Submodule.mem_top
  exact one_ne_zero ((RingHom.mem_ker).1 (hle h1mem) |>.symm.trans (map_one Ψ)).symm

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

theorem graphIdeal_ne_top : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K)),
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  graphIdeal (κ' := κ') E R π ρ ≠ ⊤ := by
  intro K κ κ' _ _ _ _ _ _ R π ρ E h1 h2 h3 h4 h5
  let kE := IsLocalRing.ResidueField E.ring
  let inc : R →+* E.ring := R.subtype.codRestrict E.ring (fun r => h4 _ r.2)
  let g : R →+* kE := (IsLocalRing.residue E.ring).comp inc
  have hnu : ∀ x : E.ring, (x : K) ≠ 0 →
      (0 < E.ord x ↔ x ∈ IsLocalRing.maximalIdeal E.ring) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hpos hu
      have := E.ord_eq_zero hu
      omega
    · intro hnu'
      have h0 : 0 ≤ E.ord x := (E.ord_nonneg_iff hx).2 x.2
      rcases h0.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hnu'
        have hinv : (x : K)⁻¹ ∈ E.ring :=
          (E.ord_nonneg_iff (inv_ne_zero hx)).1 (by rw [E.ord_inv, ← h]; simp)
        exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hx))
  have hker : ∀ r : R, π r = 0 ↔ g r = 0 := by
    intro r
    by_cases hr : (r : K) = 0
    · have : r = 0 := Subtype.ext hr
      subst this
      simp
    · rw [h5 r hr, show g r = IsLocalRing.residue E.ring (inc r) from rfl,
        IsLocalRing.residue_eq_zero_iff]
      exact hnu (inc r) hr
  have hsurj : Function.Surjective π.rangeRestrict := π.rangeRestrict_surjective
  let φ₀ : π.range →+* kE := π.rangeRestrict.liftOfSurjective hsurj
    ⟨g, fun r hr => by
      rw [RingHom.mem_ker] at hr ⊢
      exact (hker r).1 (congrArg Subtype.val hr)⟩
  have hφ₀ : ∀ r, φ₀ (π.rangeRestrict r) = g r := fun r =>
    RingHom.liftOfSurjective_comp_apply _ hsurj _ r
  have hinj : Function.Injective φ₀ := (injective_iff_map_eq_zero φ₀).2 fun s hs => by
    obtain ⟨r, rfl⟩ := hsurj s
    rw [hφ₀] at hs
    exact Subtype.ext ((hker r).2 hs)
  haveI : IsFractionRing π.range κ := IsFractionRing.of_field π.range κ fun z => by
    obtain ⟨a, b, hb, e⟩ := h3 z
    refine ⟨π.rangeRestrict a, π.rangeRestrict b, ?_⟩
    show z = π a / π b
    rw [eq_div_iff hb, e]
  let ι : κ →+* kE := IsFractionRing.lift hinj
  have hι : ∀ r, ι (π r) = g r := fun r => by
    rw [← hφ₀]
    exact IsFractionRing.lift_algebraMap hinj (π.rangeRestrict r)
  letI : Algebra κ kE := ι.toAlgebra
  letI : Algebra κ κ' := ρ.toRingHom.toAlgebra
  haveI : Nontrivial (kE ⊗[κ] κ') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain κ kE κ'
      ι.injective ρ.toRingHom.injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (kE ⊗[κ] κ')
  letI : Field (kE ⊗[κ] κ' ⧸ M) := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  let α : E.ring →+* (kE ⊗[κ] κ' ⧸ M) :=
    q.comp (Algebra.TensorProduct.includeLeftRingHom.comp (IsLocalRing.residue E.ring))
  let β : κ' →+* (kE ⊗[κ] κ' ⧸ M) :=
    q.comp (Algebra.TensorProduct.includeRight (R := κ) (A := kE)).toRingHom
  refine graphIdeal_ne_top_of_hom R π ρ E h1 h2 h4 α β (fun r => ?_) (fun x hx => ?_)
  · show q (IsLocalRing.residue E.ring (inc r) ⊗ₜ 1) = q (1 ⊗ₜ ρ (π r))
    congr 1
    rw [show IsLocalRing.residue E.ring (inc r) = g r from rfl, ← hι,
      show ι (π r) = π r • (1 : kE) by rw [Algebra.smul_def, mul_one]; rfl,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  · show q (IsLocalRing.residue E.ring x ⊗ₜ 1) = 0
    rw [(IsLocalRing.residue_eq_zero_iff x).2 ((hnu x (ne_zero_of_ord_pos E hx)).1 hx),
      TensorProduct.zero_tmul, map_zero]

end GlobalTheory.GraphLocal
