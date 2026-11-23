import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueCentreLocalHomStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartPoint

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

abbrev chartRing {κ : Type} (x : κ → Ω) (c : κ) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ (Set.range fun j => x j / x c)

theorem stalk_value (hg : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] (p : Cpt ξ) (φ : regAt ξ p →+* R)
    (z : Spec (CommRingCat.of R) ⟶ X) (hzc : centre z = p.1) (hv : ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a))
    (h : genPt ξ ⤳ centre z) (s : X.presheaf.stalk (centre z)) :
    ∃ hm : genMap ξ ⟨centre z, h⟩ s ∈ regAt ξ p,
      (Scheme.stalkClosedPointTo z).hom s = φ ⟨genMap ξ ⟨centre z, h⟩ s, hm⟩ := by
  obtain ⟨pp, hpp⟩ := p
  dsimp only at hzc
  subst hzc
  refine ⟨⟨s, rfl⟩, ?_⟩
  obtain ⟨h', s', e1, e2⟩ := hv ⟨genMap ξ ⟨centre z, h⟩ s, ⟨s, rfl⟩⟩
  have e3 : s' = s := hg.inj ⟨centre z, h⟩ e1
  subst e3
  exact e2

set_option backward.isDefEq.respectTransparency false in

theorem spec_square {F : Type} [Field F] (θ : Ω →+* F) {A : Subring F} [IsLocalRing A]
    (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z)
    (hs : ∀ s : X.presheaf.stalk (centre z),
      (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) :
    Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
  have e : A.subtype.comp (Scheme.stalkClosedPointTo z).hom = θ.comp (genMap ξ ⟨centre z, h⟩) := RingHom.ext hs
  have e1 := LieTangent.spec_centre z
  have e2 := LieTangent.spec_genMap ξ ⟨centre z, h⟩
  calc Spec.map (CommRingCat.ofHom A.subtype) ≫ z
      = Spec.map (CommRingCat.ofHom A.subtype) ≫
          (Spec.map (CommRingCat.ofHom (R := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom) ≫
            X.fromSpecStalk (centre z)) := by rw [e1]
    _ = Spec.map (CommRingCat.ofHom θ) ≫ (Spec.map (CommRingCat.ofHom (genMap ξ ⟨centre z, h⟩)) ≫
            X.fromSpecStalk (centre z)) := by
        rw [← Category.assoc, ← Category.assoc, LieTangent.spec_comp, LieTangent.spec_comp, e]
    _ = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
        exact congrArg (_ ≫ ·) e2

theorem point_of_local_subring : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ (F : Type) [Field F] (θ : Ω →+* F) (A : Subring F) [IsLocalRing A], (∀ j, θ (x j / x c) ∈ A) → ∃ (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z), InChart ξ x c ⟨centre z, h⟩ ∧ (∀ s : X.presheaf.stalk (centre z), (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
  intro X Ω _ ξ κ x c hT hc F _ θ A _ hA
  have hC : ∀ s ∈ chartRing x c, θ s ∈ A := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact hA j
    | algebraMap r =>
      have : θ (algebraMap ℤ Ω r) = (r : F) := by simp
      rw [this]
      exact intCast_mem A r
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let θC : chartRing x c →+* A :=
    (θ.comp (chartRing x c).val.toRingHom).codRestrict A (fun s => hC s s.2)
  obtain ⟨p, ⟨hpc, hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x hT c hc
    (Ideal.comap θC (IsLocalRing.maximalIdeal A)) inferInstance
  have hunit : ∀ s (hs : s ∈ chartRing x c), unitAt ξ p s ↔ IsUnit (⟨θ s, hC s hs⟩ : A) := by
    intro s hs
    rw [← hpu ⟨s, hs⟩, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    rfl
  have hreg : ∀ a ∈ regAt ξ p, θ a ∈ A := by
    intro a ha
    obtain ⟨s, hs, hsu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c p hpc a).1 ha
    obtain ⟨u, hu⟩ := (hunit s hs).1 hsu
    have h1 : (((u⁻¹ : Aˣ) : A) : F) * θ s = 1 := by
      have h2 := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at h2
      exact h2
    have h3 : θ a = (((u⁻¹ : Aˣ) : A) : F) * θ (s * a) := by
      rw [map_mul, ← mul_assoc, h1, one_mul]
    rw [h3]
    exact mul_mem ((u⁻¹ : Aˣ) : A).2 (hC _ hsa)
  let φ : regAt ξ p →+* A := (θ.comp (regAt ξ p).subtype).codRestrict A (fun a => hreg a a.2)
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨s, hs, hsu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c p hpc a).1 a.2
    have hua : IsUnit (⟨θ (s * a), hC _ hsa⟩ : A) := by
      have h1 : (⟨θ (s * a), hC _ hsa⟩ : A) = ⟨θ s, hC s hs⟩ * φ a :=
        Subtype.ext (map_mul θ s a)
      rw [h1]
      exact ((hunit s hs).1 hsu).mul ha
    obtain ⟨h0, -, hi⟩ := (hunit _ hsa).2 hua
    have hs0 : s ≠ 0 := left_ne_zero_of_mul h0
    have ha0 : (a : Ω) ≠ 0 := right_ne_zero_of_mul h0
    have hinv : (a : Ω)⁻¹ ∈ regAt ξ p := by
      have h1 : (a : Ω)⁻¹ = s * (s * a)⁻¹ := by field_simp
      rw [h1]
      exact mul_mem hsu.2.1 hi
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
  obtain ⟨z, ⟨hzc, hzv⟩, -⟩ := GlobalTheory.T.existsUnique_centre_local_hom X Ω ξ hT.gen p A φ hloc
  have h : genPt ξ ⤳ centre z := by rw [hzc]; exact p.2
  have hp : (⟨centre z, h⟩ : Cpt ξ) = p := Subtype.ext hzc
  have hs : ∀ s : X.presheaf.stalk (centre z),
      (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s) := by
    intro s
    obtain ⟨hm, e⟩ := stalk_value hT.gen p φ z hzc hzv h s
    rw [e]
    rfl
  exact ⟨z, h, by rw [hp]; exact hpc, hs, spec_square θ z h hs⟩

end GlobalTheory.CompanionTheory.Ar.ChartPoint
