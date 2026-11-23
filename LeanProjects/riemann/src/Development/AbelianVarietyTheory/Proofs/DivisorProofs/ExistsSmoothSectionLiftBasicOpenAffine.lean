import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.SmLift
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem awayMap_surjective_of_surjective (π : R →+* R₀) (hπ : Function.Surjective π) (f : R) :
    Function.Surjective (Localization.awayMap π f) :=
  Localization.awayMap_surjective_iff.2 fun a =>
    (hπ a).elim fun b hb => ⟨b, 0, by simp [hb]⟩

theorem isNilpotent_of_awayMap_eq_zero (π : R →+* R₀) (hnil : IsNilpotent (RingHom.ker π)) (f : R)
    (x : Localization.Away f) (hx : Localization.awayMap π f x = 0) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) x
  have hc : (Localization.awayMap π f).comp (algebraMap R (Localization.Away f)) =
      (algebraMap R₀ (Localization.Away (π f))).comp π := IsLocalization.map_comp _
  have h1 : algebraMap R₀ (Localization.Away (π f)) (π a) = 0 := by
    have := congrArg (Localization.awayMap π f) hs
    rw [map_mul, hx, zero_mul] at this
    rw [← RingHom.comp_apply, ← hc, RingHom.comp_apply, ← this]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (π f)) _ _).1 h1
  have hmem : f ^ k * a ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_mul, map_pow]; exact hk
  have h0 : (f ^ k * a) ^ N = 0 := by
    have := Ideal.pow_mem_pow hmem N
    rw [hN] at this
    exact Ideal.mem_bot.1 this
  have hu : IsUnit (algebraMap R (Localization.Away f) (s * f ^ k)) := by
    rw [map_mul, map_pow]
    exact (IsLocalization.map_units _ s).mul ((IsLocalization.Away.algebraMap_isUnit f).pow k)
  refine ⟨N, (hu.pow N).mul_left_eq_zero.1 ?_⟩
  rw [← mul_pow, map_mul, ← mul_assoc, hs, ← map_mul, mul_comm a, ← map_pow, h0, map_zero]

theorem exists_liftIn_unfolded : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀ ∧
    e ⁻¹ᵁ V = ⊤ := by
  intro R R₀ _ _ π hπ hnil X hX g₀ hg p
  haveI := hX
  have hker : RingHom.ker π ≤ p.asIdeal := fun a ha => by
    obtain ⟨N, hN⟩ := hnil
    have := Ideal.pow_mem_pow ha N
    rw [hN] at this
    exact p.isPrime.mem_of_pow_mem N ((Ideal.mem_bot.1 this) ▸ p.asIdeal.zero_mem)
  obtain ⟨p₀, hp₀⟩ : p ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [_root_.range_comap_of_surjective (R := R) R₀ π hπ]
    exact hker
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g₀ p₀)) isOpen_univ
  obtain ⟨_, ⟨r, rfl⟩, hp₀r, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p₀) (u := {q : PrimeSpectrum R₀ | g₀ q ∈ V}) hxV (g₀ ⁻¹ᵁ V).isOpen
  obtain ⟨f, rfl⟩ := hπ r
  refine ⟨f, ?_, V, hV, ?_⟩
  · rw [← hp₀]
    exact hp₀r
  have hsurj := awayMap_surjective_of_surjective π hπ f
  have hnilL := isNilpotent_of_awayMap_eq_zero π hnil f
  have hc : (Localization.awayMap π f).comp (algebraMap R (Localization.Away f)) =
      (algebraMap R₀ (Localization.Away (π f))).comp π := IsLocalization.map_comp _
  have hx0 : Set.range (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀) ⊆ V := by
    rintro _ ⟨q, rfl⟩
    apply hsub
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away (π f)) (π f)).subset ⟨q, rfl⟩
  obtain ⟨x, h₁, h₂⟩ := GlobalTheory.exists_lift_of_smooth_of_isAffineOpen X.hom (isAffineOpen_top (Sp R)) hV
    (fun _ _ => trivial) (CommRingCat.ofHom (Localization.awayMap π f))
    (spMap (algebraMap R (Localization.Away f))) (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀)
    (by
      rw [Category.assoc, hg, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      exact (congrArg (fun φ : R →+* Localization.Away (π f) => φ a) hc).symm)
    (fun _ _ => trivial) hx0 (by
      intro R' A _ _ _ _ _ _ π' hπ' φ
      exact ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.exists_lift_nil π'
        (fun c => (hsurj c).imp fun b hb => (hπ' b).trans hb)
        (fun a ha => hnilL a (by rw [RingHom.mem_ker] at ha; rw [← ha]; exact (hπ' a).symm)) φ)
  refine ⟨x, h₂, h₁, top_unique fun q _ => ?_⟩
  obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (Localization.awayMap π f)) := by
    rw [_root_.range_comap_of_surjective (R := Localization.Away f) _ _ hsurj]
    intro a ha
    obtain ⟨n, hn⟩ := hnilL a ha
    exact (q : PrimeSpectrum (Localization.Away f)).isPrime.mem_of_pow_mem n (hn ▸ q.asIdeal.zero_mem)
  show x q ∈ V
  have : x q = (spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀) q' := by
    rw [← h₁]
    exact congrArg x hq'.symm
  rw [this]
  exact hx0 ⟨q', rfl⟩

theorem exists_liftIn : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ GlobalTheory.SecLift.LiftIn π X g₀ f V :=
  exists_liftIn_unfolded

end GlobalTheory.SecLift
