import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqMulOfContinuousOnQuotient
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory

open AffinePoints in

theorem exists_eq_of_continuous_quotient_algHom {A : Type} [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [IsIntegrallyClosed A] {ψ : (A →ₐ[ℂ] ℂ) → ℂ} (hψ : Continuous ψ)
    {a b : A} (hb : b ≠ 0) (hab : ∀ e : A →ₐ[ℂ] ℂ, e b * ψ e = e a) :
    ∃ c : A, ∀ e : A →ₐ[ℂ] ℂ, e c = ψ e := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have key (s r : A) (h : b * s = a * r) (e : A →ₐ[ℂ] ℂ) : e s = ψ e * e r := by
    refine congrFun (Continuous.ext_on (dense_nonvanishing hb) (continuous_eval s)
      (hψ.mul (continuous_eval r)) fun w hw => mul_left_cancel₀ hw ?_) e
    have h1 := congrArg w h
    rw [map_mul, map_mul, ← hab w] at h1
    exact h1.trans (_root_.mul_assoc _ _ _)
  by_cases H : b ∣ a
  · obtain ⟨c, hc⟩ := H
    exact ⟨c, fun e => by rw [key c 1 (by rw [hc, _root_.mul_one]) e, map_one, _root_.mul_one]⟩
  obtain ⟨p, hp, s, r, hs, hr, h⟩ := ContinuousQuotient.exists_prime_of_not_dvd hb H
  have h0 : Ideal.Quotient.mkₐ ℂ p s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨e, he⟩ := not_forall.mp fun h => h0 (eq_zero_of_forall_algHom_complex _ h)
  refine (he ((key s r h (e.comp (Ideal.Quotient.mkₐ ℂ p))).trans ?_)).elim
  change _ * e (Ideal.Quotient.mk p r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, mul_zero]

theorem isIntegrallyClosed_sections_of_isDomain {Y : Scheme.{0}}
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(Y, U)] : IsIntegrallyClosed Γ(Y, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hp ↦ ?_
  let P : Spec Γ(Y, U) := ⟨p, hp.isPrime⟩
  have hy : hU.fromSpec P ∈ U := hU.range_fromSpec.le ⟨P, rfl⟩
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk (hU.fromSpec P)) :=
    Y.presheaf.algebra_section_stalk (U := U) ⟨_, hy⟩
  have h : IsLocalization p.primeCompl (Y.presheaf.stalk (hU.fromSpec P)) :=
    hU.isLocalization_stalk' P hy
  have := hY (hU.fromSpec P)
  exact IsIntegrallyClosed.of_equiv (R := Y.presheaf.stalk (hU.fromSpec P))
    (IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk (hU.fromSpec P))
      (Localization.AtPrime p)).toRingEquiv

open AffinePoints in

theorem exists_ev_eq_of_continuousOn_quotient :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ (V : Y.Opens), IsAffineOpen V → IsDomain Γ(Y, V) → ∀ φ : CxPts p (RingHom.id ℂ) → ℂ, ContinuousOn φ (ptsIn p (RingHom.id ℂ) V) → ∀ a b : Γ(Y, V), b ≠ 0 → (∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V b y * φ y = ev p (RingHom.id ℂ) V a y) → ∃ c : Γ(Y, V), ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V c y = φ y := by
  intro Y p D hp U hU hdom φ hφ a b hb hab
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hN := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hsm).2.1
  have := isIntegrallyClosed_sections_of_isDomain (fun y => (hN y).2) hU
  have hc : (algX p U).FiniteType := by
    have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  let : Algebra ℂ Γ(Y, U) := (algX p U).toAlgebra
  have : Algebra.FiniteType ℂ Γ(Y, U) := hc
  let s (e : Γ(Y, U) →ₐ[ℂ] ℂ) : CxPts p (RingHom.id ℂ) := ofHom hU e.toRingHom fun c => e.commutes c
  have hm (e) : s e ∈ ptsIn p (RingHom.id ℂ) U := ofHom_mem _ _ _
  have hv (e) (f) : ev p (RingHom.id ℂ) U f (s e) = e f := ev_ofHom _ _ _ _
  have hs : Continuous s := continuous_iff_continuousAt.2 fun e => tendsto_subtype_rng.2
    (Points.tendsto_of_isAffineOpen hU (hm e) (Filter.Eventually.of_forall hm) fun f => by
      have h : Continuous fun w => ev p (RingHom.id ℂ) U f (s w) := by
        simp only [hv]; exact continuous_eval f
      exact h.continuousAt)
  obtain ⟨c, hc⟩ := exists_eq_of_continuous_quotient_algHom (hφ.comp_continuous hs hm) (a := a) hb
    fun e => by rw [← hv, ← hv]; exact hab _ (hm e)
  refine ⟨c, fun y hy => ?_⟩
  let e : Γ(Y, U) →ₐ[ℂ] ℂ :=
    { evHom hy with commutes' := fun t => (ev_eq hy _).symm.trans (ev_algX hy t) }
  have he : s e = y := Subtype.ext (Points.ext_of_valR hU (hm e) hy fun f =>
    (hv e f).trans (ev_eq hy f).symm)
  rw [← he, hv]
  exact hc e

end GlobalTheory
