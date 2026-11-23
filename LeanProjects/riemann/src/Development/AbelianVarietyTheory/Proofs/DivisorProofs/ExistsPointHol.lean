import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.TangentOrigin

namespace GlobalTheory.AnPer

theorem exists_point_hol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens E)
    (X : Scheme.{0}) (e : E → (Sp ℂ ⟶ X)) (U : X.Opens), IsAffineOpen U → IsHolTo (W : Set E) e → (∀ p ∈ W, ⊤ ≤ e p ⁻¹ᵁ U) →
    ∃ x : Sp (Hol W) ⟶ X, ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x = e p := by
  intro E _ _ _ W X e U hU he hW
  have ha : ∀ f : Γ(X, U), AnalyticOnNhd ℂ (fun p => valAt' (e p) U f) W := fun f p hp =>
    SCV.analyticAt_of_differentiableOn (he U f).2 ((he U f).1.mem_nhds ⟨hp, hW p hp⟩)
  have hv : ∀ (f : Γ(X, U)) (p : E) (hp : p ∈ W), (Hol.mk _ (ha f)).fn p = evalPt (e p) U (hW p hp) f :=
    fun f p hp => (Hol.fn_mk _ _ hp).trans (valAt'_eq_evalPt _ _ _ _)
  let ψ : Γ(X, U) →+* Hol W :=
    { toFun := fun f => Hol.mk _ (ha f)
      map_one' := Hol.ext_fn fun p hp => by rw [hv _ p hp, map_one, ← Hol.ev_apply p hp, map_one]
      map_mul' := fun f g => Hol.ext_fn fun p hp => by rw [Hol.fn_mul _ _ hp, hv _ p hp, hv _ p hp, hv _ p hp, map_mul]
      map_zero' := Hol.ext_fn fun p hp => by rw [hv _ p hp, map_zero, ← Hol.ev_apply p hp, map_zero]
      map_add' := fun f g => Hol.ext_fn fun p hp => by rw [Hol.fn_add _ _ hp, hv _ p hp, hv _ p hp, hv _ p hp, map_add] }
  obtain ⟨x, hx, hxψ⟩ := exists_evalPt_eq hU ψ
  have h' : ∀ (p : E) (hp : p ∈ W), ⊤ ≤ (spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x) ⁻¹ᵁ U := fun p hp q _ => hx trivial
  refine ⟨x, hx, fun p hp => ext_evalPt hU (h' p hp) (hW p hp) (RingHom.ext fun f => ?_)⟩
  rw [evalPt_spMap_comp _ x U hx, hxψ]
  exact (Hol.ev_apply p hp _).trans (hv f p hp)

theorem point_hol_ext : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E)
    (X S : Scheme.{0}) (s : X ⟶ S) [IsSeparated s] (x x' : Sp (Hol W) ⟶ X), x ≫ s = x' ≫ s →
    (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x = spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x') → x = x' := by
  intro E _ _ W X S s _ x x' hs h
  have : _root_.IsReduced (Hol W) := isReduced_of_injective (holSub W).val Subtype.val_injective
  suffices IsDominant (equalizer.ι x x') from
    ext_of_isDominant_of_isSeparated s hs (equalizer.ι x x') (equalizer.condition _ _)
  refine ⟨?_⟩
  have hd : Dense (Set.range fun p : W => PrimeSpectrum.comap (Hol.ev p.1 p.2 : Hol W →+* ℂ) default) := by
    rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro f hf
    have : f = 0 := Hol.ext_fn fun p hp => by
      have h1 := (PrimeSpectrum.mem_vanishingIdeal _ _).1 hf _ ⟨⟨p, hp⟩, rfl⟩
      have h2 : Hol.ev p hp f ∈ (default : PrimeSpectrum ℂ).asIdeal := h1
      rw [Ideal.eq_bot_of_prime (default : PrimeSpectrum ℂ).asIdeal, Ideal.mem_bot] at h2
      rw [← Hol.ev_apply p hp, ← Hol.ev_apply p hp, h2, map_zero]
    rw [this]
    exact zero_mem _
  refine Dense.mono ?_ hd
  rintro _ ⟨p, rfl⟩
  refine ⟨equalizer.lift _ (h p.1 p.2) (default : PrimeSpectrum ℂ), ?_⟩
  exact congrArg (fun m : Sp ℂ ⟶ Sp (Hol W) => m (default : PrimeSpectrum ℂ)) (equalizer.lift_ι _ (h p.1 p.2))

end GlobalTheory.AnPer
