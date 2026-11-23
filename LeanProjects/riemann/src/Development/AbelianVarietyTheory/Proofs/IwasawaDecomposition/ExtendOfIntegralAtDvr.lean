import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfForallMemDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.GenExt
open GlobalTheory.FlagMod

theorem generic_le {X : Scheme.{0}} {G W : X.Opens} (hG : IsAffineOpen G) [IsDomain Γ(X, G)]
    (hW : W ≤ G) (hne : ∃ x, x ∈ W) :
    ⊤ ≤ (spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G))) ≫ tau hG) ⁻¹ᵁ W := by
  intro y _
  obtain ⟨x, hx⟩ := hne
  obtain ⟨q, hq⟩ := hG.range_fromSpec.ge (hW hx)
  have hq' : q ∈ (tau hG ⁻¹ᵁ W : (Sp Γ(X, G)).Opens) := by
    show hG.fromSpec q ∈ W
    rw [hq]; exact hx
  have hsp : (spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G)))) y ⤳ q := by
    refine (PrimeSpectrum.le_iff_specializes (R := Γ(X, G)) ((spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G)))) y) q).1 ?_
    show Ideal.comap _ y.asIdeal ≤ q.asIdeal
    rw [@Ideal.eq_bot_of_prime _ _ y.asIdeal y.2]
    exact Ideal.comap_bot_le_of_injective _ (IsFractionRing.injective Γ(X, G) (FractionRing Γ(X, G)))
  exact hsp.mem_open (tau hG ⁻¹ᵁ W).isOpen hq'

theorem extend_of_integral_at_dvr : ∀ (X : Scheme.{0}) (G W₀ : X.Opens) (hle : W₀ ≤ G), IsAffineOpen G → IsDomain Γ(X, G) → IsNoetherianRing Γ(X, G) → IsIntegrallyClosed Γ(X, G) → Countable Γ(X, G) → (∃ x, x ∈ W₀) → Function.Injective (resG X hle) ∧ ∀ f₀ : Γ(X, W₀), (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ X), Countable R → ⊤ ≤ z ⁻¹ᵁ G → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range) → ∃ f : Γ(X, G), resG X hle f = f₀ := by
  intro X G W₀ hle hG hD hN hI hC hne
  let K := FractionRing Γ(X, G)
  let η : Sp K ⟶ X := spMap (algebraMap Γ(X, G) K) ≫ tau hG
  have hηG : ⊤ ≤ η ⁻¹ᵁ G := le_preimage_comp _ (tau_le hG le_rfl)
  have key : ∀ (W : X.Opens) (hW : W ≤ G) (h : ⊤ ≤ η ⁻¹ᵁ W) (a : Γ(X, G)),
      ev η W h (resG X hW a) = algebraMap Γ(X, G) K a := by
    intro W hW h a
    rw [ev_res η hW h hηG, ev_spMap_tau hG]
  have hW₀ : ⊤ ≤ η ⁻¹ᵁ W₀ := generic_le hG hle hne
  refine ⟨fun a b e => IsFractionRing.injective Γ(X, G) K (by rw [← key W₀ hle hW₀, ← key W₀ hle hW₀, e]), ?_⟩
  intro f₀ hf
  have hKc : Countable K := by
    have hs : Function.Surjective (fun p : Γ(X, G) × nonZeroDivisors Γ(X, G) => IsLocalization.mk' K p.1 p.2) :=
      fun x => by
        obtain ⟨p, e⟩ := IsLocalization.mk'_surjective (nonZeroDivisors Γ(X, G)) x
        exact ⟨p, e⟩
    exact hs.countable
  have hint : _root_.IsIntegral Γ(X, G) (ev η W₀ hW₀ f₀) := by
    apply GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring Γ(X, G) K
    intro V hV hBV
    let ι : Γ(X, G) →+* V := (algebraMap Γ(X, G) K).codRestrict V.toSubring hBV
    have hz : ⊤ ≤ (spMap ι ≫ tau hG) ⁻¹ᵁ G := le_preimage_comp _ (tau_le hG le_rfl)
    have hc : (algebraMap V K).comp ι = algebraMap Γ(X, G) K := RingHom.ext fun _ => rfl
    have he : spMap (algebraMap V K) ≫ spMap ι ≫ tau hG = η := by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
    have h' : ⊤ ≤ (spMap (algebraMap V K) ≫ spMap ι ≫ tau hG) ⁻¹ᵁ W₀ := by rw [he]; exact hW₀
    obtain ⟨v, hv⟩ := hf V K (spMap ι ≫ tau hG) inferInstance hz h'
    rw [ev_congr he W₀ h' hW₀] at hv
    rw [← hv]
    exact v.2
  obtain ⟨f, hf'⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).1 hint
  refine ⟨f, ext_ev_loc fun p hp => ?_⟩
  obtain ⟨s, hsle, hps⟩ := hG.exists_basicOpen_le ⟨p, hp⟩ (hle hp)
  have hN : ⊤ ≤ η ⁻¹ᵁ X.basicOpen s := generic_le hG (X.basicOpen_le s) ⟨p, hps⟩
  have inj : Function.Injective (ev η (X.basicOpen s) hN) := by
    haveI := hG.isLocalization_basicOpen s
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, m⟩, e⟩ := IsLocalization.surj (Submonoid.powers s) x
    have h1 : algebraMap Γ(X, G) K a = 0 := by
      rw [← key _ (X.basicOpen_le s) hN a]
      change ev η _ hN (algebraMap Γ(X, G) Γ(X, X.basicOpen s) a) = 0
      rw [← e, map_mul, hx, zero_mul]
    have ha : a = 0 := IsFractionRing.injective Γ(X, G) K (by rw [h1, map_zero])
    have hu : IsUnit (algebraMap Γ(X, G) Γ(X, X.basicOpen s) m) := IsLocalization.map_units _ m
    rw [ha, map_zero] at e
    exact hu.mul_left_eq_zero.1 e
  have hres : resG X hsle (resG X hle f) = resG X hsle f₀ := by
    apply inj
    rw [ev_res η hsle hN hW₀, ev_res η hsle hN hW₀, key W₀ hle hW₀, hf']
  refine ⟨X.basicOpen s, hps, fun S _ z hz hzN => ?_⟩
  rw [← ev_res z hsle hzN hz, ← ev_res z hsle hzN hz (f₀), hres]

end GlobalTheory.GenExt
