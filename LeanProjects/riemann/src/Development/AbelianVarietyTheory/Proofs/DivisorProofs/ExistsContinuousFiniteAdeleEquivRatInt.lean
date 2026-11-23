import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdeleEquivOfLocal

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.AdeleZ

open Rat.HeightOneSpectrum GlobalTheory.NormLevelCompare

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem padic_ccast {p q : Nat.Primes} (h : p = q) :
    ∃ e : ℚ_[p] ≃A[ℚ] ℚ_[q], ∀ x, e x ∈ PadicInt.subring q ↔ x ∈ PadicInt.subring p := by
  subst h
  exact ⟨ContinuousAlgEquiv.refl ℚ _, fun _ => Iff.rfl⟩

theorem exists_clocal (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃A[ℚ] w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have h : primesEquiv (primeCorr w) = primesEquiv w := by simp [primeCorr]
  obtain ⟨c, hc⟩ := padic_ccast h
  refine ⟨((adicCompletion.padicEquiv (primeCorr w)).trans c).trans
    (adicCompletion.padicEquiv w).symm, fun x => ?_⟩
  rw [← padicEquiv_mem w, ← padicEquiv_mem (primeCorr w), ← hc]
  change adicCompletion.padicEquiv w ((adicCompletion.padicEquiv w).symm _) ∈ _ ↔ _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  rfl

variable (e : ∀ w : HeightOneSpectrum ℤ, (primeCorr w).adicCompletion ℚ ≃A[ℚ] w.adicCompletion ℚ)
  (he : ∀ w x, e w x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ)

theorem tendsto_primeCorr : Filter.Tendsto primeCorr Filter.cofinite Filter.cofinite :=
  primeCorr.injective.tendsto_cofinite

include he in
theorem maps_int : ∀ᶠ w in Filter.cofinite, Set.MapsTo
    (fun x => ((e w).toRingHom : (primeCorr w).adicCompletion ℚ →+* w.adicCompletion ℚ) x)
      ((primeCorr w).adicCompletionIntegers ℚ) (w.adicCompletionIntegers ℚ) :=
  .of_forall fun w x hx => (he w x).2 hx

def adeleMap : FiniteAdeleRing (𝓞 ℚ) ℚ →+* FiniteAdeleRing ℤ ℚ :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
      (fun w : HeightOneSpectrum ℤ => w.adicCompletion ℚ)
      (B₁ := fun v => v.adicCompletionIntegers ℚ) (B₂ := fun w => w.adicCompletionIntegers ℚ)
      primeCorr tendsto_primeCorr (fun w => (e w).toRingHom) (maps_int e he)

theorem continuous_adeleMap : Continuous (adeleMap e he) :=
  RestrictedProduct.mapAlong_continuous _ _ primeCorr tendsto_primeCorr _ (maps_int e he)
    fun w => (e w).continuous

def adeleAlgHom : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] FiniteAdeleRing ℤ ℚ where
  toFun a := ⟨fun w => e w (a (primeCorr w)), by
    have h1 := primeCorr.injective.tendsto_cofinite.eventually a.2
    exact h1.mono fun w hw => (he w _).2 hw⟩
  map_one' := FiniteAdeleRing.ext _ fun w => map_one (e w)
  map_mul' := fun a b => FiniteAdeleRing.ext _ fun w => map_mul (e w) _ _
  map_zero' := FiniteAdeleRing.ext _ fun w => map_zero (e w)
  map_add' := fun a b => FiniteAdeleRing.ext _ fun w => map_add (e w) _ _
  commutes' := fun r => FiniteAdeleRing.ext _ fun w => (e w).commutes r

theorem adeleAlgHom_apply (a : FiniteAdeleRing (𝓞 ℚ) ℚ) (w : HeightOneSpectrum ℤ) :
    adeleAlgHom e he a w = e w (a (primeCorr w)) := rfl

theorem adeleAlgHom_eq : ⇑(adeleAlgHom e he) = ⇑(adeleMap e he) := by
  funext a
  exact FiniteAdeleRing.ext _ fun w => rfl

theorem adeleAlgHom_injective : Function.Injective (adeleAlgHom e he) := by
  intro a b hab
  refine FiniteAdeleRing.ext _ fun v => ?_
  obtain ⟨w, rfl⟩ := primeCorr.surjective v
  have h := congrArg (fun x : FiniteAdeleRing ℤ ℚ => x w) hab
  simp only [adeleAlgHom_apply] at h
  exact (e w).injective h

theorem adeleAlgHom_surjective : Function.Surjective (adeleAlgHom e he) := by
  intro b
  obtain ⟨f, hf⟩ : ∃ f : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletion ℚ,
      ∀ w, f (primeCorr w) = (e w).symm (b w) :=
    ⟨_, fun w => Equiv.piCongrLeft_apply_apply
      (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ) primeCorr
      (fun w => (e w).symm (b w)) w⟩
  have hfi : ∀ᶠ v in Filter.cofinite, f v ∈ v.adicCompletionIntegers ℚ := by
    have h1 := primeCorr.symm.injective.tendsto_cofinite.eventually b.2
    refine h1.mono fun v hv => ?_
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    rw [Equiv.symm_apply_apply] at hv
    rw [hf, ← he, ContinuousAlgEquiv.apply_symm_apply]
    exact hv
  obtain ⟨a, ha⟩ : ∃ a : FiniteAdeleRing (𝓞 ℚ) ℚ, ∀ v, a v = f v := ⟨⟨f, hfi⟩, fun _ => rfl⟩
  refine ⟨a, FiniteAdeleRing.ext _ fun w => ?_⟩
  rw [adeleAlgHom_apply, ha, hf, ContinuousAlgEquiv.apply_symm_apply]

omit e he in

theorem exists_continuous_adele_equiv :
    ∃ e : FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] FiniteAdeleRing ℤ ℚ, Continuous e := by
  choose e he using exists_clocal
  refine ⟨AlgEquiv.ofBijective (adeleAlgHom e he)
    ⟨adeleAlgHom_injective e he, adeleAlgHom_surjective e he⟩, ?_⟩
  change Continuous (adeleAlgHom e he)
  rw [adeleAlgHom_eq]
  exact continuous_adeleMap e he

end GlobalTheory.AdeleZ
