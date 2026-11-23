import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitCokernelCoforkBiprodMap
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem shortExact_pullback_cokernel_of_shortExact {C : Type*} [Category C] [Abelian C]
    {A E₂ E₃ F F' : C} (b : E₂ ⟶ E₃) [Epi b] (ιF : F ⟶ E₃)
    (ι' : F' ⟶ E₃) [Mono ι'] (s : F ⟶ F') (hs : s ≫ ι' = ιF) (f : A ⟶ E₂)
    (hz : f ≫ b ≫ cokernel.π ιF = 0) (hS : (ShortComplex.mk f (b ≫ cokernel.π ιF) hz).ShortExact)
    (t : A ⟶ pullback b ι') (τ : A ⟶ F) (ht1 : t ≫ pullback.fst b ι' = f)
    (ht2 : t ≫ pullback.snd b ι' = τ ≫ s) :
    ∃ hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0,
      (ShortComplex.mk t (pullback.snd b ι' ≫ cokernel.π s) hz').ShortExact := by
  have hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0 := by
    rw [← Category.assoc, ht2, Category.assoc, cokernel.condition, comp_zero]
  refine ⟨hz', ?_⟩
  have hmf : Mono f := hS.mono_f
  have hmt : Mono t := by
    subst ht1
    exact mono_of_mono t (pullback.fst b ι')
  have hsnd : Epi (pullback.snd b ι') := Abelian.epi_pullback_of_epi_f b ι'
  refine ShortComplex.ShortExact.mk' ?_ hmt (epi_comp _ _)
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  simp only at x hx
  have hc := (ShortComplex.exact_cokernel s)
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hc
  obtain ⟨T₁, π₁, hπ₁, y, hy⟩ := hc (x ≫ pullback.snd b ι') (by simpa using hx)
  simp only at hy
  have hex := hS.exact
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hex
  have hb : (π₁ ≫ x ≫ pullback.fst b ι') ≫ b ≫ cokernel.π ιF = 0 := by
    have : π₁ ≫ x ≫ pullback.fst b ι' ≫ b = y ≫ ιF := by
      rw [pullback.condition, ← Category.assoc, ← Category.assoc, ← hs,
        Category.assoc π₁, hy, Category.assoc]
    have h2 := this =≫ cokernel.π ιF
    simp only [Category.assoc] at h2 ⊢
    rw [h2, cokernel.condition, comp_zero]
  obtain ⟨T₂, π₂, hπ₂, z, hz2⟩ := hex (π₁ ≫ x ≫ pullback.fst b ι') hb
  simp only at hz2
  refine ⟨T₂, π₂ ≫ π₁, epi_comp _ _, z, ?_⟩
  simp only
  apply (cancel_mono (pullback.fst b ι')).1
  simp only [Category.assoc, ht1]
  simpa [Category.assoc] using hz2

end GlobalTheory

open GlobalTheory in
theorem GlobalTheory.shortExact_pullback_cokernel_modules : ∀ (X : Scheme.{0}) {A E₂ E₃ F F' : X.Modules} (b : E₂ ⟶ E₃) [Epi b] (ιF : F ⟶ E₃)
    (ι' : F' ⟶ E₃) [Mono ι'] (s : F ⟶ F'), s ≫ ι' = ιF → ∀ (f : A ⟶ E₂)
    (hz : f ≫ b ≫ cokernel.π ιF = 0), (ShortComplex.mk f (b ≫ cokernel.π ιF) hz).ShortExact →
    ∀ (t : A ⟶ pullback b ι') (τ : A ⟶ F), t ≫ pullback.fst b ι' = f →
    t ≫ pullback.snd b ι' = τ ≫ s → ∃ hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0,
      (ShortComplex.mk t (pullback.snd b ι' ≫ cokernel.π s) hz').ShortExact := by
  intro X A E₂ E₃ F F' b _ ιF ι' _ s hs f hz hS t τ ht1 ht2
  exact shortExact_pullback_cokernel_of_shortExact b ιF ι' s hs f hz hS t τ ht1 ht2
