import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedAdelicMetricIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedOfPositiveNorms
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.ModelLiftConj

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

theorem ringOfIntegers_hom_injective (F : Type) [Field F] [NumberField F] (σ : 𝓞 F →+* ℂ) :
    Function.Injective σ := by
  rw [injective_iff_map_eq_zero]
  have hk : (RingHom.ker σ).comap (algebraMap ℤ (𝓞 F)) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker] at hn
    simp only [algebraMap_int_eq, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  have := Ideal.eq_bot_of_comap_eq_bot hk
  intro x hx
  have : x ∈ RingHom.ker σ := hx
  simpa [*] using this

theorem exists_extend_ringOfIntegers (F : Type) [Field F] [NumberField F] (σ : 𝓞 F →+* ℂ) :
    ∃ σF : F →+* ℂ, σF.comp (algebraMap (𝓞 F) F) = σ :=
  ⟨IsFractionRing.lift (ringOfIntegers_hom_injective F σ), by
    ext x; simp [IsFractionRing.lift_algebraMap]⟩

theorem model_weight_isConj_of_lift : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (G : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (w : ∀ σ : 𝓞 F →+* ℂ, CxPts M.p σ → ℝ), (∀ (σ : F →+* ℂ) (y : Pts Y σ) (y' : CxPts M.p (σ.comp (algebraMap (𝓞 F) F))), y'.1 = y.1 ≫ M.j → w _ y' = G σ y) → (∀ (σ σ' : F →+* ℂ) (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → G σ' y' = G σ y) → ∀ σ σ' : 𝓞 F →+* ℂ, (Weight.ofFun (w σ)).IsConj (Weight.ofFun (w σ')) := by
  intro F _ _ Y M G w h1 h2 σ σ' i y y' hy' _
  show w σ' y' = w σ y
  obtain ⟨σF, rfl⟩ := exists_extend_ringOfIntegers F σ
  have hsq : y.1 ≫ M.p = spMap σF ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [y.2, spMap_comp']
  let yh : Pts Y σF := ⟨M.pb.lift y.1 (spMap σF) hsq, M.pb.lift_snd _ _ _⟩
  have hyh : y.1 = yh.1 ≫ M.j := (M.pb.lift_fst _ _ _).symm
  have e1 : w _ y = G σF yh := h1 σF yh y hyh
  have hσ' : σ' = ((starRingEnd ℂ).comp σF).comp (algebraMap (𝓞 F) F) := by
    have h3 : spMap σ' = spMap ((((starRingEnd ℂ).comp σF).comp (algebraMap (𝓞 F) F))) := by
      rw [← y'.2, hy', Category.assoc, y.2, RingHom.comp_assoc, spMap_comp' _ (starRingEnd ℂ)]
    have h4 := Spec.map_injective h3
    exact congrArg CommRingCat.Hom.hom h4
  subst hσ'
  let yc : Pts Y ((starRingEnd ℂ).comp σF) := ⟨spMap (starRingEnd ℂ) ≫ yh.1, by
    rw [Category.assoc, yh.2, spMap_comp']⟩
  have e2 : w _ y' = G _ yc := h1 _ yc y' (by rw [hy', hyh, Category.assoc])
  rw [e2, e1]
  exact h2 σF _ yh yc rfl

end GlobalTheory.ModelLiftConj
