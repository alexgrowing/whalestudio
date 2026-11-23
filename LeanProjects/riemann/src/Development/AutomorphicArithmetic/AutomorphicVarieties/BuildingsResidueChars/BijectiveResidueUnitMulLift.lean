import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ComplDefY

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

theorem UpperTheory.bijective_residue_unit_mul_lift :
    ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (u : w.adicCompletionIntegers F), Valued.v (u : w.adicCompletion F) = 1 → ∀ s : 𝓞 F ⧸ w.asIdeal → 𝓞 F, (∀ r, Ideal.Quotient.mk w.asIdeal (s r) = r) → Function.Bijective fun r => IsLocalRing.residue (w.adicCompletionIntegers F) (u * algebraMap (𝓞 F) (w.adicCompletionIntegers F) (s r)) := by
  intro F _ _ w u hu s hs
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  have hv : ∀ k : F, Valued.v (algebraMap F (w.adicCompletion F) k) = w.valuation F k :=
    fun k => IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w k
  have hmem : ∀ x : w.adicCompletionIntegers F,
      x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ↔ Valued.v (x : w.adicCompletion F) < 1 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have hx : Valued.v (x : w.adicCompletion F) ≤ 1 := x.2
    exact ⟨fun h => lt_of_le_of_ne hx h, fun h => ne_of_lt h⟩
  have hcoe : ∀ b : 𝓞 F, ((algebraMap (𝓞 F) (w.adicCompletionIntegers F) b : w.adicCompletionIntegers F) : w.adicCompletion F)
      = algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F b) := fun b => rfl
  have hker : ∀ a ∈ w.asIdeal,
      ((IsLocalRing.residue (w.adicCompletionIntegers F)).comp
        (algebraMap (𝓞 F) (w.adicCompletionIntegers F))) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmem, hcoe, hv]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem w a).mpr ha
  let g := Ideal.Quotient.lift w.asIdeal ((IsLocalRing.residue (w.adicCompletionIntegers F)).comp
        (algebraMap (𝓞 F) (w.adicCompletionIntegers F))) hker
  have hg : ∀ r, IsLocalRing.residue (w.adicCompletionIntegers F)
      (algebraMap (𝓞 F) (w.adicCompletionIntegers F) (s r)) = g r := by
    intro r
    conv_rhs => rw [← hs r]
    rfl
  have hinj : Function.Injective g := g.injective
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    have hU : {z : w.adicCompletion F | Valued.v (z - (y : w.adicCompletion F)) < 1} ∈ nhds (y : w.adicCompletion F) := by
      rw [Valued.mem_nhds]
      refine ⟨1, fun z hz => ?_⟩
      simpa [Valuation.restrict_lt_iff_lt_embedding] using hz
    obtain ⟨a, ha⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) w).mem_nhds hU
    have ha' : Valued.v (algebraMap F (w.adicCompletion F) a - (y : w.adicCompletion F)) < 1 := ha
    have hale : w.valuation F a ≤ 1 := by
      rw [← hv]
      have hy : Valued.v (y : w.adicCompletion F) ≤ 1 := y.2
      have e : algebraMap F (w.adicCompletion F) a
          = (algebraMap F (w.adicCompletion F) a - (y : w.adicCompletion F)) + (y : w.adicCompletion F) := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le ha'.le hy)
    obtain ⟨b, hb⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer w hale 1
    have hb' : Valued.v (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F b - a)) < 1 := by
      rw [hv]; simpa using hb
    refine ⟨Ideal.Quotient.mk w.asIdeal b, ?_⟩
    change IsLocalRing.residue _ (algebraMap (𝓞 F) (w.adicCompletionIntegers F) b) = _
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmem]
    have e : ((algebraMap (𝓞 F) (w.adicCompletionIntegers F) b - y : w.adicCompletionIntegers F) : w.adicCompletion F)
        = algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F b - a)
          + (algebraMap F (w.adicCompletion F) a - (y : w.adicCompletion F)) := by
      rw [map_sub]
      change ((algebraMap (𝓞 F) (w.adicCompletionIntegers F) b : w.adicCompletionIntegers F) : w.adicCompletion F) - (y : w.adicCompletion F) = _
      rw [hcoe]
      ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt hb' ha')
  have hc : IsUnit (IsLocalRing.residue (w.adicCompletionIntegers F) u) :=
    ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr hu).map _
  have hf : (fun r => IsLocalRing.residue (w.adicCompletionIntegers F)
      (u * algebraMap (𝓞 F) (w.adicCompletionIntegers F) (s r)))
      = (fun z => (hc.unit : IsLocalRing.ResidueField (w.adicCompletionIntegers F)) * z) ∘ g := by
    funext r
    simp only [Function.comp_apply, map_mul, hg, IsUnit.unit_spec]
  rw [hf]
  exact (Units.mulLeft_bijective hc.unit).comp ⟨hinj, hsurj⟩
