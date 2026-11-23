import Formalism.SharpRestriction.GrowthBounds.RootWeights.DeltaIntegralEnvelopingStable
import Lemmata.ClearingDenominators.UmonLeUzmon

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem delta_le_nabla {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hK : v ∈ Nabla (O := O) E lam v) : Delta (O := O) E v ≤ NablaSub (O := O) E lam v := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨u', hu', rfl⟩ u hu
  have := hK (u * u') (Submonoid.mul_mem _ hu hu')
  simpa using this

theorem integral_enveloping_span_top {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    Submodule.span (KK O) {x | ∃ u ∈ UZmon E, x = u v} = ⊤ := by
  rw [eq_top_iff, ← hI.2.2.2]
  refine Submodule.span_mono ?_
  rintro x ⟨u, hu, rfl⟩
  exact ⟨u, enveloping_le_integral_enveloping E hu, rfl⟩

theorem nabla_to_delta_maps_fg [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam)
    (hK : v ∈ Nabla (O := O) E lam v) : (nablaToDeltaMaps (O := O) E lam v).FG := by
  refine lattice_fg_of_integral_functionals (O := O) (W := Module.End (KK O) V) _
    {φ | ∃ u ∈ UZmon E, ∃ u' ∈ UZmon E, φ = (xi ∘ₗ u) ∘ₗ LinearMap.applyₗ (u' v)} ?_ ?_
  · intro f hf
    have hz : ∀ u' ∈ UZmon E, f (u' v) = 0 := by
      intro u' hu'
      refine enveloping_coordinate_separates hI hCR h1 fun u hu => ?_
      have := hf _ ⟨u, hu, u', hu', rfl⟩
      simpa using this
    have hk : (⊤ : Submodule (KK O) V) ≤ LinearMap.ker f := by
      rw [← integral_enveloping_span_top hI]
      refine Submodule.span_le.2 ?_
      rintro x ⟨u, hu, rfl⟩
      exact hz u hu
    exact LinearMap.ext fun x => hk Submodule.mem_top
  · rintro φ ⟨u, hu, u', hu', rfl⟩ f hf
    have ha : u' v ∈ Nabla (O := O) E lam v := delta_le_nabla hK (Submodule.subset_span ⟨u', hu', rfl⟩)
    have hb : f (u' v) ∈ Nabla (O := O) E lam v := delta_le_nabla hK (hf _ ha)
    obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hb u hu
    exact ⟨c, by simpa using hc⟩

theorem nabla_finitely_generated [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) :
    (NablaSub (O := O) E lam v).FG := by
  refine lattice_fg_of_integral_functionals (O := O) (W := V) _ {φ | ∃ u ∈ UZmon E, φ = xi ∘ₗ u} ?_ ?_
  · intro x hx
    refine enveloping_coordinate_separates hI hCR h1 fun u hu => ?_
    have := hx _ ⟨u, hu, rfl⟩
    simpa using this
  · rintro φ ⟨u, hu, rfl⟩ x hx
    obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hx u hu
    exact ⟨c, by simpa using hc⟩

theorem exists_scalar_multiple_mem_delta {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) (y : V) :
    ∃ o : O, o ≠ 0 ∧ o • y ∈ Delta (O := O) E v := by
  first | exact Bl.ClearingDenominators.goal1 .. | (apply Bl.ClearingDenominators.goal1 <;> assumption) | (intros; apply Bl.ClearingDenominators.goal1 <;> assumption) | (apply @Bl.ClearingDenominators.goal1 <;> assumption) | (intros; apply @Bl.ClearingDenominators.goal1 <;> assumption) | (apply @Bl.ClearingDenominators.goal1 <;> first | assumption | infer_instance)

theorem nabla_to_delta_maps_span_top [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hfg : (NablaSub (O := O) E lam v).FG) : MQ (K := KK O) (nablaToDeltaMaps (O := O) E lam v) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  obtain ⟨G, hG⟩ := hfg
  choose o ho ho' using exists_scalar_multiple_mem_delta (O := O) hI
  set c : O := ∏ g ∈ G, o (f g) with hc
  have hc0 : c ≠ 0 := prod_ne_zero_iff.2 fun g _ => ho _
  have hmem : c • f ∈ nablaToDeltaMaps (O := O) E lam v := by
    intro x hx
    have hx' : x ∈ Submodule.span O (G : Set V) := hG ▸ hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem g hg =>
      rw [LinearMap.smul_apply, hc, ← mul_prod_erase G _ hg, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (ho' _)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [← algebraMap_smul (KK O) r y, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ hy
  have hc1 : algebraMap O (KK O) c ≠ 0 := by
    simpa using (IsFractionRing.injective O (KK O)).ne hc0
  have : f = (algebraMap O (KK O) c)⁻¹ • (c • f) := by
    rw [← algebraMap_smul (KK O) c f, smul_smul, inv_mul_cancel₀ hc1, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem coordinate_rank_one_mem_maps {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) :
    xi.smulRight v ∈ nablaToDeltaMaps (O := O) E lam v := by
  intro x hx
  obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hx 1 (Submonoid.one_mem _)
  rw [Module.End.one_apply] at hc
  rw [LinearMap.smulRight_apply, hc, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩)

end hw

end Formalism.MainNotions.G.GLWeightTheory
