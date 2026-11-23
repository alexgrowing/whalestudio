import Formalism.WachLatticeTwists.HodgeTateChains.XiAdicFiltrationData
import Formalism.WachLatticeTwists.TorsionLengthCounts.SubmoduleLengthBoundStatement

open Module IsDiscreteValuationRing

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

lemma cyc_len (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Cy : Type)
    [AddCommGroup Cy] [Module O Cy] (c0 : Cy) (hc0 : ∀ y : Cy, ∃ a : O, y = a • c0)
    (P : Submodule O Cy) (a : O) (hP : ∀ x ∈ P, a • x = 0) :
    Module.length O P ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  let φ : O →ₗ[O] Cy := LinearMap.toSpanSingleton O Cy c0
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal (P.comap φ : Ideal O)).principal
  have hbmem : b • c0 ∈ P := by
    have : b ∈ (P.comap φ : Ideal O) := by rw [hb]; exact Submodule.mem_span_singleton_self b
    exact this
  let ψ : O →ₗ[O] P := LinearMap.toSpanSingleton O P ⟨b • c0, hbmem⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨p, hp⟩
    obtain ⟨r, rfl⟩ := hc0 p
    have hr : r ∈ (P.comap φ : Ideal O) := hp
    rw [hb, Submodule.mem_span_singleton] at hr
    obtain ⟨r', rfl⟩ := hr
    refine ⟨r', Subtype.ext ?_⟩
    simp [ψ, LinearMap.toSpanSingleton_apply, smul_smul]
  have hker : (Ideal.span {a} : Submodule O O) ≤ LinearMap.ker ψ := by
    rw [Ideal.span, Submodule.span_le, Set.singleton_subset_iff]
    show ψ a = 0
    apply Subtype.ext
    simpa [ψ, LinearMap.toSpanSingleton_apply] using hP _ hbmem
  exact Module.length_le_of_surjective (Submodule.liftQ _ ψ hker)
    (fun p => by
      obtain ⟨r, hr⟩ := hψ p
      exact ⟨Submodule.Quotient.mk r, by rw [Submodule.liftQ_apply]; exact hr⟩)

theorem tbLen : StatTBLen := by
  intro O _ _ _ n _ Q Cy _ _ _ _ ι π hι hex ⟨c0, hc0⟩ N ℓ c hN
  let N1 : Submodule O (n → Formalism.NG.KO O) := N.comap ι
  have hN1 : ∀ x ∈ N1, ((ℓ : O) ^ c) • x = 0 := by
    intro x hx
    apply hι
    rw [map_smul, map_zero]
    exact hN _ hx
  have hl1 := Formalism.RepresentationBoundsCohomology.submoduleLengthBound_statement O n N1 ℓ c hN1
  let f : N1 →ₗ[O] N := (ι.comp N1.subtype).codRestrict N (fun x => x.2)
  let πN : N →ₗ[O] Cy := π.comp N.subtype
  let g : N →ₗ[O] LinearMap.range πN := πN.rangeRestrict
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply hι
    exact congrArg Subtype.val hxy
  have hg : Function.Surjective g := LinearMap.surjective_rangeRestrict _
  have hfg : Function.Exact f g := by
    intro x
    constructor
    · intro hx
      have hx' : π x.1 = 0 := congrArg Subtype.val hx
      obtain ⟨t, ht⟩ := (hex _).1 hx'
      exact ⟨⟨t, by show ι t ∈ N; rw [ht]; exact x.2⟩, Subtype.ext ht⟩
    · rintro ⟨t, rfl⟩
      apply Subtype.ext
      exact (hex _).2 ⟨t.1, rfl⟩
  have hadd := Module.length_eq_add_of_exact f g hf hg hfg
  have hl2 : Module.length O (LinearMap.range πN) ≤ Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ c}) := by
    apply cyc_len O Cy c0 hc0
    rintro _ ⟨x, rfl⟩
    rw [← map_smul]
    have : ((ℓ : O) ^ c) • x = 0 := Subtype.ext (hN _ x.2)
    rw [this, map_zero]
  have hl3 : Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ c})
      = (c : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by
    rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, addVal_pow, nsmul_eq_mul]
  rw [hadd, add_mul, one_mul]
  exact add_le_add hl1 (hl3 ▸ hl2)

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
