import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeTgt

variable {R : Type} [CommRing R]

theorem cls_eq' {K I : Cx R} {n : ℤ} (x y : Cocycle K I n) (m : ℤ) (hm : m + 1 = n) (β : Cochain K I m)
    (h : (x : Cochain K I n) = (y : Cochain K I n) + δ m n β) :
    CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  exact ⟨β, by simp [h]⟩

end GlobalTheory.EtC.ConeTgt

private theorem coe_zcomp {R : Type} [CommRing R] {K L M : Cx R} {m n k : ℤ}
    (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) :
    ((zcomp a b h : Cocycle K M k) : Cochain K M k) = a.1.comp b.1 h := rfl

private theorem cohomologyClass_mk_eq_zero_of_eq_δ {R : Type} [CommRing R] {K L : Cx R} {n : ℤ} (x : Cocycle K L n)
    (m : ℤ) (hm : m + 1 = n) (β : Cochain K L m) (h : (x : Cochain K L n) = δ m n β) :
    CohomologyClass.mk x = 0 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
  exact ⟨β, h.symm⟩

theorem GlobalTheory.EtC.coneSeqTgt_exact : ∀ (R : Type) [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ), Function.Exact (cpush K f n) (cpush K (mappingCone.inr f) n) ∧ Function.Exact (cpush K (mappingCone.inr f) n) (cpost K (mappingCone.fst f) n (n + 1) rfl) ∧ Function.Exact (cpost K (mappingCone.fst f) n (n + 1) rfl) (cpush K f (n + 1)) := by
  intro R _ K I J f n
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_⟩
  · obtain ⟨y, rfl⟩ := c.mk_surjective
    constructor
    · intro hy
      simp only [cpush, cpost_mk] at hy
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hy
      obtain ⟨γ, hγ⟩ := hy
      rw [coe_zcomp] at hγ
      have ha : δ n (n + 1) (γ.comp (mappingCone.fst f).1 (by omega : n - 1 + 1 = n)) = 0 := by
        rw [δ_comp γ (mappingCone.fst f).1 _ n 2 (n + 1) rfl (by omega) rfl,
          Cocycle.δ_eq_zero, hγ]
        simp [Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl ha), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n - 1) (by omega)
        (-(γ.comp (mappingCone.snd f) (add_zero _))) ?_
      rw [coe_zcomp, δ_neg, δ_comp_zero_cochain _ _ _ (by omega), mappingCone.δ_snd, hγ]
      simp [Cochain.comp_assoc_of_second_is_zero_cochain,
        Cochain.comp_assoc_of_third_is_zero_cochain, mappingCone.inr_snd]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨x, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ (n + -1) (by omega) (x.1.comp (mappingCone.inl f) rfl) ?_
      rw [δ_comp x.1 (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl (neg_add_cancel 1),
        mappingCone.δ_inl, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.ofHom_comp]
  · obtain ⟨z, rfl⟩ := c.mk_surjective
    constructor
    · intro hz
      rw [cpost_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hz
      obtain ⟨c₀, hc₀⟩ := hz
      rw [coe_zcomp] at hc₀
      have hy : δ n (n + 1) (z.1.comp (mappingCone.snd f) (add_zero n) +
          c₀.comp (Cochain.ofHom f) (add_zero n)) = 0 := by
        rw [δ_add, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, δ_comp_ofHom, hc₀,
          Cocycle.δ_eq_zero]
        simp [Cochain.comp_assoc_of_third_is_zero_cochain]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hy), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n + -1) (by omega)
        (c₀.comp (mappingCone.inl f) rfl) ?_
      rw [coe_zcomp, δ_comp c₀ (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl
        (neg_add_cancel 1), mappingCone.δ_inl, hc₀]
      rw [mappingCone.ext_cochain_to_iff _ n (n + 1) rfl]
      constructor
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.add_comp]
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain,
          Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.add_comp]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨y, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl 0 ?_
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
  · obtain ⟨w, rfl⟩ := c.mk_surjective
    constructor
    · intro hw
      simp only [cpush, cpost_mk] at hw
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hw
      obtain ⟨b, hb⟩ := hw
      rw [coe_zcomp] at hb
      refine ⟨CohomologyClass.mk (mappingCone.liftCocycle f w (-b) rfl
        (by rw [δ_neg, hb]; simp)), ?_⟩
      rw [cpost_mk]
      congr 1
      apply Cocycle.ext
      rw [coe_zcomp]
      simp [mappingCone.liftCochain_fst]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨z, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl (-(z.1.comp (mappingCone.snd f) (add_zero n))) ?_
      rw [δ_neg, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_third_is_zero_cochain]
