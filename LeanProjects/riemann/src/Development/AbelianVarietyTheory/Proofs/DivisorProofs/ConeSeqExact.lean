import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeSeq

variable {R : Type} [CommRing R]

theorem cls_eq {K I : Cx R} {n : ℤ} (x y : Cocycle K I n) (m : ℤ) (hm : m + 1 = n) (β : Cochain K I m)
    (h : (x : Cochain K I n) = (y : Cochain K I n) + δ m n β) :
    CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  exact ⟨β, by simp [h]⟩

end GlobalTheory.EtC.ConeSeq

theorem GlobalTheory.EtC.coneSeq_exact : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ), Function.Exact (cpull (mappingCone.inr f) I n) (cpull f I n) ∧ Function.Exact (cpull f I n) (cpre (mappingCone.fst f) I n (n + 1) (by omega)) ∧ Function.Exact (cpre (mappingCone.fst f) I n (n + 1) (by omega)) (cpull (mappingCone.inr f) I (n + 1)) := by
  intro R _ K L f I n
  refine ⟨?_, ?_, ?_⟩
  · intro y
    constructor
    · intro hb
      obtain ⟨b, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ b _) = 0 at hb
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hb
      obtain ⟨β, hβ⟩ := hb
      refine ⟨CohomologyClass.mk (mappingCone.descCocycle f (n.negOnePow • β) b (by omega) ?_), ?_⟩
      · rw [δ_units_smul, hβ]; simp [zcomp]
      · change CohomologyClass.mk (zcomp _ _ _) = _
        congr 1; ext1; simp [zcomp]
    · rintro ⟨z, rfl⟩
      obtain ⟨c, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ c _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨n.negOnePow • (mappingCone.inl f).comp (c : Cochain _ I n) (by omega), ?_⟩
      rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) rfl]
      simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, smul_smul]
  · intro y
    constructor
    · intro ha
      obtain ⟨a, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ a _) = 0 at ha
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)] at ha
      obtain ⟨γ, hγ⟩ := ha
      have hβ : δ n (n + 1) ((Cochain.ofHom (mappingCone.inr f)).comp γ (zero_add n)) = 0 := by
        rw [δ_ofHom_comp, hγ]; simp [zcomp]
      refine ⟨CohomologyClass.mk (Cocycle.mk (-(n.negOnePow • (Cochain.ofHom (mappingCone.inr f)).comp γ (zero_add n))) (n + 1) rfl (by rw [δ_neg, δ_units_smul, hβ]; simp)), ?_⟩
      change CohomologyClass.mk (zcomp _ _ _) = _
      refine ConeSeq.cls_eq _ _ (n - 1) (by omega) (-((mappingCone.inl f).comp γ (by omega))) ?_
      have key := δ_comp (mappingCone.inl f) γ (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) rfl
      rw [hγ] at key
      simp [zcomp] at key
      simp [zcomp, key, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
    · rintro ⟨z, rfl⟩
      obtain ⟨b, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ b _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)]
      refine ⟨-(n.negOnePow • (mappingCone.snd f).comp (b : Cochain _ I n) (zero_add n)), ?_⟩
      rw [δ_neg, δ_units_smul, δ_comp _ _ _ 1 (n + 1) (n + 1) rfl (zero_add 1) rfl]
      simp [zcomp, smul_smul, Cochain.comp_assoc_of_second_is_zero_cochain]
  · intro y
    constructor
    · intro hc
      obtain ⟨c, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ c _) = 0 at hc
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)] at hc
      obtain ⟨β, hβ⟩ := hc
      set a : Cochain K I n := (mappingCone.inl f).comp (c : Cochain _ I (n + 1)) (by omega) +
        n.negOnePow • (Cochain.ofHom f).comp β (zero_add n) with ha_def
      have hsnd := δ_comp (mappingCone.snd f) β (zero_add n) 1 (n + 1) (n + 1) rfl (zero_add 1) rfl
      rw [hβ] at hsnd
      simp [zcomp] at hsnd
      have hdec : (c : Cochain _ I (n + 1)) = (mappingCone.fst f).1.comp a (by omega) +
          δ n (n + 1) ((mappingCone.snd f).comp β (zero_add n)) := by
        rw [mappingCone.ext_cochain_from_iff f n (n + 1) rfl]
        constructor
        · simp [ha_def, hsnd, Cochain.comp_assoc_of_second_is_zero_cochain]
        · simp [ha_def, hsnd, Cochain.comp_assoc_of_second_is_zero_cochain]
      have hcoc : δ n (n + 1) a = 0 := by
        have h1 := congrArg (δ (n + 1) (n + 2)) hdec
        rw [δ_add, δ_δ, add_zero, Cocycle.δ_eq_zero c (n + 2)] at h1
        rw [δ_comp _ _ _ 2 (n + 1) (n + 2) (by omega) rfl rfl] at h1
        simp at h1
        have h2 := congrArg (fun x => (mappingCone.inl f).comp x (show -1 + (n + 2) = n + 1 by omega)) h1
        simpa using h2.symm
      refine ⟨CohomologyClass.mk (Cocycle.mk a (n + 1) rfl hcoc), ?_⟩
      change CohomologyClass.mk (zcomp _ _ _) = _
      refine ConeSeq.cls_eq _ _ n rfl (-((mappingCone.snd f).comp β (zero_add n))) ?_
      simp [zcomp, hdec]
    · rintro ⟨z, rfl⟩
      obtain ⟨a, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ a _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)]
      exact ⟨0, by simp [zcomp]⟩
