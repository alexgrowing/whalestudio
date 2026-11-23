import Mathlib

open Polynomial

theorem UpperTheory.V.Ws.fibTrdeg :
    ∀ {D C K : Type} [CommRing D] [IsDomain D] [CommRing C] [Algebra D C] [Field K] (j : C →+* K) (T : Finset K), Function.Injective j → Function.Injective (algebraMap D C) →
          (∀ E : Subfield K, (∀ d, j (algebraMap D C d) ∈ E) → (∀ t ∈ T, t ∈ E) →
            (∀ (p : K[X]) (x : K), p.Monic → (∀ n, p.coeff n ∈ E) → p.IsRoot x → x ∈ E) → ∀ y, j y ∈ E) →
          Algebra.trdeg D C ≤ (T.card : Cardinal) := by
  intro D C K _ _ _ _ _ j T hj hD hE
  letI : Algebra D K := (j.comp (algebraMap D C)).toAlgebra
  haveI : FaithfulSMul D C := (faithfulSMul_iff_algebraMap_injective D C).mpr hD
  haveI : FaithfulSMul D K := (faithfulSMul_iff_algebraMap_injective D K).mpr (hj.comp hD)
  haveI : IsDomain C := Function.Injective.isDomain j hj
  set M := AlgebraicIndependent.matroid D K with hM
  obtain ⟨S, hS, hSalg⟩ :=
    AlgebraicIndependent.matroid_isFlat_iff.mp (Matroid.isFlat_closure (M := M) (T : Set K))
  have hmemS : ∀ x, x ∈ S ↔ x ∈ M.closure (T : Set K) := fun x => Set.ext_iff.mp hS x
  let E : Subfield K :=
    { S.toSubring with
      inv_mem' := fun x hx => by
        by_cases h0 : x = 0
        · rw [h0, inv_zero]
          exact S.zero_mem
        have halg : IsAlgebraic S x⁻¹ := by
          refine ⟨Polynomial.C (⟨x, hx⟩ : S) * Polynomial.X - 1, ?_, ?_⟩
          · intro h
            have h' := congrArg (fun q => Polynomial.coeff q 0) h
            simp at h'
          · simp [h0]
        exact (hmemS _).mpr (hSalg _ halg) }
  have hjE : ∀ y, j y ∈ E := by
    refine hE E (fun d => S.algebraMap_mem d) (fun t ht => ?_) (fun p x hp hc hr => ?_)
    · exact (hmemS t).mpr (M.subset_closure (T : Set K) (by simp [M]) ht)
    · have hl : p ∈ Polynomial.lifts (algebraMap S K) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact ⟨⟨p.coeff n, hc n⟩, rfl⟩
      obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hp
      have halg : IsAlgebraic S x := by
        refine ⟨q, hqm.ne_zero, ?_⟩
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq]
        exact hr
      exact (hmemS x).mpr (hSalg x halg)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis D C
  rw [← hs.cardinalMk_eq_trdeg]
  let jA : C →ₐ[D] K := { j with commutes' := fun _ => rfl }
  have hind : AlgebraicIndependent D (jA ∘ ((↑) : s → C)) := hs.1.map' (f := jA) hj
  have hI : M.Indep (Set.range (jA ∘ ((↑) : s → C))) := by
    rw [AlgebraicIndependent.matroid_indep_iff]
    exact hind.to_subtype_range
  have hsub : Set.range (jA ∘ ((↑) : s → C)) ⊆ M.closure (T : Set K) := by
    rintro _ ⟨a, rfl⟩
    exact (hmemS _).mp (hjE a)
  calc Cardinal.mk s = Cardinal.mk (Set.range (jA ∘ ((↑) : s → C))) :=
        (Cardinal.mk_range_eq _ hind.injective).symm
    _ ≤ M.cRk (M.closure (T : Set K)) := hI.cardinalMk_le_cRk_of_subset hsub
    _ = M.cRk (T : Set K) := M.cRk_closure _
    _ ≤ Cardinal.mk (T : Set K) := M.cRk_le_cardinalMk _
    _ = (T.card : Cardinal) := by simp
