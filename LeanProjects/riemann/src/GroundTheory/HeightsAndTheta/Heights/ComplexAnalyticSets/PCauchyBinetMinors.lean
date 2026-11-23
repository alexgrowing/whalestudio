import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCauchyBinet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset

namespace CauchyBinetMinorsAlt

theorem det_one_add_eq_sum {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n R) :
    (1 + X).det = ∑ s : Finset n, (X.submatrix ((↑) : s → n) ((↑) : s → n)).det := by
  rw [add_comm]
  change detRowAlternating (fun i => X i + (1 : Matrix n n R) i) = _
  rw [show (fun i => X i + (1 : Matrix n n R) i) =
      (fun i => X i) + (fun i => (1 : Matrix n n R) i) from rfl, AlternatingMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact det_piecewise_one_eq_submatrix_det X s

theorem minor_reindex {R : Type*} [CommRing R] {n k : ℕ} (X : Matrix (Fin n) (Fin n) R)
    (s : Finset (Fin n)) (hk : s.card = k) :
    (X.submatrix ((↑) : s → Fin n) ((↑) : s → Fin n)).det =
      (X.submatrix (s.orderEmbOfFin hk) (s.orderEmbOfFin hk)).det := by
  rw [← det_submatrix_equiv_self (s.orderIsoOfFin hk).toEquiv]
  congr 1

theorem sum_finset_by_card {n : ℕ} {β : Type*} [AddCommMonoid β] (f : Finset (Fin n) → β) :
    ∑ s : Finset (Fin n), f s =
      ∑ k ∈ range (n + 1), ∑ S : {S : Finset (Fin n) // S.card = k}, f S.1 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n + 1)) (fun s _ => by
    have := card_le_univ s
    simp only [Fintype.card_fin] at this
    exact mem_range.2 (by omega))]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_subtype _ (fun s => by simp) _

theorem sum_strictMono {n k : ℕ} {β : Type*} [AddCommMonoid β]
    [DecidablePred (fun b : Fin k → Fin n => StrictMono b)] (g : (Fin k → Fin n) → β) :
    ∑ b ∈ univ.filter (fun b : Fin k → Fin n => StrictMono b), g b =
      ∑ S : {S : Finset (Fin n) // S.card = k}, g (S.1.orderEmbOfFin S.2) := by
  symm
  refine Finset.sum_bij (fun S _ => (S.1.orderEmbOfFin S.2 : Fin k → Fin n)) ?_ ?_ ?_ ?_
  · intro S _
    simpa using (S.1.orderEmbOfFin S.2).strictMono
  · intro S _ T _ h
    apply Subtype.ext
    have h' := congrArg Set.range h
    simp only [range_orderEmbOfFin] at h'
    exact_mod_cast h'
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    have hc : (univ.image b).card = k := by
      rw [card_image_of_injective _ hb.injective, card_univ, Fintype.card_fin]
    exact ⟨⟨univ.image b, hc⟩, mem_univ _,
      (orderEmbOfFin_unique hc (fun x => mem_image_of_mem b (mem_univ x)) hb).symm⟩
  · intro _ _
    rfl

theorem principal_minor {p q k : ℕ} (M : Matrix (Fin p) (Fin q) ℂ)
    (S : {S : Finset (Fin q) // S.card = k}) :
    ((Mᴴ * M).submatrix (S.1.orderEmbOfFin S.2) (S.1.orderEmbOfFin S.2)).det =
      ∑ T : {T : Finset (Fin p) // T.card = k},
        ((‖(M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)).det‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, CauchyBinet.proof]
  refine Finset.sum_congr rfl fun T _ => ?_
  have h1 : colsOf (Mᴴ.submatrix (S.1.orderEmbOfFin S.2) id) T =
      (M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2))ᴴ := by
    ext i j
    simp [colsOf, conjTranspose_apply]
  have h2 : rowsOf (M.submatrix id (S.1.orderEmbOfFin S.2)) T =
      M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2) := by
    ext i j
    simp [rowsOf]
  rw [h1, h2, det_conjTranspose, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

end CauchyBinetMinorsAlt

open CauchyBinetMinorsAlt in

theorem CauchyBinetMinors.proof : CauchyBinetMinors.Statement := by
  intro p q M
  let G : (k : ℕ) → {T : Finset (Fin p) // T.card = k} → {S : Finset (Fin q) // S.card = k} → ℂ :=
    fun k T S => ((‖(M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)).det‖ ^ 2 : ℝ) : ℂ)
  have hL : (1 + Mᴴ * M).det = ∑ k ∈ range (p + q + 1), ∑ T, ∑ S, G k T S := by
    rw [det_one_add_eq_sum, sum_finset_by_card]
    have hk : ∀ k, ∑ S : {S : Finset (Fin q) // S.card = k},
        ((Mᴴ * M).submatrix ((↑) : S.1 → Fin q) ((↑) : S.1 → Fin q)).det = ∑ T, ∑ S, G k T S := by
      intro k
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [minor_reindex _ S.1 S.2, principal_minor]
    simp only [hk]
    have hsub : range (q + 1) ⊆ range (p + q + 1) := range_subset_range.2 (by omega)
    exact Finset.sum_subset hsub (f := fun k => ∑ T, ∑ S, G k T S) (fun k _ hk => by
      have : IsEmpty {S : Finset (Fin q) // S.card = k} := ⟨fun S => by
        have := card_le_univ S.1
        rw [Fintype.card_fin, S.2] at this
        simp only [mem_range] at hk
        omega⟩
      exact Finset.sum_eq_zero fun T _ => Fintype.sum_empty _)
  have hR : ((∑ k ∈ range (p + 1),
        ∑ a ∈ univ.filter (fun a : Fin k → Fin p => StrictMono a),
          ∑ b ∈ univ.filter (fun b : Fin k → Fin q => StrictMono b),
            ‖(M.submatrix a b).det‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ range (p + q + 1), ∑ T, ∑ S, G k T S := by
    simp only [Complex.ofReal_sum]
    have hk : ∀ k, (∑ a ∈ univ.filter (fun a : Fin k → Fin p => StrictMono a),
          ∑ b ∈ univ.filter (fun b : Fin k → Fin q => StrictMono b),
            ((‖(M.submatrix a b).det‖ ^ 2 : ℝ) : ℂ)) = ∑ T, ∑ S, G k T S := by
      intro k
      rw [sum_strictMono]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [sum_strictMono]
    simp only [hk]
    have hsub : range (p + 1) ⊆ range (p + q + 1) := range_subset_range.2 (by omega)
    exact Finset.sum_subset hsub (f := fun k => ∑ T, ∑ S, G k T S) (fun k _ hk => by
      have : IsEmpty {T : Finset (Fin p) // T.card = k} := ⟨fun T => by
        have := card_le_univ T.1
        rw [Fintype.card_fin, T.2] at this
        simp only [mem_range] at hk
        omega⟩
      exact Fintype.sum_empty _)
  rw [hL, hR]

end GroundTheory.Heights₂.Heights
