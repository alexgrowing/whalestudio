import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns

theorem det_eq_one {K : Type*} [Field K] {n : ℕ} (u : Matrix (Fin n) (Fin n) K)
    (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0) : u.det = 1 := by
  rw [Matrix.det_of_lowerTriangular u (fun i j hij => h0 _ _ hij)]
  simp [h1]

theorem linearIndependent_cols {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {n : ℕ}
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0)
    (v : Fin n → M) (hv : LinearIndependent K v) :
    LinearIndependent K fun k => ∑ l, u l k • v l := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  have hz : ∀ l, ∑ k, u l k * g k = 0 := by
    apply hv (fun l => ∑ k, u l k * g k)
    rw [← hg]
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  have hm : u.mulVec g = 0 := funext hz
  have hg0 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_eq_one u h1 h0]; exact one_ne_zero) hm
  intro i
  exact congrFun hg0 i

theorem span_cols {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {n : ℕ}
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ k, u k k = 1) (h0 : ∀ l k, l < k → u l k = 0)
    (v : Fin n → M) :
    Submodule.span K (Set.range fun k => ∑ l, u l k • v l) = Submodule.span K (Set.range v) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨m, rfl⟩
    have hu : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u (by rw [det_eq_one u h1 h0]; exact isUnit_one)
    have hvm : v m = ∑ k, u⁻¹ k m • ∑ l, u l k • v l := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have hl : ∀ l, ∑ k, (u⁻¹ k m * u l k) • v l = (if l = m then (1 : K) else 0) • v l := by
        intro l
        rw [← Finset.sum_smul]
        congr 1
        have := congrFun (congrFun hu l) m
        rw [Matrix.mul_apply, Matrix.one_apply] at this
        rw [← this]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      simp [hl]
    show v m ∈ _
    rw [hvm]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem genU_diag (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (k : Fin (r s)) :
    genU Ω r s k k = 1 := by
  simp [genU]

theorem genU_zero (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (l k : Fin (r s)) (h : l < k) :
    genU Ω r s l k = 0 := by
  have h1 : ¬ k < l := not_lt.2 h.le
  have h2 : l ≠ k := h.ne
  simp [genU, h1, h2]

theorem genU_gen (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (q : GenIx r) :
    genU Ω r q.1 q.2.1.1 q.2.1.2 =
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) := by
  obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := q
  exact dif_pos h

theorem algebraicIndependent_gen (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) :
    AlgebraicIndependent Ω (fun q : GenIx r =>
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
  (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
    (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    (IsFractionRing.injective _ _)

theorem algebraicIndependent_comp {Ω₀ Ω K I : Type} [Field Ω₀] [Field Ω] [Field K] [Algebra Ω K]
    (fn : Ω₀ →+* Ω) {x : I → K} (hx : AlgebraicIndependent Ω x) :
    letI := ((algebraMap Ω K).comp fn).toAlgebra
    AlgebraicIndependent Ω₀ x := by
  letI a1 : Algebra Ω₀ Ω := fn.toAlgebra
  letI a2 : Algebra Ω₀ K := ((algebraMap Ω K).comp fn).toAlgebra
  haveI : IsScalarTower Ω₀ Ω K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact hx.restrictScalars (R := Ω₀) (K := Ω) fn.injective

theorem adjoin_entries {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) {S : Type} (r : S → ℕ) :
    letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra
    IntermediateField.adjoin Ω₀
        (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => genU Ω r q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) := by
  letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨s, l, k⟩, rfl⟩
    show genU Ω r s l k ∈ _
    by_cases h : k < l
    · have := genU_gen Ω r ⟨s, ⟨(l, k), h⟩⟩
      exact this ▸ IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
    · by_cases e : l = k
      · subst e
        rw [genU_diag]
        exact one_mem _
      · rw [genU_zero Ω r s l k (lt_of_le_of_ne (not_lt.1 h) e)]
        exact zero_mem _
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    show algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) ∈ _
    rw [← genU_gen]
    exact IntermediateField.subset_adjoin _ _ ⟨⟨q.1, q.2.1.1, q.2.1.2⟩, rfl⟩

theorem isGenericFlag_columns : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (S : Type) (r : S → ℕ) (d : ℕ), 0 < d → (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q))) (GenField Ω r) = d) → ∀ (E₀ E' : Type) [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E'] [Module (GenField Ω r) E'] (j : E₀ →+ E') (V₀ : S → Submodule Ω₀ E₀) (c : ∀ s, Fin (r s) → E₀), (∀ s, LinearIndependent Ω₀ (c s) ∧ Submodule.span Ω₀ (Set.range (c s)) = V₀ s) → (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω (GenField Ω r) (fn a) • j e) → (∀ s, LinearIndependent (GenField Ω r) fun k => j (c s k)) → (∀ s, Submodule.span (GenField Ω r) (Set.range fun k => ∑ l, genU Ω r s l k • j (c s l)) = Submodule.span (GenField Ω r) (Set.range fun k => j (c s k))) ∧ (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; IsGenericFlag (Ω' := GenField Ω r) j V₀ (fun s k => ∑ l, genU Ω r s l k • j (c s l)) d) := by
  intro Ω₀ Ω _ _ fn S r d hd hdeg E₀ E' _ _ _ _ j V₀ c hc hj hli
  refine ⟨fun s => span_cols _ (genU_diag Ω r s) (genU_zero Ω r s) _, ?_⟩
  letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra
  refine ⟨c, genU Ω r, hc, hj, hli,
    fun s => linearIndependent_cols _ (genU_diag Ω r s) (genU_zero Ω r s) _ (hli s),
    genU_diag Ω r, genU_zero Ω r, fun _ _ => rfl, ?_, hd, ?_⟩
  · have h := algebraicIndependent_comp fn (algebraicIndependent_gen Ω r)
    have he : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) = fun q : GenIx r =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) :=
      funext (genU_gen Ω r)
    rw [he]
    exact h
  · rw [adjoin_entries fn r]
    exact hdeg

end GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns
