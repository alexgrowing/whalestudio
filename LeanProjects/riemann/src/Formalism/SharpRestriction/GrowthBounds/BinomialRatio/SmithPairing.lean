import Mathlib

namespace Formalism.InvariantFactorPaths.KP

open Module

private theorem smithMatrix_lemma {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (n : ℕ)
    (φ : (Fin n → O) →ₗ[O] (Fin n → O)) :
    ∃ b c : Module.Basis (Fin n) O (Fin n → O), ∀ i j, i ≠ j → c.repr (φ (b j)) i = 0 := by
  classical
  obtain ⟨m, snf⟩ := Submodule.smithNormalForm (Pi.basisFun O (Fin n)) (LinearMap.range φ)
  have hx : ∀ i, ∃ x, φ x = (snf.bN i : Fin n → O) := fun i => LinearMap.mem_range.1 (snf.bN i).2
  choose x hx using hx
  let s : LinearMap.range φ →ₗ[O] (Fin n → O) := snf.bN.constr O x
  have hs : ∀ y : LinearMap.range φ, φ (s y) = y := by
    have : φ ∘ₗ s = (LinearMap.range φ).subtype :=
      snf.bN.ext fun i => by simp [s, Module.Basis.constr_basis, hx]
    intro y
    exact LinearMap.congr_fun this y
  have hsi : Function.Injective s := fun y y' h => Subtype.ext (by rw [← hs y, ← hs y', h])
  let f : (Fin n → O) →ₗ[O] LinearMap.range s := s.rangeRestrict ∘ₗ φ.rangeRestrict
  have hf : ∀ v : LinearMap.range s, f v = v := by
    rintro ⟨v, y, rfl⟩
    apply Subtype.ext
    have : φ.rangeRestrict (s y) = y := Subtype.ext (hs y)
    simp only [f, LinearMap.comp_apply, this]
    rfl
  have hc : IsCompl (LinearMap.range s) (LinearMap.ker f) := LinearMap.isCompl_of_proj hf
  have hK : ∀ v ∈ LinearMap.ker f, φ v = 0 := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have h1 : s (φ.rangeRestrict v) = 0 := by
      have := congrArg Subtype.val hv
      simpa [f] using this
    have h2 : φ.rangeRestrict v = 0 := hsi (by rw [h1, map_zero])
    simpa using congrArg Subtype.val h2
  obtain ⟨k, bK⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin n)) (LinearMap.ker f)
  let bS : Module.Basis (Fin m) O (LinearMap.range s) := snf.bN.map (LinearEquiv.ofInjective s hsi)
  let B : Module.Basis (Fin m ⊕ Fin k) O (Fin n → O) :=
    (bS.prod bK).map (Submodule.prodEquivOfIsCompl _ _ hc)
  have hB1 : ∀ i, B (Sum.inl i) = x i := by
    intro i
    simp [B, bS, Module.Basis.constr_basis, s]
  have hB2 : ∀ l, B (Sum.inr l) ∈ LinearMap.ker f := by
    intro l
    simp [B]
  have hcard : n = m + k := by
    have := Fintype.card_congr ((Pi.basisFun O (Fin n)).indexEquiv B)
    simpa using this
  let e1 : Fin m ≃ Set.range snf.f := Equiv.ofInjective snf.f snf.f.injective
  have hc2 : Fintype.card (Fin k) = Fintype.card {j // j ∉ Set.range snf.f} := by
    have h1 := Fintype.card_congr e1
    rw [Fintype.card_subtype_compl, ← h1]
    simp only [Fintype.card_fin]
    omega
  let e2 : Fin k ≃ {j // j ∉ Set.range snf.f} := Fintype.equivOfCardEq hc2
  let E : Fin m ⊕ Fin k ≃ Fin n :=
    (Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ Set.range snf.f))
  refine ⟨B.reindex E, snf.bM, fun i j hij => ?_⟩
  obtain ⟨z, rfl⟩ := E.surjective j
  rw [Module.Basis.reindex_apply, E.symm_apply_apply]
  rcases z with a | l
  · have hEa : E (Sum.inl a) = snf.f a := rfl
    rw [hEa] at hij
    rw [hB1, hx, snf.snf a, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, if_neg hij.symm, smul_zero]
  · rw [hK _ (hB2 l), map_zero, Finsupp.zero_apply]

theorem smithMatrix {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) O) :
    ∃ P Q : Matrix (Fin n) (Fin n) O, IsUnit P.det ∧ IsUnit Q.det ∧
      ∀ i j, i ≠ j → (P * A * Q) i j = 0 := by
  classical
  obtain ⟨b, c, hbc⟩ := smithMatrix_lemma n (Matrix.toLin' A)
  refine ⟨c.toMatrix (Pi.basisFun O (Fin n)), (Pi.basisFun O (Fin n)).toMatrix b, ?_, ?_, fun i j hij => ?_⟩
  · exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  · exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  · have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b (Pi.basisFun O (Fin n))
      c (Pi.basisFun O (Fin n)) (Matrix.toLin' A)
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at h
    rw [h, LinearMap.toMatrix_apply]
    exact hbc i j hij

theorem smithPairing (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K) :
    ∃ P Q : Matrix (Fin n) (Fin n) O, IsUnit P.det ∧ IsUnit Q.det ∧
      ∀ i j, i ≠ j → (P.map (algebraMap O K) * G * Q.map (algebraMap O K)) i j = 0 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => G p.1 p.2)
  have hA : ∀ i j, ∃ a : O, algebraMap O K a = (d : O) • G i j := fun i j => by
    obtain ⟨a, ha⟩ := hd (i, j) (Finset.mem_univ _)
    exact ⟨a, ha⟩
  choose A hA using hA
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := smithMatrix n (Matrix.of A)
  refine ⟨P, Q, hP, hQ, fun i j hij => ?_⟩
  have hd0 : algebraMap O K (d : O) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O K), (IsFractionRing.injective O K).eq_iff]
    exact nonZeroDivisors.coe_ne_zero d
  have key : (Matrix.of A).map (algebraMap O K) = algebraMap O K (d : O) • G := by
    ext i j
    simp [hA, Algebra.smul_def]
  have h2 : (P * Matrix.of A * Q).map (algebraMap O K) =
      algebraMap O K (d : O) • (P.map (algebraMap O K) * G * Q.map (algebraMap O K)) := by
    rw [Matrix.map_mul, Matrix.map_mul, key, Matrix.mul_smul, Matrix.smul_mul]
  have h3 := congrFun (congrFun h2 i) j
  rw [Matrix.map_apply, hPQ i j hij, map_zero, Matrix.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3.symm).resolve_left hd0

end Formalism.InvariantFactorPaths.KP
