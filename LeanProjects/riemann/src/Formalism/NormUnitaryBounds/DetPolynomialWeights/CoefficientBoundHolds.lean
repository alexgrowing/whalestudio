import Formalism.NormUnitaryBounds.Statement

open Module

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

lemma addVal_prod {ι : Type*} (s : Finset ι) (c : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, c i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

lemma length_quot_zero : Module.length R (R ⧸ Ideal.span ({0} : Set R)) = ⊤ := by
  have := Ring.ord_eq_addVal (R := R) 0
  simpa [Ring.ord] using this

lemma key {ρ : ℕ} (P : Submodule R (Fin ρ → R)) (n : ℕ)
    (hP : Module.length R ((Fin ρ → R) ⧸ P) ≤ n) (ϖ : R) (hϖ : Irreducible ϖ) :
    ∃ G : Matrix (Fin ρ) (Fin ρ) R, (∀ i, G i ∈ P) ∧ G.det ∣ ϖ ^ n := by
  classical
  obtain ⟨n', snf⟩ := P.smithNormalForm (Pi.basisFun R (Fin ρ))
  have hsurj : Function.Surjective snf.f := by
    by_contra h
    obtain ⟨k, hk⟩ : ∃ k, k ∉ Set.range snf.f := by
      simp only [Function.Surjective, not_forall] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by simpa using hk⟩
    let L : (Fin ρ → R) →ₗ[R] R ⧸ Ideal.span ({0} : Set R) :=
      (Ideal.span ({0} : Set R)).mkQ ∘ₗ snf.bM.coord k
    have hle : P ≤ LinearMap.ker L := fun x hx => by
      have := snf.le_ker_coord_of_notMem_range hk hx
      rw [LinearMap.mem_ker] at this ⊢
      simp [L, this]
    have hLs : Function.Surjective (P.liftQ L hle) := by
      intro y
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk (r • snf.bM k), by
        simp [L]; rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]⟩
    have h1 := Module.length_le_of_surjective (P.liftQ L hle) hLs
    rw [length_quot_zero] at h1
    exact absurd (h1.trans hP) (by simp)
  let σ : Fin n' ≃ Fin ρ := Equiv.ofBijective snf.f ⟨snf.f.injective, hsurj⟩
  have hσ : ∀ k, snf.f (σ.symm k) = k := fun k => σ.apply_symm_apply k
  let c : Fin ρ → R := fun k => snf.a (σ.symm k)
  let G : Matrix (Fin ρ) (Fin ρ) R := fun k => (snf.bN (σ.symm k) : Fin ρ → R)
  have hGrow : ∀ k, G k = c k • snf.bM k := fun k => by
    simp only [G, c, snf.snf, hσ]
  refine ⟨G, fun k => (snf.bN (σ.symm k)).2, ?_⟩

  have hdetG : G.det = (∏ k, c k) * (Matrix.of fun k j => snf.bM k j).det := by
    rw [← Matrix.det_mul_column]
    congr 1
    ext k j
    simp [hGrow]
  have hunit : IsUnit (Matrix.of fun k j => snf.bM k j).det := by
    have := (Pi.basisFun R (Fin ρ)).isUnit_det snf.bM
    rw [Basis.det_apply] at this
    have heq : (Matrix.of fun k j => snf.bM k j) = ((Pi.basisFun R (Fin ρ)).toMatrix snf.bM).transpose := by
      ext k j; simp [Basis.toMatrix_apply]
    rw [heq, Matrix.det_transpose]; exact this

  let L : (Fin ρ → R) →ₗ[R] (Π k : Fin ρ, R ⧸ Ideal.span ({c k} : Set R)) :=
    LinearMap.pi fun k => (Ideal.span ({c k} : Set R)).mkQ ∘ₗ snf.bM.coord k
  have hle : P ≤ LinearMap.ker L := fun x hx => by
    rw [LinearMap.mem_ker]
    funext k
    simp only [L, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, Basis.coord_apply]
    have := snf.repr_apply_embedding_eq_repr_smul ⟨x, hx⟩ (i := σ.symm k)
    rw [hσ] at this
    simp only at this
    rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hLs : Function.Surjective (P.liftQ L hle) := by
    intro y
    choose r hr using fun k => Submodule.Quotient.mk_surjective _ (y k)
    refine ⟨Submodule.Quotient.mk (snf.bM.equivFun.symm r), ?_⟩
    funext k
    have hrep : snf.bM.repr (snf.bM.equivFun.symm r) k = r k := by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp only [L, Submodule.liftQ_apply, LinearMap.pi_apply, LinearMap.comp_apply,
      Basis.coord_apply, hrep, Submodule.mkQ_apply, hr]
  have h1 := Module.length_le_of_surjective (P.liftQ L hle) hLs
  rw [Module.length_pi_of_fintype] at h1
  have h2 : IsDiscreteValuationRing.addVal R (∏ k, c k) ≤ IsDiscreteValuationRing.addVal R (ϖ ^ n) := by
    rw [addVal_prod, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp only [nsmul_eq_mul, mul_one]
    refine le_trans (le_of_eq ?_) (h1.trans hP)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Ring.ord_eq_addVal]; rfl
  rw [IsDiscreteValuationRing.addVal_le_iff_dvd] at h2
  rw [hdetG]
  exact (IsUnit.mul_right_dvd hunit).mpr h2

end Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas

namespace Formalism.NormUnitaryCountingLemmas

open Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas in
theorem coefficient_bound_holds : CB := by
  intro R _ _ _ ϖ hϖ S _ _ _ N n hlen I Φ e hΦ ρ φ J
  classical
  let ψ : (Fin ρ → R) →ₗ[R] S := Fintype.linearCombination R φ
  let P : Submodule R (Fin ρ → R) := N.comap ψ
  have hP : Module.length R ((Fin ρ → R) ⧸ P) ≤ n := by
    refine le_trans (Module.length_le_of_injective (P.mapQ N ψ le_rfl) ?_) hlen
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    simp [P]
  obtain ⟨G, hG, c, hc⟩ := key P n hP ϖ hϖ
  let A : Matrix (Fin ρ) (Fin ρ) (FractionRing R) := Matrix.of fun a b => Φ (φ a) (J b)
  have hentry : ∀ i b, ∃ r : R, algebraMap R (FractionRing R) ϖ ^ e *
      ((G.map (algebraMap R (FractionRing R))) * A) i b = algebraMap R (FractionRing R) r := by
    intro i b
    have : ((G.map (algebraMap R (FractionRing R))) * A) i b = Φ (ψ (G i)) (J b) := by
      simp [Matrix.mul_apply, A, ψ, Fintype.linearCombination_apply, map_sum, map_smul,
        Algebra.smul_def]
    rw [this]
    exact hΦ _ (hG i) (J b)
  choose r hr using hentry
  have hϖK : algebraMap R (FractionRing R) ϖ ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]
    exact hϖ.ne_zero
  have hdet : algebraMap R (FractionRing R) ϖ ^ ((ρ : ℤ) * e) *
      ((G.map (algebraMap R (FractionRing R))) * A).det =
        algebraMap R (FractionRing R) (Matrix.of r).det := by
    rw [RingHom.map_det]
    have : (algebraMap R (FractionRing R)).mapMatrix (Matrix.of r) =
        (algebraMap R (FractionRing R) ϖ ^ e) • ((G.map (algebraMap R (FractionRing R))) * A) := by
      ext i b
      simp [← hr i b]
    rw [this, Matrix.det_smul, Fintype.card_fin, ← zpow_natCast, ← zpow_mul, mul_comm e]
  refine ⟨c * (Matrix.of r).det, ?_⟩
  rw [zpow_add₀ hϖK, zpow_natCast, ← map_pow, hc, map_mul, map_mul, ← hdet, Matrix.det_mul,
    RingHom.map_det]
  simp only [RingHom.mapMatrix_apply]
  ring

end Formalism.NormUnitaryCountingLemmas
