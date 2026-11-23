import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.CyclicVector

theorem exists_ne_zero_aeval_mulVec_eq_zero {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (p : K[X]) (hp : Irreducible p) (hd : p ∣ γ.charpoly) :
    ∃ w : Fin n → K, w ≠ 0 ∧ aeval γ p *ᵥ w = 0 := by
  classical
  apply Matrix.exists_mulVec_eq_zero_iff.2
  have : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let f := (Algebra.ofId K L).mapMatrix (m := Fin n)
  let M' : Matrix (Fin n) (Fin n) L := γ.map (algebraMap K L)
  have hf : f (aeval γ p) = aeval M' p := (Polynomial.aeval_algHom_apply f γ p).symm
  have hroot : M'.charpoly.IsRoot (AdjoinRoot.root p) := by
    rw [Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hd
  have hs : AdjoinRoot.root p ∈ spectrum L M' := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval M' (p.map (algebraMap K L)) ⟨_, hs, rfl⟩
  rw [aeval_map_algebraMap] at h2
  have h0 : eval (AdjoinRoot.root p) (p.map (algebraMap K L)) = 0 := by
    rw [eval_map, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  beta_reduce at h2
  rw [h0, spectrum.zero_mem_iff] at h2
  have h3 : (aeval M' p).det = 0 := by
    by_contra hne
    exact h2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne))
  have h4 : (algebraMap K L) (aeval γ p).det = 0 := by
    rw [RingHom.map_det, ← h3, ← hf]
    rfl
  exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h4

theorem exists_vector_annihilator_dvd {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v : Fin n → K, ∀ h : K[X], aeval γ h *ᵥ v = 0 → γ.charpoly ∣ h := by
  classical
  set χ := γ.charpoly with hχ
  have hχ0 : χ ≠ 0 := (Matrix.charpoly_monic γ).ne_zero
  have hsq : Squarefree χ := hs.squarefree
  let S : Finset K[X] := (UniqueFactorizationMonoid.normalizedFactors χ).toFinset
  have hSirr : ∀ p ∈ S, Irreducible p := fun p hp =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p (Multiset.mem_toFinset.1 hp)
  have hSdvd : ∀ p ∈ S, p ∣ χ := fun p hp =>
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hp)
  have hw : ∀ p : K[X], ∃ w : Fin n → K, p ∈ S → w ≠ 0 ∧ aeval γ p *ᵥ w = 0 := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨w, h1, h2⟩ := exists_ne_zero_aeval_mulVec_eq_zero γ p (hSirr p hp) (hSdvd p hp)
      exact ⟨w, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose w hw using hw
  refine ⟨∑ p ∈ S, w p, fun h hh => ?_⟩

  have key : ∀ p ∈ S, p ∣ h := by
    intro p hp
    obtain ⟨q, hq⟩ := hSdvd p hp
    have hpi := hSirr p hp
    have hpq : ¬ p ∣ q := by
      rintro ⟨r, rfl⟩
      exact hpi.not_isUnit (hsq p ⟨r, by rw [hq]; ring⟩)
    have hother : ∀ p' ∈ S, p' ≠ p → aeval γ q *ᵥ w p' = 0 := by
      intro p' hp' hne
      have hd : p' ∣ q := by
        have h1 : p' ∣ p * q := hq ▸ hSdvd p' hp'
        rcases (hSirr p' hp').prime.dvd_or_dvd h1 with h2 | h2
        · exfalso
          apply hne
          have hass : Associated p' p := (hSirr p' hp').associated_of_dvd hpi h2
          have e1 := UniqueFactorizationMonoid.normalize_normalized_factor p' (Multiset.mem_toFinset.1 hp')
          have e2 := UniqueFactorizationMonoid.normalize_normalized_factor p (Multiset.mem_toFinset.1 hp)
          rw [← e1, ← e2]
          exact normalize_eq_normalize_iff.2 ⟨hass.dvd, hass.symm.dvd⟩
        · exact h2
      obtain ⟨r, rfl⟩ := hd
      rw [mul_comm p' r, map_mul, ← Matrix.mulVec_mulVec, (hw p' hp').2, Matrix.mulVec_zero]
    have hqv : aeval γ q *ᵥ (∑ p' ∈ S, w p') = aeval γ q *ᵥ w p := by
      rw [Matrix.mulVec_sum, Finset.sum_eq_single_of_mem p hp]
      intro p' hp' hne
      exact hother p' hp' hne
    have hker : aeval γ (h * q) *ᵥ w p = 0 := by
      rw [map_mul, ← Matrix.mulVec_mulVec, ← hqv, Matrix.mulVec_mulVec, ← map_mul, mul_comm h q,
        map_mul, ← Matrix.mulVec_mulVec, hh, Matrix.mulVec_zero]
    by_contra hph
    have hcop : IsCoprime p (h * q) :=
      (hpi.coprime_iff_not_dvd.2 hph).mul_right (hpi.coprime_iff_not_dvd.2 hpq)
    obtain ⟨a, b, hab⟩ := hcop
    apply (hw p hp).1
    have hval := congrArg (fun t => aeval γ t *ᵥ w p) hab
    simp only [map_add, map_mul, map_one, Matrix.one_mulVec, Matrix.add_mulVec] at hval
    rw [← hval, ← Matrix.mulVec_mulVec, (hw p hp).2, ← Matrix.mulVec_mulVec (M := aeval γ b),
      ← map_mul, hker]
    simp
  by_cases hh0 : h = 0
  · simp [hh0]
  have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hχ0).1 hsq
  refine (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hχ0 hh0).2
    ((Multiset.le_iff_subset hnd).2 fun p hp => ?_)
  have hpS : p ∈ S := Multiset.mem_toFinset.2 hp
  have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor p hp
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hh0).2 ⟨hSirr p hpS, hnorm, key p hpS⟩

theorem exists_cyclic_vector : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K),
    γ.charpoly.Separable → ∃ v : Fin n → K, ∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v := by
  intro K _ n γ hs
  obtain ⟨v, hv⟩ := exists_vector_annihilator_dvd γ hs
  refine ⟨v, ?_⟩
  let T : K[X] →ₗ[K] (Fin n → K) :=
    { toFun := fun h => aeval γ h *ᵥ v
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  let F : (Fin n → K) →ₗ[K] (Fin n → K) :=
    T ∘ₗ (degreeLT K n).subtype ∘ₗ (degreeLTEquiv K n).symm.toLinearMap
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hd : γ.charpoly ∣ (((degreeLTEquiv K n).symm c : degreeLT K n) : K[X]) := hv _ hc
    have hdeg : (((degreeLTEquiv K n).symm c : degreeLT K n) : K[X]).degree < γ.charpoly.degree := by
      rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
      exact Polynomial.mem_degreeLT.1 ((degreeLTEquiv K n).symm c).2
    have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt hd hdeg
    have h1 : (degreeLTEquiv K n).symm c = 0 := Subtype.ext h0
    simpa using h1
  have hsurj : Function.Surjective F := LinearMap.injective_iff_surjective.1 hinj
  intro y
  obtain ⟨c, hc⟩ := hsurj y
  exact ⟨_, hc.symm⟩

end GlobalTheory.CompanionTheory.TorusCh.CyclicVector
