import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationSplitKaehlerDSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniGeneralMembersNoDerivativeRelationStatement

namespace GlobalTheory

open IsLocalRing

theorem derivation_mem_of_mem_sq {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (δ : Derivation k A A) (q : Ideal A) {x : A} (hx : x ∈ q ^ 2) : δ x ∈ q := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact q.add_mem (q.mul_mem_right _ hm) (q.mul_mem_right _ hn)
  · intro x y hx hy
    rw [map_add]; exact q.add_mem hx hy

theorem residue_algebraMap_eq_zero_iff_mem {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] (q : Ideal A) [q.IsPrime] [IsLocalization.AtPrime R q] (x : A) :
    residue R (algebraMap A R x) = 0 ↔ x ∈ q := by
  rw [residue_eq_zero_iff]
  conv_rhs => rw [← IsLocalization.AtPrime.under_maximalIdeal R q]
  rfl

theorem cotangent_relation_derivation {k A R : Type} [CommRing k] [CommRing A] [Algebra k A]
    (q : Ideal A) [q.IsPrime] [CommRing R] [IsLocalRing R] [Algebra A R]
    [IsLocalization.AtPrime R q]
    (δ : Derivation k A A) {κ : Type} (J : Finset κ) (g : κ → A)
    (hg : ∀ j, algebraMap A R (g j) ∈ maximalIdeal R) (c : κ → ResidueField R)
    (hrel : ∑ j ∈ J, c j • (maximalIdeal R).toCotangent ⟨_, hg j⟩ = 0) :
    ∑ j ∈ J, c j * residue R (algebraMap A R (δ (g j))) = 0 := by
  set ψ : A →+* ResidueField R := (residue R).comp (algebraMap A R) with hψdef
  have hψ : ∀ x, ψ x = 0 ↔ x ∈ q := fun x => residue_algebraMap_eq_zero_iff_mem q x
  have hgq : ∀ j, g j ∈ q := fun j => (hψ _).1 ((residue_eq_zero_iff _).2 (hg j))
  set r : κ → R := fun j => (residue_surjective (c j)).choose with hr
  have hrc : ∀ j, residue R (r j) = c j := fun j => (residue_surjective (c j)).choose_spec
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples q.primeCompl J r
  have hb' : ∀ i ∈ J, ∃ x : A, algebraMap A R x = (b : A) • r i := fun i hi => hb i hi
  choose! a ha using hb'
  have hb0 : ψ b ≠ 0 := fun h => b.2 ((hψ _).1 h)
  have hψa : ∀ j ∈ J, ψ (a j) = ψ b * c j := by
    intro j hj
    simp only [hψdef, RingHom.comp_apply, ha j hj, Algebra.smul_def, map_mul, hrc]
  set y : A := ∑ j ∈ J, a j * g j with hy
  have hyq : y ∈ q := q.sum_mem fun j _ => q.mul_mem_left _ (hgq j)

  have hT : (maximalIdeal R).toCotangent
      (∑ j ∈ J, algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R)) = 0 := by
    rw [map_sum]
    have : ∀ j ∈ J, (maximalIdeal R).toCotangent (algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R))
        = ψ b • (c j • (maximalIdeal R).toCotangent ⟨_, hg j⟩) := by
      intro j hj
      rw [map_smul, smul_smul, ← hψa j hj]
      exact (algebraMap_smul (ResidueField R) (algebraMap A R (a j)) _).symm
    rw [Finset.sum_congr rfl this, ← Finset.smul_sum, hrel, smul_zero]
  rw [Ideal.toCotangent_eq_zero] at hT
  have hcoe : ((∑ j ∈ J, algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R) : maximalIdeal R) : R)
      = algebraMap A R y := by
    simp [hy, Submodule.coe_sum, map_sum, map_mul, Algebra.smul_def]
  rw [hcoe, ← IsLocalization.AtPrime.map_eq_maximalIdeal q R, ← Ideal.map_pow,
    IsLocalization.mem_map_algebraMap_iff q.primeCompl R] at hT
  obtain ⟨⟨x, s⟩, hxs⟩ := hT
  rw [← map_mul, IsLocalization.eq_iff_exists q.primeCompl R] at hxs
  obtain ⟨t, ht⟩ := hxs
  have hz : (t : A) * (y * s) ∈ q ^ 2 := ht ▸ Ideal.mul_mem_left _ _ x.2
  have hδz := (hψ _).2 (derivation_mem_of_mem_sq δ q hz)
  have hs0 : ψ s ≠ 0 := fun h => s.2 ((hψ _).1 h)
  have ht0 : ψ t ≠ 0 := fun h => t.2 ((hψ _).1 h)
  have hy0 : ψ y = 0 := (hψ _).2 hyq
  have hδy : ψ (δ y) = 0 := by
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hy0] at hδz
    simpa [hs0, ht0] using hδz
  have hg0 : ∀ j, ψ (g j) = 0 := fun j => (hψ _).2 (hgq j)
  rw [hy, map_sum, map_sum] at hδy
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hg0, zero_mul, add_zero] at hδy
  rw [Finset.sum_congr rfl (fun j hj => by rw [hψa j hj, mul_assoc]), ← Finset.mul_sum] at hδy
  exact (mul_eq_zero.1 hδy).resolve_left hb0

end GlobalTheory

namespace GlobalTheory
open IsLocalRing

theorem bertini_cotangent_independent : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ), ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (q : Ideal A) [q.IsPrime] (R : Type) [CommRing R] [IsLocalRing R] [Algebra A R] [IsLocalization.AtPrime R q], (∃ p, f p ∉ q) → LinearIndependent (IsLocalRing.ResidueField R) (fun j : {j : Fin M // algebraMap A R (∑ p, u (j, p) • f p) ∈ IsLocalRing.maximalIdeal R} => ((IsLocalRing.maximalIdeal R).toCotangent ⟨_, j.2⟩ : IsLocalRing.CotangentSpace R)) := by
  intro k A _ _ _ _ _ ι _ f M
  obtain ⟨n, δ, ω, hD⟩ := GlobalTheory.T.exists_derivation_split_kaehlerD_smooth k A
  have hC := fun (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι) (h : i₀ ∈ J) =>
    GlobalTheory.T.bertini_general_members_no_derivative_relation k A n δ ω hD f M J i₀ p₀ h
  classical
  let Qf : Finset (Fin M) × Fin M × ι → MvPolynomial (Fin M × ι) k := fun x =>
    if h : x.2.1 ∈ x.1 then (hC x.1 x.2.1 x.2.2 h).choose else 1
  refine ⟨∏ x, Qf x, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro x _
    simp only [Qf]
    split_ifs with h
    · exact (hC _ _ _ h).choose_spec.1
    · exact one_ne_zero
  · intro u hu q _ R _ _ _ _ hp
    obtain ⟨p₀, hp₀⟩ := hp
    rw [map_prod, Finset.prod_ne_zero_iff] at hu
    rw [linearIndependent_iff']
    intro s w hw i₀ hi₀
    by_contra hne
    let ψ : A →+* ResidueField R := (residue R).comp (algebraMap A R)
    letI : Algebra k (ResidueField R) := (ψ.comp (algebraMap k A)).toAlgebra
    let φ : A →ₐ[k] ResidueField R := { ψ with commutes' := fun _ => rfl }
    let J : Finset (Fin M) := s.map (Function.Embedding.subtype _)
    let c : Fin M → ResidueField R := fun j =>
      if h : algebraMap A R (∑ p, u (j, p) • f p) ∈ maximalIdeal R then w ⟨j, h⟩ / w i₀ else 0
    have hJ : i₀.1 ∈ J := Finset.mem_map_of_mem _ hi₀
    have hx := hu (J, i₀.1, p₀) (Finset.mem_univ _)
    simp only [Qf, dif_pos hJ] at hx
    refine (hC J i₀.1 p₀ hJ).choose_spec.2 u hx (ResidueField R) φ c ?_ ?_ ?_ ?_
    · exact fun h => hp₀ ((residue_algebraMap_eq_zero_iff_mem q _).1 h)
    · show c i₀.1 = 1
      rw [show c i₀.1 = w i₀ / w i₀ from dif_pos i₀.2]
      exact div_self hne
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hi
      exact (residue_eq_zero_iff _).2 j.2
    · intro l
      have hrel : ∑ j ∈ s, (w j / w i₀) •
          (maximalIdeal R).toCotangent ⟨_, j.2⟩ = 0 := by
        simp_rw [div_eq_mul_inv, mul_comm _ (w i₀)⁻¹, mul_smul]
        rw [← Finset.smul_sum, hw, smul_zero]
      have key := cotangent_relation_derivation q (δ l) s
        (fun j => ∑ p, u (j.1, p) • f p) (fun j => j.2) (fun j => w j / w i₀) hrel
      rw [Finset.sum_map]
      convert key using 2 with j hj
      show c j.1 * φ _ = _
      rw [show c j.1 = w j / w i₀ from dif_pos j.2]
      rfl

end GlobalTheory
