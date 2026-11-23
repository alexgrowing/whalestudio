import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselianStatement
open IsLocalRing Polynomial

namespace GlobalTheory.StrictHensel

theorem henselian_of_sections {R : Type} [CommRing R] [IsLocalRing R]
    (H : ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime],
      q.comap (algebraMap R A) = maximalIdeal R →
        ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) :
    HenselianLocalRing R := by
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  let P : StandardEtalePair R := ⟨f, hf, derivative f, 1, 0, 1, by simp⟩
  have e : ∀ p : R[X], aeval (residue R a₀) p = residue R (p.eval a₀) := fun p => by
    rw [← ResidueField.algebraMap_eq]; exact aeval_algebraMap_apply_eq_algebraMap_eval _ _
  have hP : P.HasMap (residue R a₀) := by
    refine ⟨?_, ?_⟩
    · change aeval (residue R a₀) f = 0
      rw [e]; exact (residue_eq_zero_iff _).mpr h₁
    · change IsUnit (aeval (residue R a₀) (derivative f))
      rw [e]; exact h₂.map (residue R)
  let ψ := P.lift (residue R a₀) hP
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hq : (RingHom.ker ψ).comap (algebraMap R P.Ring) = maximalIdeal R := by
    ext r
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, ResidueField.algebraMap_eq,
      residue_eq_zero_iff]
  obtain ⟨s, hs⟩ := H P.Ring (RingHom.ker ψ) hq
  refine ⟨s P.X, ?_, ?_⟩
  · have h := (P.hasMap_X.map s).1
    simpa [P, IsRoot, coe_aeval_eq_eval] using h
  · have hmem : P.X - algebraMap R P.Ring a₀ ∈ RingHom.ker ψ := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, ResidueField.algebraMap_eq]
      simp [ψ]
    rw [← hs, Ideal.mem_comap] at hmem
    simpa using hmem

theorem isSepClosed_of_sections {R : Type} [CommRing R] [IsLocalRing R]
    (H : ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime],
      q.comap (algebraMap R A) = maximalIdeal R →
        ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) :
    IsSepClosed (ResidueField R) := by
  refine IsSepClosed.of_exists_root _ fun g hm hirr hsep => ?_
  obtain ⟨f, hf, -, hfm⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts g).2 (map_surjective _ residue_surjective g)) hm
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  let P : StandardEtalePair R := ⟨f, hfm, derivative f, 1, 0, 1, by simp⟩
  have e : ∀ p : R[X], aeval (AdjoinRoot.root g) p =
      AdjoinRoot.mk g (p.map (residue R)) := fun p => by
    rw [← AdjoinRoot.aeval_eq, ← ResidueField.algebraMap_eq, aeval_map_algebraMap]
  have hP : P.HasMap (AdjoinRoot.root g) := by
    refine ⟨?_, ?_⟩
    · change aeval (AdjoinRoot.root g) f = 0
      rw [e, hf, AdjoinRoot.mk_self]
    · change IsUnit (aeval (AdjoinRoot.root g) (derivative f))
      rw [e, ← derivative_map, hf, isUnit_iff_ne_zero, Ne, AdjoinRoot.mk_eq_zero]
      rintro ⟨c, hc⟩
      obtain ⟨a, b, hab⟩ := hsep
      exact hirr.not_isUnit (isUnit_of_dvd_one ⟨a + b * c, by rw [← hab, hc]; ring⟩)
  let ψ := P.lift (AdjoinRoot.root g) hP
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hq : (RingHom.ker ψ).comap (algebraMap R P.Ring) = maximalIdeal R := by
    ext r
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply R (ResidueField R) (AdjoinRoot g),
      map_eq_zero_iff _ (algebraMap (ResidueField R) (AdjoinRoot g)).injective,
      ResidueField.algebraMap_eq, residue_eq_zero_iff]
  obtain ⟨s, -⟩ := H P.Ring (RingHom.ker ψ) hq
  have ha : f.eval (s P.X) = 0 := by
    have h := (P.hasMap_X.map s).1
    simpa [P, coe_aeval_eq_eval] using h
  exact ⟨residue R (s P.X), by rw [← hf, eval_map, eval₂_hom, ha, map_zero]⟩

end GlobalTheory.StrictHensel

namespace GlobalTheory.StrictHensel

theorem sections_of_henselian_sepClosed {R : Type} [CommRing R] [IsLocalRing R]
    [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime]
    (hq : q.comap (algebraMap R A) = maximalIdeal R) :
    ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q := by
  let S := Localization.AtPrime q
  haveI : IsLocalHom (algebraMap R S) := ⟨fun r hr => by
    rw [IsScalarTower.algebraMap_apply R A S, IsLocalization.AtPrime.isUnit_to_map_iff S q] at hr
    exact (notMem_maximalIdeal).mp fun h => hr (by
      have : r ∈ q.comap (algebraMap R A) := hq ▸ h
      exact this)⟩
  haveI : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.comp R A S
  haveI : Algebra.EssFiniteType R S := Algebra.EssFiniteType.comp R A S
  have hsurj := IsSepClosed.algebraMap_surjective (ResidueField R) (ResidueField S)
  let e : ResidueField R ≃ₐ[ResidueField R] ResidueField S :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) ⟨fun a b h => (algebraMap (ResidueField R) (ResidueField S)).injective h, hsurj⟩
  let φ : A →ₐ[R] ResidueField R := ((e.symm.restrictScalars R).toAlgHom).comp
    ((IsScalarTower.toAlgHom R S (ResidueField S)).comp (IsScalarTower.toAlgHom R A S))
  obtain ⟨s, hs⟩ := (GlobalTheory.T.bijective_residue_comp_etale_henselian R A R).2 φ
  refine ⟨s, ?_⟩
  ext x
  have hx := congrArg (fun ψ : A →ₐ[R] ResidueField R => ψ x) hs
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at hx
  rw [Ideal.mem_comap, ← residue_eq_zero_iff, ← ResidueField.algebraMap_eq]
  change algebraMap R (ResidueField R) (s x) = 0 ↔ x ∈ q
  rw [hx]
  simp only [φ, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq]
  change e.symm (residue S (algebraMap A S x)) = 0 ↔ x ∈ q
  rw [map_eq_zero_iff _ e.symm.injective, residue_eq_zero_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff S q]

end GlobalTheory.StrictHensel

namespace GlobalTheory.StrictHensel

theorem strictlyHenselian_iff : ∀ (R : Type) [CommRing R] [IsLocalRing R],
    (∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime],
      q.comap (algebraMap R A) = maximalIdeal R →
        ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) ↔
      (HenselianLocalRing R ∧ IsSepClosed (ResidueField R)) := by
  intro R _ _
  refine ⟨fun H => ⟨henselian_of_sections H, isSepClosed_of_sections H⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  intro A _ _ _ q _ hq
  exact sections_of_henselian_sepClosed A q hq

end GlobalTheory.StrictHensel
