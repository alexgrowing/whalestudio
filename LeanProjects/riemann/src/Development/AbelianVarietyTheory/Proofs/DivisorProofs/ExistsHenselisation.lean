import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HensIsLocalRingAndIsLocalHomOfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingHensStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPointedEtaleNeighbourhoodEqMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubMemMaximalIdealPointedEtaleNeighbourhooStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHensStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationInjectiveOfNbhdStatement

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem exists_henselisation : ∀ (R : Type) [CommRing R] [IsLocalRing R], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Function.Bijective (ResidueField.map (algebraMap R S)) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R _ _
  haveI : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R
  obtain ⟨hloc, hofloc⟩ := GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of R
  haveI : HenselianLocalRing (Hens R) := GlobalTheory.T.henselianLocalRing_hens' R
  let ofA : ∀ i : EtNbhd R, i.B →ₐ[R] Hens R := fun i =>
    { toRingHom := Hens.of i, commutes' := GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i }
  have hof_trans : ∀ {i j : EtNbhd R} (h : i ≤ j) (x : i.B),
      Hens.of j (EtNbhd.trans h x) = Hens.of i x := fun h x => Ring.DirectLimit.of_f h x
  have hexists : ∀ s : Hens R, ∃ i b, Hens.of i b = s := fun s => Ring.DirectLimit.exists_of s
  have hlocB : ∀ i : EtNbhd R, IsLocalHom (algebraMap R i.B) := fun i => ⟨fun r hr => by
    by_contra hn
    have hm : algebraMap R i.B r ∈ maximalIdeal i.B := by
      rw [GlobalTheory.T.maximalIdeal_pointedEtaleNeighbourhood_eq_map R i]; exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal r).2 hn)
    exact (mem_maximalIdeal _).1 hm hr⟩
  haveI : IsLocalHom (algebraMap R (Hens R)) := by
    have e : algebraMap R (Hens R) =
        (Hens.of EtNbhd.base).comp (algebraMap R (EtNbhd.base (R := R)).B) := rfl
    rw [e]
    haveI := hlocB EtNbhd.base
    haveI := hofloc EtNbhd.base
    infer_instance
  have hmax : (maximalIdeal R).map (algebraMap R (Hens R)) = maximalIdeal (Hens R) := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit (algebraMap R (Hens R)) r hr
    · intro s hs
      obtain ⟨i, b, rfl⟩ := hexists s
      have hb : b ∈ maximalIdeal i.B := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact (mem_maximalIdeal _).1 hs (hu.map (Hens.of i))
      rw [GlobalTheory.T.maximalIdeal_pointedEtaleNeighbourhood_eq_map R i] at hb
      have hm := Ideal.mem_map_of_mem (Hens.of i) hb
      rwa [Ideal.map_map, show (Hens.of i).comp (algebraMap R i.B) = algebraMap R (Hens R) from
        RingHom.ext (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i)] at hm
  have hres : Function.Bijective (ResidueField.map (algebraMap R (Hens R))) := by
    refine ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨s, rfl⟩ := residue_surjective y
    obtain ⟨i, b, rfl⟩ := hexists s
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_sub_mem_maximalIdeal_pointedEtaleNeighbourhood R i b
    refine ⟨residue R r, ?_⟩
    rw [ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      ← GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i r, ← map_sub]
    exact map_nonunit (Hens.of i) _ hr
  refine ⟨Hens R, inferInstance, inferInstance, inferInstance, inferInstance, GlobalTheory.T.flat_hens' R, hmax, hres,
    EtNbhd R, inferInstance, inferInstance, inferInstance, fun i => (ofA i).range, ?_, ?_, ?_⟩
  · intro i j h y hy
    obtain ⟨x, rfl⟩ := (AlgHom.mem_range _).1 hy
    exact (AlgHom.mem_range _).2 ⟨EtNbhd.trans h x, hof_trans h x⟩
  · intro s
    obtain ⟨i, b, rfl⟩ := hexists s
    exact ⟨i, (AlgHom.mem_range _).2 ⟨b, rfl⟩⟩
  · intro i
    exact ⟨i.A, inferInstance, inferInstance, inferInstance, i.q, inferInstance,
      ⟨AlgEquiv.ofInjective (ofA i) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R i)⟩⟩

end GlobalTheory.Henselisation
