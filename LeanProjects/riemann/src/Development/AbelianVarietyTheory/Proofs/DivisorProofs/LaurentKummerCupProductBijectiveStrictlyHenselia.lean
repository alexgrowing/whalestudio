import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsCohomologyBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassZeroOfGeometricPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentEqualizerDegreeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassFromIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfNoetherianCase
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.GmPhiBij

theorem inj (q : ℕ) [NeZero q] (R : Type) [CommRing R] (hq : IsUnit (q : R)) (i : ℤ) : Function.Injective (gmPhi q R i) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine GlobalTheory.T.class_zero_of_geometric_points q R hq (i - 1) a fun K _ _ f => ?_
  have hqK : IsUnit (q : K) := by simpa using hq.map f
  have hK : AIC K := fun p _ hd => IsAlgClosed.exists_root p (Polynomial.natDegree_pos_iff_degree_pos.mp hd).ne'
  apply (GlobalTheory.T.units_cohomology_bijective q K hK hqK i).1
  rw [map_zero, ← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q f hq, ha, map_zero]

theorem surj_noeth (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A] (hA : SH A) (hq : IsUnit (q : A)) (i : ℤ) :
    Function.Surjective (gmPhi q A i) := by
  intro x
  obtain ⟨A', _, _, hint, hker, a', ha'⟩ := GlobalTheory.T.laurent_class_from_integral q A hA hq i x
  have hq' : IsUnit (q : A') := by simpa using hq.map (algebraMap A A')
  set L := (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom with hLdef
  set R := (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom with hRdef
  have hLR : L.comp (algebraMap A A') = R.comp (algebraMap A A') := by
    refine RingHom.ext fun a => ?_
    change (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a) =
      (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a)
    rw [AlgHom.commutes, AlgHom.commutes]
  have hq2 : IsUnit (q : A' ⊗[A] A') := by simpa using hq'.map L
  have heq : pull _ (spMap L) _ 0 a' = pull _ (spMap R) _ 0 a' := by
    apply inj q _ hq2 i
    rw [← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q L hq', ← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q R hq', ← ha', ← GmPhiNat.pull_spMap_comp,
      ← GmPhiNat.pull_spMap_comp, ← GmPhiNat.laurentMap_comp, ← GmPhiNat.laurentMap_comp, hLR]
  obtain ⟨a, ha⟩ := GlobalTheory.T.descent_equalizer_degree_zero q A A' hint hker hq (i - 1) a' heq
  refine ⟨a, ?_⟩
  have hsub : gmPhi q A i a - x = 0 := by
    apply GlobalTheory.T.laurent_cohomology_injective q A A' hint hker hq (fun j => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) 1 one_pos) i
    rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q (algebraMap A A') hq, ha, ha', sub_self]
  exact sub_eq_zero.mp hsub

end GmPhiBij

theorem gmPhi_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
    Function.Bijective (gmPhi q A i) := by
  intro q _ A _ hA hq i
  exact ⟨GmPhiBij.inj q A hq i, GlobalTheory.T.surjective_of_noetherian_case q (fun B _ _ hB hqB j => GmPhiBij.surj_noeth q B hB hqB j) A hA hq i⟩

end GlobalTheory.EtC

end
