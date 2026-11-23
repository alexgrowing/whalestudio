import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCompletionResidueEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFiniteOfQuasiFiniteCompleteLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLeOfIsEtaleCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalGaloisCoverOfFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivSubMemMaximalIdealOfPurelyInsepResidueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QFEtale

theorem isEtaleCompletion_of_galRigid : ∀ (O R : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (f : O →+* R) [IsLocalHom f], IsAdicComplete (maximalIdeal R) R → (∀ p : Ideal R, p.IsPrime → (maximalIdeal O).map f ≤ p → p = maximalIdeal R) → ((residue R).comp f).Finite → ringKrullDim O ≤ ringKrullDim R → GalRigid f → IsEtaleCompletion f ∧ ((residue R).comp f).FormallyUnramified := by
  intro O R _ _ _ _ _ _ _ _ _ _ f _ hRc hqf hfin hdim hrig
  haveI hOn : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  letI : Algebra (ResidueField O) (ResidueField R) := (ResidueField.map f).toAlgebra
  have hres : (residue R).comp f = (ResidueField.map f).comp (residue O) := by
    ext o; simp [ResidueField.map_residue]
  have hfin' : (ResidueField.map f).Finite := by
    rw [hres] at hfin; exact RingHom.Finite.of_comp_finite hfin
  haveI : Module.Finite (ResidueField O) (ResidueField R) := hfin'
  let M := separableClosure (ResidueField O) (ResidueField R)
  let m : ResidueField O →+* M := algebraMap (ResidueField O) M
  have hmf : m.Finite := RingHom.finite_algebraMap.2 inferInstance
  haveI : Algebra.IsSeparable (ResidueField O) M := inferInstance
  haveI : Algebra.FormallyUnramified (ResidueField O) M := Algebra.FormallyUnramified.of_isSeparable _ _
  have hmu : m.FormallyUnramified := RingHom.formallyUnramified_algebraMap.2 inferInstance
  obtain ⟨A, _, _, _, ψ, hψl, E, hAcn, hψe, hψu, hE⟩ := GlobalTheory.T.exists_etaleCompletion_with_residueField_equiv O M m hmf hmu
  obtain ⟨hAn, hAi, hAc, hA0⟩ := hAcn
  let u' : A →+* ResidueField R := (algebraMap M (ResidueField R)).comp ((E.symm : ResidueField A →+* M).comp (residue A))
  have hu' : ∀ a, u' a = 0 ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← residue_eq_zero_iff]
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, map_eq_zero_iff _ (algebraMap M (ResidueField R)).injective,
      map_eq_zero_iff _ E.symm.injective]
  have hker : RingHom.ker u' = maximalIdeal A := by ext a; exact hu' a
  have hc : (residue R).comp f = u'.comp ψ := by
    ext o
    have h1 := RingHom.congr_fun hE (residue O o)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ResidueField.map_residue] at h1
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, ← h1, RingEquiv.symm_apply_apply, m]
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  obtain ⟨b, hb1, hb2⟩ := GlobalTheory.EtaleCompletionLift.exists_extension O A R (ResidueField R) ψ f u' (residue R) hψe hψu hRc
    inferInstance hker (ker_residue) hc (fun r => residue_surjective _)
  have hbm : ∀ a, b a ∈ maximalIdeal R ↔ a ∈ maximalIdeal A := by
    intro a
    rw [← residue_eq_zero_iff, ← hu', ← RingHom.comp_apply, hb2]
  haveI hbl : IsLocalHom b := ⟨fun a ha => by
    by_contra h
    exact (mem_maximalIdeal _).1 ((hbm a).2 ((mem_maximalIdeal a).2 h)) ha⟩
  have hbfin : b.Finite := by
    refine GlobalTheory.T.ringHom_finite_of_quasiFinite_complete_local A R b hAc (fun p hp h => hqf p hp ?_) ?_
    · rw [← hb1, ← Ideal.map_map, hψe.2.1]; exact h
    · refine RingHom.Finite.of_comp_finite (f := ψ) ?_
      rw [RingHom.comp_assoc, hb1]; exact hfin
  have hbinj : Function.Injective b := GlobalTheory.T.injective_of_finite_of_ringKrullDim_le' A R b hbfin ((GlobalTheory.T.ringKrullDim_le_of_isEtaleCompletion' O A ψ hψe).trans hdim)
  obtain ⟨R', _, _, _, θ, hR'cn, hθl, hθi, hθf, hfix⟩ := GlobalTheory.T.exists_completeNormal_galois_cover_of_finite A R b ⟨hAn, hAi, hAc, hA0⟩ hbfin hbinj
  let q := ringExpChar M
  haveI : ExpChar M q := ringExpChar.expChar M
  haveI : ExpChar (ResidueField R) q := expChar_of_injective_algebraMap (algebraMap M (ResidueField R)).injective q
  have hpi : ∀ x : ResidueField R, ∃ n : ℕ, ∃ a : A, x ^ q ^ n = residue R (b a) := by
    intro x
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem M q x
    obtain ⟨a, ha⟩ := residue_surjective (E y)
    refine ⟨n, a, ?_⟩
    rw [← RingHom.comp_apply, hb2, ← hy]
    simp only [u', RingHom.comp_apply, RingEquiv.coe_toRingHom, ha, RingEquiv.symm_apply_apply]
  have hbsurj : Function.Surjective b := by
    intro r
    refine hfix r fun σ hσ hσb => hrig R' θ σ hR'cn hθi hθf hσ (fun o => ?_) (fun r => GlobalTheory.T.ringEquiv_sub_mem_maximalIdeal_of_purelyInsep_residue A R R' b θ q σ hpi hσb r) r
    rw [← hb1]; exact hσb (ψ o)
  have hmapsurj : Function.Surjective (ResidueField.map b) := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hbsurj r
    exact ⟨residue A a, ResidueField.map_residue _ _⟩
  have hres2 : (residue R).comp f = (ResidueField.map b).comp ((residue A).comp ψ) := by
    rw [← hb1]; ext o; simp [ResidueField.map_residue]
  refine ⟨⟨?_, ?_, hfin⟩, ?_⟩
  · rw [← hb1]; exact RingHom.Flat.comp hψe.1 (RingHom.Flat.of_bijective ⟨hbinj, hbsurj⟩)
  · rw [← hb1, ← Ideal.map_map, hψe.2.1]; exact map_maximalIdeal_of_surjective b hbsurj
  · rw [hres2]; exact RingHom.FormallyUnramified.comp hψu (RingHom.FormallyUnramified.of_surjective hmapsurj)

end GlobalTheory.QFEtale
