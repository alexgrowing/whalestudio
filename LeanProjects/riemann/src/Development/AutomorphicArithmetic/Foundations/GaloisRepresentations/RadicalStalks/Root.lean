import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OneLeft
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Transl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FromSpecEv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobRootMor
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RootMor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.root :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ : k →+* k), Function.Bijective σ → ∀ (ψ : A.left ⟶ A.left) (m : SMor A σ ψ), (∀ x ∈ PrimitiveSubmodule A, m.pull x = 0) →
      ∃ (σ' : k →+* k) (ψ' : A.left ⟶ A.left), Function.Bijective σ' ∧ SMor A σ' ψ' ∧ (∀ x, σ' x ^ p = σ x) ∧ GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ ψ' = ψ := by
  intro p _ k _ _ hk A _ _ hab σ hσ ψ m hm
  haveI : IsAbelianScheme A := hab
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hk
  haveI : AlgebraicGeometry.IsIntegral A.left := GlobalTheory.isIntegral_left_of_isAbelianScheme_field A hab
  haveI : Smooth A.hom := IsAbelianScheme.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k A hab
  have hLie : LieExact A := (GlobalTheory.abelianDeRham.2.1 k A g hab hg).1
  have hT : ∀ v : epsR k ⟶ A, IsTangent v → IsConst (v.left ≫ ψ) := by
    intro v hv
    refine (tan k A hab σ ψ m hσ.2 v hv).mp ?_
    intro f hf
    obtain ⟨h, hh⟩ := hLie.2 v hv
    have hcl : Form.cl _ ((GrpMor.isMor m).pullForm f) = 0 := by
      rw [IsMor.cl_pullForm]
      have hF : (⟨Form.cl _ f, hf⟩ : primDR A) ∈ PrimitiveSubmodule A := by
        show Form.cl _ f ∈ F1 _
        rw [hodgeFiltration_eq_range]
        exact ⟨f, rfl⟩
      exact congrArg Subtype.val (hm _ hF)
    have hmem : Form.cl _ ((GrpMor.isMor m).pullForm f) ∈ primDR A := hcl ▸ (primDR A).zero_mem
    rw [← hh.2 _ hmem]
    have he : (⟨Form.cl _ ((GrpMor.isMor m).pullForm f), hmem⟩ : primDR A) = 0 := Subtype.ext hcl
    rw [he]
    exact map_zero h
  have hall := transl k A σ ψ m hT
  have hroot := dzero p k hk A.left A.left A.hom ψ (fun v hv => hall (Over.homMk v hv))
  obtain ⟨ψ', hψ'⟩ := root0 p A.left A.left (cast_left p k hk A) ψ hroot
  refine ⟨((frobeniusEquiv k p).symm : k →+* k).comp σ, ψ', ?_, ?_, ?_, hψ'⟩
  · exact (frobeniusEquiv k p).symm.bijective.comp hσ
  · exact rootMor p k hk A hab σ _ ψ ψ' m (fun x => frobeniusEquiv_symm_pow_p k p (σ x)) hψ'
  · exact fun x => frobeniusEquiv_symm_pow_p k p (σ x)
