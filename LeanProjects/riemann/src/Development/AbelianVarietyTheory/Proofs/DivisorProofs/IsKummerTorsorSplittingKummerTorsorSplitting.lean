import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEqZeroOfLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafSectionLocallyFiniteCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerRelationBoundaryKernelGeneratorSumZeroStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KummerSplit

theorem exists_comp_eq_of_injective {R : Type} [CommRing R] {A B K : Shv R} [Injective K] (g : A ⟶ B) (φ : A ⟶ K)
    (h : ∀ U (a : Sec A U), Sec.map g a = 0 → Sec.map φ a = 0) : ∃ ψ : B ⟶ K, g ≫ ψ = φ := by
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hS : S.Exact := S.exact_of_f_is_kernel (kernelIsKernel g)
  have hf : S.f ≫ φ = 0 := by
    refine (GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R (S.f ≫ φ)).2.2.2 0 fun U a => ?_
    have h0 : Sec.map g (Sec.map (kernel.ι g) a) = 0 := by
      rw [← sec_map_comp, kernel.condition]; rfl
    change Sec.map φ (Sec.map (kernel.ι g) a) = Sec.map (0 : kernel g ⟶ K) a
    rw [h U _ h0]; rfl
  exact ⟨hS.descToInjective φ hf, hS.comp_descToInjective φ hf⟩

theorem kernel_local (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q))
    (h : (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0) :
    (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := GlobalTheory.T.kummerRelation_boundary_kernel_generator_sum_zero q V c h

theorem exists_isKum (q : ℕ) [NeZero q] : ∃ t, IsKum q t := by
  have hinj : Injective ((res (ZMod q) (tw q 1)).X 0) := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q 1)).2.1 0
  have hu := free_hom_sections (ZMod q) unitsP ((free (ZMod q)).obj unitsP)
  obtain ⟨G, hG⟩ := (free_hom_sections (ZMod q) (tripP q) ((free (ZMod q)).obj unitsP)).1
    (fun U x => freeGen (ZMod q) unitsP U (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP U (unitsP.mk (tripP.get x).src))
    (fun V U g x => by
      rw [res_sub, hu.2.2.1, hu.2.2.1]
      rfl)
  obtain ⟨Φ, hΦ⟩ := (free_hom_sections (ZMod q) (tripP q) ((res (ZMod q) (tw q 1)).X 0)).1
    (fun U x => resGen 1 (tripP.get x).root)
    (fun V U g x => by
      unfold resGen
      rw [sec_res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1]
      rfl)
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_injective G Φ (fun U a ha => by
    apply sec_eq_zero_of_loc
    refine loc_calculus.2.1 U _ _ ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination (ZMod q) (tripP q) U).1 a) ?_
    rintro V g ⟨c, hc⟩
    have hc' := congrArg (Sec.map G) hc
    rw [← sec_res_map, ha, res_zero', smap_sum] at hc'
    rw [sec_res_map, hc, smap_sum]
    simp only [hG] at hc'
    simp only [hΦ]
    exact kernel_local q V c hc'.symm)
  refine ⟨fun U v => Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)), ?_, ?_⟩
  · intro V U g v _
    rw [sec_res_map, hu.2.2.1]
    rfl
  · intro U ζ v w hw
    have e := congrArg (Sec.map ψ) (hG U (tripP.mk ⟨ζ, v, w, hw⟩))
    rw [← sec_map_comp, hψ, hΦ, smap_sub] at e
    change resGen 1 ζ = Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk w)) -
      Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)) at e
    show Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk w)) =
      Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)) + resGen 1 ζ
    rw [e]
    exact (add_sub_cancel _ _).symm

theorem isKum_kumT : ∀ (q : ℕ) [NeZero q], IsKum q (kumT q) := fun q _ => pick_spec (exists_isKum q)

end GlobalTheory.EtC.KummerSplit
