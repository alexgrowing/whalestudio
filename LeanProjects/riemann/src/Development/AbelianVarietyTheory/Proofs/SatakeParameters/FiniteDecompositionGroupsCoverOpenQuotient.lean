import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.DecCover

theorem main : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (N : Subgroup (G F Ω)), IsOpen (N : Set (G F Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T ∧ ∀ g : G F Ω, ∃ u ∈ T, ∃ A' : ValuationSubring Ω, IsPlaceOver A' u ∧ ∃ x ∈ Dec (F := F) A', ∃ n ∈ N, g = x * n := by
  intro Ω _ F _ _ _ _ v N hN
  classical
  have : IsGalois F Ω := {}
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hN N.one_mem
  have hcheb := fun g : G F Ω =>
    GlobalTheory.Published.cheb_holds F Ω U.toSubgroup U.isOpen U.isNormal' g {v}
  choose u hu _ _ B hB _ σ hσ hσU using hcheb
  have hmem : ∀ g : G F Ω, (σ g)⁻¹ * g ∈ N := by
    intro g
    apply hU
    have h1 := U.isNormal'.conj_mem _ (hσU g) (σ g)⁻¹
    have h2 : (σ g)⁻¹ * (σ g * g⁻¹) * (σ g)⁻¹⁻¹ = ((σ g)⁻¹ * g)⁻¹ := by group
    rw [h2] at h1
    have h3 := U.toSubgroup.inv_mem h1
    rw [inv_inv] at h3
    exact h3
  have hopen : ∀ g : G F Ω, IsOpen {h : G F Ω | (σ g)⁻¹ * h ∈ N} := fun g =>
    hN.preimage (continuous_mul_left _)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun g : G F Ω => {h : G F Ω | (σ g)⁻¹ * h ∈ N}) hopen
    (fun g _ => Set.mem_iUnion.2 ⟨g, hmem g⟩)
  refine ⟨t.image u, ?_, fun g => ?_⟩
  · intro hv
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hv
    exact hu i (by simp [hi])
  · obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ g))
    refine ⟨u i, Finset.mem_image_of_mem u hi, B i, hB i, σ i, (hσ i).1, (σ i)⁻¹ * g, hgi, ?_⟩
    group

end GlobalTheory.DecCover

end
