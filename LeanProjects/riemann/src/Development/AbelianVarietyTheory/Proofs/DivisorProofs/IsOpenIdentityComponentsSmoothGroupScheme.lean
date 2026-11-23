import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNbhdSectionFibreIsPreirreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSndImageMulMemOpenGroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitComponentMulMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdentityComponentsOfMulInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfLocallyClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableUnderGeneralizationSectionComponentsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.IdCompOpen

theorem isOpen_sectionComponents_of_family (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X)
    (hf : Smooth f) (he : e ≫ f = 𝟙 _) (O : X.Opens → Set X) (hO : ∀ U, IsOpen (O U))
    (h1 : ∀ (U : X.Opens) (y : X), e (f y) ∈ U →
      y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → y ∈ O U)
    (h2 : ∀ (U : X.Opens) (y : X),
      (∀ z ∈ U, f z = f y → z ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) →
      y ∈ O U → y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  classical
  have hfe : ∀ t : S, f (e t) = t := fun t => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  refine GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_local_pieces X _ (GlobalTheory.T.stableUnderGeneralization_section_connectedComponentIn X S f e hf he) ?_
  intro x hx
  obtain ⟨U, V₀, V, I, hV, hs, hU, hI, hirr⟩ := GlobalTheory.T.exists_open_nbhd_section_fiber_isPreirreducible X S f e hf he (f x)
  refine ⟨⟨O U, hO U⟩ ⊓ f ⁻¹ᵁ (V₀ ⊓ e ⁻¹ᵁ U), f ⁻¹ᵁ V, I.image (fun c => f.app V c), ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hV hy.2.1
  · exact ⟨h1 U x hU hx, hs, hU⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
    rw [← Scheme.preimage_basicOpen]
    exact hI d hd
  · intro y hy hJ
    have hpre := hirr (f y) hy.2.1 (fun c hc => by
      have := hJ _ (Finset.mem_image_of_mem _ hc)
      rw [← Scheme.preimage_basicOpen] at this
      exact this)
    refine h2 U y ?_ hy.1
    intro z hz hzy
    have hsub := hpre.isPreconnected.subset_connectedComponentIn
      (x := e (f y)) (F := f ⁻¹' {f y}) ⟨hy.2.2, hfe _⟩ Set.inter_subset_right
    show z ∈ connectedComponentIn (f ⁻¹' {f z}) (e (f z))
    rw [hzy]
    exact hsub ⟨hz, hzy⟩

theorem isOpen_identityComponent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → IsOpen {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G _ hG
  exact isOpen_sectionComponents_of_family G.left S G.hom (η[G]).left hG (Over.w (η[G]))
    (fun U => {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y})
    (GlobalTheory.T.isOpen_snd_image_mul_mem_open_groupScheme S G hG) (GlobalTheory.T.mem_mul_preimage_of_mem_unitComponent S G hG) (GlobalTheory.T.mem_unitComponent_of_mul_mem S G hG)

end GlobalTheory.IdCompOpen
