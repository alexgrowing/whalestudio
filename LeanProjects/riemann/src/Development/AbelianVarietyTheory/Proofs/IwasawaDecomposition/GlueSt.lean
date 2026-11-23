import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace GlobalTheory.TorRef

theorem glueSt : GlueSt := by
  intro X X' U Y π j g hred hj hd hY hext
  choose V h hxV hV using hext
  have hsep : IsSeparated (terminal.from Y) := hY.isSeparated_terminal_from
  have compat : ∀ a b, pullback.fst (V a).ι (V b).ι ≫ h a = pullback.snd (V a).ι (V b).ι ≫ h b := by
    intro a b
    let p : pullback (V a).ι (V b).ι ⟶ X' := pullback.fst (V a).ι (V b).ι ≫ (V a).ι
    have hp : pullback.snd (V a).ι (V b).ι ≫ (V b).ι = p := (pullback.condition).symm
    have hopen : IsOpenMap p := p.isOpenEmbedding.isOpenMap
    have hdom : IsDominant (pullback.fst (p ≫ π) j) := by
      refine ⟨?_⟩
      have hr := Scheme.Pullback.range_fst (p ≫ π) j
      have hden : Dense (p ⁻¹' (π ⁻¹' Set.range j)) := hd.preimage hopen
      have he : Set.range (pullback.fst (p ≫ π) j) = p ⁻¹' (π ⁻¹' Set.range j) := by
        rw [hr]
        ext x
        simp
      show Dense (Set.range (pullback.fst (p ≫ π) j))
      rw [he]
      exact hden
    have : AlgebraicGeometry.IsReduced (pullback (V a).ι (V b).ι) := isReduced_of_isOpenImmersion p
    refine ext_of_isDominant_of_isSeparated (terminal.from Y) (terminal.hom_ext _ _)
      (pullback.fst (p ≫ π) j) ?_
    have hqr : pullback.fst (p ≫ π) j ≫ p ≫ π = pullback.snd (p ≫ π) j ≫ j := pullback.condition
    have hA : pullback.fst (V a).ι (V b).ι ≫ (V a).ι ≫ π = p ≫ π := (Category.assoc _ _ _).symm
    have hB : pullback.snd (V a).ι (V b).ι ≫ (V b).ι ≫ π = p ≫ π := by rw [← Category.assoc, hp]
    have h₁ := hV a _ (pullback.fst (p ≫ π) j ≫ pullback.fst (V a).ι (V b).ι) (pullback.snd (p ≫ π) j)
      ((Category.assoc _ _ _).trans ((congrArg (pullback.fst (p ≫ π) j ≫ ·) hA).trans hqr))
    have h₂ := hV b _ (pullback.fst (p ≫ π) j ≫ pullback.snd (V a).ι (V b).ι) (pullback.snd (p ≫ π) j)
      ((Category.assoc _ _ _).trans ((congrArg (pullback.fst (p ≫ π) j ≫ ·) hB).trans hqr))
    exact (Category.assoc _ _ _).symm.trans (h₁.trans (h₂.symm.trans (Category.assoc _ _ _)))
  have hcov : IsOpenCover V :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩
  let 𝒰 := X'.openCoverOfIsOpenCover V hcov
  obtain ⟨G, hι⟩ : ∃ G : X' ⟶ Y, ∀ x, (V x).ι ≫ G = h x :=
    ⟨𝒰.glueMorphisms h compat, fun x => 𝒰.ι_glueMorphisms h compat x⟩
  refine ⟨G, fun T a u hau => ?_⟩
  have hcovT : IsOpenCover (fun x => a ⁻¹ᵁ V x) :=
    eq_top_iff.2 fun t _ => TopologicalSpace.Opens.mem_iSup.2 ⟨a t, hxV (a t)⟩
  refine (T.openCoverOfIsOpenCover _ hcovT).hom_ext _ _ fun (x : X') => ?_
  show (a ⁻¹ᵁ V x).ι ≫ a ≫ G = (a ⁻¹ᵁ V x).ι ≫ u ≫ g
  have hr : (a ∣_ V x) ≫ (V x).ι = (a ⁻¹ᵁ V x).ι ≫ a := morphismRestrict_ι a (V x)
  have h₃ := hV x _ (a ∣_ V x) ((a ⁻¹ᵁ V x).ι ≫ u)
    (by rw [reassoc_of% hr, hau, Category.assoc])
  rw [← reassoc_of% hr, hι x, h₃, Category.assoc]

end GlobalTheory.TorRef
