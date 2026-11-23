import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwDcosFin

theorem finite_image_mk_of_isCompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsOpen (H : Set G)) {C : Set G} (hC : IsCompact C) :
    ((QuotientGroup.mk : G → G ⧸ H) '' C).Finite := by
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun g : G => (fun x => g * x) '' (H : Set G))
    (fun g => (Homeomorph.mulLeft g).isOpenMap _ hH)
    (fun x _ => Set.mem_iUnion.2 ⟨x, 1, H.one_mem, mul_one x⟩)
  refine (s.finite_toSet.image (QuotientGroup.mk : G → G ⧸ H)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hy⟩ : ∃ g ∈ s, g⁻¹ * x ∈ H := by
    simpa using hs hx
  exact ⟨g, hg, QuotientGroup.eq.2 hy⟩

theorem dcos_finite_support_iwGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : ℕ) (t : GLw a w),
    (Function.support fun q : GLw a w ⧸ iwGL a w => dcos a w t q.out).Finite ∧ IsOpen (iwGL a w : Set (GLw a w)) ∧
      IsCompact (iwGL a w : Set (GLw a w)) ∧ iwGL a w ≤ GlobalTheory.LFun.KGL w a ∧
      (iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) ≠ 0 := by
  intro E _ _ _ w a t
  have hIo : IsOpen (iwGL a w : Set (GLw a w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin a)
  have hIc : IsCompact (iwGL a w : Set (GLw a w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin a)
  refine ⟨?_, hIo, hIc, GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w a,
    GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hIo (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a)⟩
  refine (finite_image_mk_of_isCompact hIo (GlobalTheory.CompanionTheory.IwFacts.isCompact_support_dcos w a t)).subset ?_
  intro q hq
  exact ⟨q.out, hq, QuotientGroup.out_eq' q⟩

end GlobalTheory.CompanionTheory.IwDcosFin
