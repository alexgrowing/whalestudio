import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen

theorem mem_regAt_genPt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) := by
  obtain ⟨g, hg⟩ := hξ.bij.2 a
  refine ⟨g, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  show (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
    Scheme.stalkClosedPointTo ξ).hom g = a
  rw [e]
  exact hg

theorem exists_open_forall_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (S : Finset Ω) :
    ∃ W : X.Opens, genPt ξ ∈ W ∧ ∀ q : Cpt ξ, q.1 ∈ W → ∀ a ∈ S, a ∈ regAt ξ q := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, fun _ _ _ h => absurd h (Finset.notMem_empty _)⟩
  | insert a S _ ih =>
    obtain ⟨W, hW, H⟩ := ih
    obtain ⟨U, hU, HU⟩ := exists_open_mem_regAt ξ ⟨genPt ξ, specializes_rfl⟩ a (mem_regAt_genPt hξ a)
    refine ⟨W ⊓ U, ⟨hW, hU⟩, fun q hq c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact HU q hq.2
    · exact H q hq.1 c hc

theorem span_regAt_le {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (q : Cpt ξ) (b e : Fin r → E) (M : Fin r → Fin r → Ω)
    (hM : ∀ i, ∑ j, M i j • e j = b i) (hreg : ∀ i j, M i j ∈ regAt ξ q) :
    Submodule.span (regAt ξ q) (Set.range b) ≤ Submodule.span (regAt ξ q) (Set.range e) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [← hM i]
  refine sum_mem fun j _ => ?_
  exact Submodule.smul_mem _ (⟨M i j, hreg i j⟩ : regAt ξ q) (Submodule.subset_span ⟨j, rfl⟩)

theorem isFrameAt_near_genPt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E) (b : Fin r → E), IsCptGen ξ → (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) ∈ T → L.IsVBOn T r V → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = V → ∃ W : X.Opens, genPt ξ ∈ W ∧ ∀ q ∈ T, q.1 ∈ W → L.IsFrameAt b q := by
  classical
  intro X Ω _ ξ E _ _ L T r V b hξ hT hVB hb hspan
  obtain ⟨U, hU, e, he, hfr⟩ := hVB _ hT
  have hbe : ∀ i, ∃ c : Fin r → Ω, ∑ j, c j • e j = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (he ▸ hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  have heb : ∀ i, ∃ c : Fin r → Ω, ∑ j, c j • b j = e i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hspan ▸ he ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose M hM using hbe
  choose N hN using heb
  let S : Finset Ω := Finset.univ.image (fun ij : Fin r × Fin r => M ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin r × Fin r => N ij.1 ij.2)
  obtain ⟨W, hW, H⟩ := exists_open_forall_mem_regAt hξ S
  refine ⟨U ⊓ W, ⟨hU, hW⟩, fun q hq hqW => ⟨hb, ?_⟩⟩
  have hMr : ∀ i j, M i j ∈ regAt ξ q := fun i j => H q hqW.2 _
    (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hNr : ∀ i j, N i j ∈ regAt ξ q := fun i j => H q hqW.2 _
    (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))
  rw [(hfr q hq hqW.1).2]
  exact le_antisymm (span_regAt_le q e b N hN hNr) (span_regAt_le q b e M hM hMr)

end GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen
