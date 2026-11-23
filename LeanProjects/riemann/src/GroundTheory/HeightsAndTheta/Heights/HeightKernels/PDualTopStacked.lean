import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopStacked
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopBasisChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSimpleSub
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.ExistsCover
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.ExistsSmulMemHermitianLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

namespace TopDualStacked

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def DegForm (F G : HermLattice K i) : Prop :=
  ∀ (T T' : Type) [Fintype T] [DecidableEq T] [Fintype T'] [DecidableEq T']
    (b : Module.Basis T ℤ (dualLattice F)) (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice G))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine G.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - G.withStdMetric.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

theorem DegForm.trans {F G H : HermLattice K i} (h₁ : DegForm F G) (h₂ : DegForm G H) : DegForm F H := by
  intro T T' _ _ _ _ b hb b' hb' II hi hII
  obtain ⟨S, hS, hdS, ⟨c⟩⟩ := DualLatticeBasisExists.proof K i G
  have hc := DualEmbBijective.proof K i G S c
  have e₂ := h₂ S T' c hc b' hb' II hi hII
  have e₁ := h₁ T S b hb c hc II hi hII
  linarith

theorem degForm_self (hBasis : DualTopBasisChange.Statement) (F : HermLattice K i) : DegForm F F := by
  intro T T' _ _ _ _ b hb b' hb' II hi hII
  have e := hBasis K i F.withStdMetric T T' b hb b' hb' II hi hII
  rw [sub_self, zero_mul, add_zero]
  exact e

theorem withStdMetric_eq {F G : HermLattice K i} (h : F.lattice = G.lattice) :
    F.withStdMetric = G.withStdMetric := by
  cases F
  cases G
  cases h
  rfl

theorem degForm_iff (F G : HermLattice K i) : DegForm F G ↔ DegForm F.withStdMetric G.withStdMetric :=
  Iff.rfl

theorem degForm_of_eq (hBasis : DualTopBasisChange.Statement) {F G : HermLattice K i}
    (h : G.lattice = F.lattice) : DegForm F G := by
  rw [degForm_iff, withStdMetric_eq h]
  exact degForm_self hBasis _

theorem degForm_of_cover (hSimple : DualTopSimpleSub.Statement) {F G : HermLattice K i}
    (hlt : G.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), G.lattice ≤ N → N ≤ F.lattice → N = G.lattice ∨ N = F.lattice) :
    DegForm F G :=
  fun T T' _ _ _ _ b hb b' hb' II hi hII => hSimple K i F G T T' b hb b' hb' II hi hII hlt hcov

theorem exists_smul_mem (X : HermLattice K i) (v : Fin i → K) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ c • v ∈ X.lattice :=
  _root_.GroundTheory.Variant₂.N1.exists_smul_mem_hermitianLattice X v

theorem exists_cover {F X : HermLattice K i} (hlt : X.lattice < F.lattice) :
    ∃ w ∈ F.lattice, w ∉ X.lattice ∧ ∀ N : Submodule (𝓞 K) (Fin i → K), X.lattice ≤ N →
      N ≤ X.lattice ⊔ Submodule.span (𝓞 K) {w} → N = X.lattice ∨ N = X.lattice ⊔ Submodule.span (𝓞 K) {w} :=
  _root_.GroundTheory.Variant₂.N1.exists_cover hlt

def addVector (X : HermLattice K i) (w : Fin i → K) : HermLattice K i where
  lattice := X.lattice ⊔ Submodule.span (𝓞 K) {w}
  fg := X.fg.sup (Submodule.fg_span_singleton w)
  span_eq := eq_top_iff.mpr (X.span_eq ▸ Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left))
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

theorem degForm_of_le (hSimple : DualTopSimpleSub.Statement) (hBasis : DualTopBasisChange.Statement)
    (F G : HermLattice K i) (hle : G.lattice ≤ F.lattice) : DegForm F G := by
  have : IsNoetherian (𝓞 K) F.lattice := isNoetherian_of_fg_of_noetherian _ F.fg
  suffices h : ∀ N : Submodule (𝓞 K) F.lattice, ∀ G : HermLattice K i,
      G.lattice = N.map F.lattice.subtype → DegForm F G by
    refine h (G.lattice.comap F.lattice.subtype) G ?_
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  intro N
  refine WellFoundedGT.induction
    (motive := fun N : Submodule (𝓞 K) F.lattice => ∀ G : HermLattice K i,
      G.lattice = N.map F.lattice.subtype → DegForm F G) N ?_
  intro N IH G hG
  by_cases hGF : G.lattice = F.lattice
  · exact degForm_of_eq hBasis hGF
  have hlt : G.lattice < F.lattice :=
    lt_of_le_of_ne (hG ▸ Submodule.map_subtype_le _ _) hGF
  obtain ⟨w, hwF, hwG, hcov⟩ := exists_cover hlt
  have hG'F : (addVector G w).lattice ≤ F.lattice :=
    sup_le hlt.le ((Submodule.span_singleton_le_iff_mem _ _).mpr hwF)
  have hGG' : G.lattice < (addVector G w).lattice :=
    lt_of_le_of_ne le_sup_left fun h =>
      hwG (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
  have hNG : N = G.lattice.comap F.lattice.subtype := by
    rw [hG, Submodule.comap_map_eq_of_injective F.lattice.injective_subtype]
  have hN : N < (addVector G w).lattice.comap F.lattice.subtype := by
    rw [hNG]
    refine lt_of_le_of_ne (Submodule.comap_mono hGG'.le) fun h => hGG'.ne ?_
    have h2 := congrArg (Submodule.map F.lattice.subtype) h
    rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.mpr hlt.le,
      inf_eq_right.mpr hG'F] at h2
  have h1 : DegForm F (addVector G w) :=
    IH _ hN (addVector G w) (by rw [Submodule.map_comap_subtype, inf_eq_right.mpr hG'F])
  exact h1.trans (degForm_of_cover hSimple hGG' hcov)

end TopDualStacked

open TopDualStacked in

theorem DualTopStacked.proof (hSimple : DualTopSimpleSub.Statement) (hBasis : DualTopBasisChange.Statement)
    (hDeg : DualStackedDegree.Statement) : DualTopStacked.Statement := by
  intro K _ _ i F F' T _ _ b hb b' hb' a II hi hII hle hab
  have e := degForm_of_le hSimple hBasis F F' hle T T b hb b' hb' II hi hII
  rw [hDeg K i F F' T b b' a hle hab] at e
  exact e

end

end GroundTheory.Heights₂.Heights
