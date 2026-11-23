import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVB

open GlobalTheory.CompanionTheory.Ar.LieTangent

theorem exists_open_forall {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (p : Cpt ξ) {I : Type} [Finite I]
    (P : I → Cpt ξ → Prop) (h : ∀ i, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → P i q) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i, P i q := by
  classical
  have := Fintype.ofFinite I
  have key : ∀ s : Finset I, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i ∈ s, P i q := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨⊤, trivial, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s _ ih =>
      obtain ⟨U, hU, HU⟩ := ih
      obtain ⟨V, hV, HV⟩ := h a
      refine ⟨U ⊓ V, ⟨hU, hV⟩, fun q hq i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact HV q hq.2
      · exact HU q hq.1 i hi
  obtain ⟨U, hU, HU⟩ := key Finset.univ
  exact ⟨U, hU, fun q hq i => HU q hq i (Finset.mem_univ i)⟩

theorem exists_open_mem_span {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] (p : Cpt ξ) {n : ℕ} (w : Fin n → E) (e : E)
    (he : e ∈ Submodule.span (regAt ξ p) (Set.range w)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Submodule.span (regAt ξ q) (Set.range w) := by
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  obtain ⟨U, hU, HU⟩ := exists_open_forall p (fun (j : Fin n) (q : Cpt ξ) => (f j : Ω) ∈ regAt ξ q)
    fun j => exists_open_mem_regAt ξ p _ (f j).2
  refine ⟨U, hU, fun q hq => ?_⟩
  refine Submodule.sum_mem _ fun j _ => ?_
  have : f j • w j = (⟨(f j : Ω), HU q hq j⟩ : regAt ξ q) • w j := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem mem_span_field_of_mem_span_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {E : Type}
    [AddCommGroup E] [Module Ω E] (p : Cpt ξ) {n : ℕ} (w : Fin n → E) (e : E)
    (he : e ∈ Submodule.span (regAt ξ p) (Set.range w)) : e ∈ Submodule.span Ω (Set.range w) := by
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  refine Submodule.sum_mem _ fun j _ => ?_
  have : f j • w j = (f j : Ω) • w j := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isFrameAt_span_and_nhd : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E), M.lat.IsFrameAt b p → Submodule.span Ω (Set.range b) = ⊤ ∧ ∃ N : X.Opens, p.1 ∈ N ∧ ∀ q : Cpt ξ, q.1 ∈ N → M.lat.IsFrameAt b q := by
  intro X G _ _ _ Ω _ ξ E _ _ M p g b hb
  obtain ⟨R, _, x, hx, F, _, _, MR, n, bR, hp⟩ := exists_chart G p.1
  have hgen : genPt ξ ∈ x.opensRange := p.2.mem_open x.opensRange.isOpen hp
  obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
  obtain ⟨c, hli, hsp, hfr⟩ := frame_of_basis x MR bR ξ M φ hφ
  have hc : ∀ q : Cpt ξ, q.1 ∈ x.opensRange → M.lat.IsFrameAt c q := by
    intro q hq
    have hq' : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hq
    obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hq'
    refine hfr q ψ hψ ?_
    have h1 : spMap ((genMap ξ q).comp ψ) ≫ x = spMap φ ≫ x := by
      have e1 : spMap ((genMap ξ q).comp ψ) = spMap (genMap ξ q) ≫ spMap ψ := by
        simp only [spMap, ← Spec.map_comp]
        rfl
      calc spMap ((genMap ξ q).comp ψ) ≫ x = spMap (genMap ξ q) ≫ spMap ψ ≫ x := by
            rw [e1, Category.assoc]
        _ = spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [hψ]
        _ = ξ := spec_genMap ξ q
        _ = spMap φ ≫ x := hφ.symm
    have h2 := Spec.map_injective ((cancel_mono x).1 h1)
    exact congrArg (fun g => g.hom) h2
  have hbc : Submodule.span (regAt ξ p) (Set.range b) = Submodule.span (regAt ξ p) (Set.range c) :=
    hb.2.symm.trans (hc p hp).2
  have hbi : ∀ i, b i ∈ Submodule.span (regAt ξ p) (Set.range c) := fun i => by
    rw [← hbc]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hcj : ∀ j, c j ∈ Submodule.span (regAt ξ p) (Set.range b) := fun j => by
    rw [hbc]
    exact Submodule.subset_span ⟨j, rfl⟩
  refine ⟨top_le_iff.1 (hsp.ge.trans (Submodule.span_le.2 ?_)), ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact mem_span_field_of_mem_span_regAt ξ p b _ (hcj j)
  obtain ⟨U, hU, HU⟩ := exists_open_forall p
    (fun (i : Fin g) (q : Cpt ξ) => b i ∈ Submodule.span (regAt ξ q) (Set.range c))
    fun i => exists_open_mem_span ξ p c _ (hbi i)
  obtain ⟨V, hV, HV⟩ := exists_open_forall p
    (fun (j : Fin n) (q : Cpt ξ) => c j ∈ Submodule.span (regAt ξ q) (Set.range b))
    fun j => exists_open_mem_span ξ p b _ (hcj j)
  refine ⟨x.opensRange ⊓ (U ⊓ V), ⟨hp, hU, hV⟩, fun q hq => ⟨hb.1, ?_⟩⟩
  rw [(hc q hq.1).2]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    exact HV q hq.2.2 j
  · rintro _ ⟨i, rfl⟩
    exact HU q hq.2.1 i

end GlobalTheory.CompanionTheory.Ar.LieVB
