import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartUnitBasicOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegularStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.ChMorph

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem hom_eq_of_points {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) {i : Ω →+* Ω'} {f g : X' ⟶ X}
    (hf : Dominates ξ' ξ f i) (hg : Dominates ξ' ξ g i) (hb : ∀ q, f q = g q) : f = g := by
  have hbase : f.base = g.base := by
    ext q
    exact hb q
  refine Scheme.Hom.ext hbase fun U => ?_
  ext s
  refine TopCat.Presheaf.section_ext X'.sheaf _ _ _ fun q hq => ?_
  have hqg : g q ∈ U := hq
  have hqf : f q ∈ U := by rw [hb q]; exact hqg
  have hpf : genPt ξ ⤳ f q := RegAtDom.map_genPt hf ▸ (hall q).map f.continuous
  have hpg : genPt ξ ⤳ g q := RegAtDom.map_genPt hg ▸ (hall q).map g.continuous
  have key : ∀ (a b : X) (_ : a = b) (ha : genPt ξ ⤳ a) (hb : genPt ξ ⤳ b) (h1 : a ∈ U) (h2 : b ∈ U),
      genMap ξ ⟨a, ha⟩ ((X.presheaf.germ U a h1).hom s) = genMap ξ ⟨b, hb⟩ ((X.presheaf.germ U b h2).hom s) := by
    rintro a _ rfl ha hb h1 h2
    rfl
  apply hgen.inj ⟨q, hall q⟩
  have e1 := RegAtDom.genMap_stalkMap hf q (hall q) hpf ((X.presheaf.germ U (f q) hqf).hom s)
  have e2 := RegAtDom.genMap_stalkMap hg q (hall q) hpg ((X.presheaf.germ U (g q) hqg).hom s)
  rw [Scheme.Hom.germ_stalkMap_apply] at e1 e2
  have e3 := key _ _ (hb q) hpf hpg hqf hqg
  rw [← e3, ← e1] at e2
  refine (congrArg (genMap ξ' ⟨q, hall q⟩) ?_).trans e2.symm
  exact TopCat.Presheaf.germ_res_apply X'.presheaf _ q hqg _

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  {o' : Type} [CommRing o'] [Algebra o' Ω'] {κ' : Type} {y : κ' → Ω'}

theorem specializes_of_dominates (M : PModel o x) (M' : PModel o' y) {i : Ω →+* Ω'} {f g : M'.X ⟶ M.X}
    (hf : Dominates M'.ξ M.ξ f i) (hg : Dominates M'.ξ M.ξ g i) (q : M'.X) : g q ⤳ f q := by
  let p' : Cpt M'.ξ := ⟨q, M'.all q⟩
  obtain ⟨h1, fa, -⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ f i hf p'
  obtain ⟨h2, ga, gb⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ g i hg p'
  replace gb := gb M'.tie.gen
  obtain ⟨c, hc0, hc⟩ := M.tie.cover ⟨f q, h1⟩
  obtain ⟨c', hc'0, hc'⟩ := M.tie.cover ⟨g q, h2⟩
  have hu : unitAt M.ξ ⟨g q, h2⟩ (x c / x c') := by
    refine gb _ (hc' c) ⟨?_, ga _ (hc' c), ?_⟩
    · exact (map_ne_zero i).2 (div_ne_zero hc0 hc'0)
    · rw [← map_inv₀, inv_div]
      exact fa _ (hc c')
  have hin : InChart M.ξ x c ⟨g q, h2⟩ := by
    refine ⟨hc0, fun j => ?_⟩
    have : x j / x c = x j / x c' * (x c / x c')⁻¹ := by
      field_simp
    rw [this]
    exact mul_mem (hc' j) hu.2.2
  refine specializes_iff_forall_open.2 fun V hV hq => ?_
  obtain ⟨a, ha, hau, hU⟩ := GlobalTheory.T.chart_unit_basic_open o Ω κ x M c ⟨f q, h1⟩ ⟨V, hV⟩ ⟨hc0, hc⟩ hq
  have hag : a ∈ regAt M.ξ ⟨g q, h2⟩ := (M.tie.ring c hc0 a).1 ha _ hin
  refine hU ⟨g q, h2⟩ hin (gb a hag ⟨(map_ne_zero i).2 hau.1, fa a hau.2.1, ?_⟩)
  rw [← map_inv₀]
  exact fa _ hau.2.2

theorem existsUnique_dominates :
    ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x)
      (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω')
      (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) →
      ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i := by
  intro o _ Ω _ _ κ _ x M o' _ Ω' _ _ κ' _ y M' i h
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.dominates_of_coords_regular M.X Ω M.ξ o κ x M'.X Ω' M'.ξ i M.tie M'.tie.gen M'.all
    (fun r p' => by
      obtain ⟨c, -, H⟩ := h p'
      exact H _ (Subalgebra.algebraMap_mem _ r))
    (fun p' => by
      obtain ⟨c, hc, H⟩ := h p'
      refine ⟨c, (map_ne_zero i).2 hc, fun c' => ?_⟩
      rw [← map_div₀]
      exact H _ (Algebra.subset_adjoin ⟨c', rfl⟩))
  refine ⟨f, hf, fun g hg => ?_⟩
  exact hom_eq_of_points M'.tie.gen M'.all hg hf fun q =>
    ((specializes_of_dominates M M' hf hg q).antisymm (specializes_of_dominates M M' hg hf q)).eq

end GlobalTheory.CompanionTheory.Ar.ChMorph
