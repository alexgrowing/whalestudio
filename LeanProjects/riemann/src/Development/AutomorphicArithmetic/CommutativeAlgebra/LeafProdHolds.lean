import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SlopeTestRemainingChoices
import Development.AutomorphicArithmetic.CommutativeAlgebra.SectionsBijectiveDisjointCover
import Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyRepresentatives
import Development.AutomorphicArithmetic.CommutativeAlgebra.RepresentativesAdditive
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Et

theorem UpperTheory.leafProd_holds :
    LeafProd := by
  intro _ R _ F Y ι V j _ hd hc n
  have A : SlopeTestRemainingChoices := ⟨GlobalTheory.T.etaleSheafSections_ext_and_glue, GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness, GlobalTheory.T.free_sections_ext_res_map, GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties, GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff,
    GlobalTheory.T.degreeZeroSectionClass_properties, GlobalTheory.T.cup_eq_class_of_isAW, GlobalTheory.T.tateTwist_sections_locally_generated, GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique, GlobalTheory.T.tateTwistUnitClass_rootClass_spec⟩
  have hsec := fun G : Shv R => UpperTheory.sections_bijective_disjoint_cover R G V j hd hc
  have hr := fun U : Scheme.{0} => UpperTheory.cohomology_representatives A R (res R F) U (n - 1) n (n + 1) (by omega) rfl
  have hp := fun {A' B' : Scheme.{0}} (g : A' ⟶ B') => (UpperTheory.representatives_additive A).1 R F g n
  have hnat : ∀ {G G' : Shv R} (φ : G ⟶ G') {A' B' : Scheme.{0}} (k : A' ⟶ B') (x : Sec G B'),
      Sec.map φ (Sec.res k x) = Sec.res k (Sec.map φ x) := by
    intro G G' φ A' B' k x
    exact ConcreteCategory.congr_hom (φ.hom.naturality k.op) x
  have hadd : ∀ {G : Shv R} {A' B' : Scheme.{0}} (k : A' ⟶ B') (x y : Sec G B'),
      Sec.res k (x + y) = Sec.res k x + Sec.res k y := by
    intro G A' B' k x y
    exact map_add _ x y
  have hzero : ∀ {G G' : Shv R} (φ : G ⟶ G') {A' : Scheme.{0}}, Sec.map φ (0 : Sec G A') = 0 := by
    intro G G' φ A'
    exact map_zero _
  have hzero' : ∀ {G : Shv R} {A' B' : Scheme.{0}} (k : A' ⟶ B'), Sec.res k (0 : Sec G B') = 0 := by
    intro G A' B' k
    exact map_zero _
  constructor
  · intro x x' h
    obtain ⟨z, hz⟩ := (hr Y).2.1 x
    obtain ⟨z', hz'⟩ := (hr Y).2.1 x'
    have hy : ∀ a, ∃ y : Sec ((res R F).X (n - 1)) (V a),
        Sec.res (j a) z = Sec.res (j a) z' + Sec.map ((res R F).d (n - 1) n) y := by
      intro a
      have h1 := hp (j a) z x hz
      have h2 := hp (j a) z' x' hz'
      exact ((hr (V a)).2.2.2.1 _ _ _ _ h1 h2).2.2.1 (congrFun h a)
    choose y hy using hy
    obtain ⟨Y', hY⟩ := (hsec ((res R F).X (n - 1))).2 y
    have hzz : z = z' + Sec.map ((res R F).d (n - 1) n) Y' := by
      apply (hsec ((res R F).X n)).1
      funext a
      have hYa : Sec.res (j a) Y' = y a := congrFun hY a
      change Sec.res (j a) z = Sec.res (j a) (z' + Sec.map ((res R F).d (n - 1) n) Y')
      rw [hadd, ← hnat, hYa]
      exact hy a
    exact ((hr Y).2.2.2.1 _ _ _ _ hz hz').2.2.2 ⟨Y', hzz⟩
  · intro c
    have hz := fun a => (hr (V a)).2.1 (c a)
    choose z hz using hz
    obtain ⟨Z, hZ⟩ := (hsec ((res R F).X n)).2 z
    have hZa : ∀ a, Sec.res (j a) Z = z a := fun a => congrFun hZ a
    have hcl : Sec.map ((res R F).d n (n + 1)) Z = 0 := by
      apply (hsec ((res R F).X (n + 1))).1
      funext a
      change Sec.res (j a) (Sec.map ((res R F).d n (n + 1)) Z) = Sec.res (j a) 0
      rw [← hnat, hZa, hzero']
      exact ((hr (V a)).2.2.1 _ _ (hz a)).1
    obtain ⟨C, hC⟩ := (hr Y).1 Z hcl
    refine ⟨C, ?_⟩
    funext a
    have h1 := hp (j a) Z C hC
    rw [hZa] at h1
    refine ((hr (V a)).2.2.2.1 _ _ _ _ h1 (hz a)).2.2.2 ⟨0, ?_⟩
    rw [hzero, add_zero]

end
