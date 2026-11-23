import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1FiniteAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleOfFiniteAffineSubcoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfIsCoboundarySubcoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSemiAbelianAffineOpenBaseChangeCompactCoveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFiniteGenerationOfAffineBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin
open GlobalTheory.CatCoh GlobalTheory.CechDR

theorem isCoc_sub {Z : Scheme.{0}} {J : Type} (W : J → Z.Opens) {c c' : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCoc W c) (hc' : IsCoc W c') : IsCoc W (fun i i' => c i i' - c' i i') := by
  intro i i' i''
  simp only [map_sub]
  linear_combination hc i i' i'' - hc' i i' i''

theorem cechFG_of_finite (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) [CompactSpace Z]
    (hfin : Module.Finite R (HO1 s)) (J : Type) (W : J → Z.Opens)
    (hD : ∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) (hc : ⨆ i, W i = ⊤) :
    CechFG W R (fun i i' => (secMap s (W i ⊓ W i')).hom) := by
  classical
  have hW : ∀ i, IsAffineOpen (W i) := fun i => by simpa using hD {i} (Finset.singleton_nonempty i)
  have hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i') := fun i i' => by
    have h := hD {i, i'} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_singleton] at h
  have hW3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'') := fun i i' i'' => by
    have h := hD {i, i', i''} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_insert, Finset.iInf_singleton, ← inf_assoc] at h
  obtain ⟨S, hS⟩ : ∃ S : Finset J, ⨆ i ∈ S, W i = ⊤ := by
    have hcov : (Set.univ : Set Z) ⊆ ⋃ i, (W i : Set Z) := by
      intro x _
      have hx : x ∈ ⨆ i, W i := hc ▸ trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      exact Set.mem_iUnion.2 hx
    obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun i => (W i : Set Z)) (fun i => (W i).isOpen) hcov
    refine ⟨S, eq_top_iff.2 fun x _ => ?_⟩
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨hi, hx⟩⟩
  have hsur : ∀ c, IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i i',
      c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
    intro c hcoc
    obtain ⟨f, h₀, hf⟩ := GlobalTheory.T.cechCocycle_of_finite_affine_subcover R Z s J W hW hW2 hD S hS c hcoc
    obtain ⟨h, hh⟩ := GlobalTheory.T.cechCocycle_isCoboundary_of_isCoboundary_subcover Z J W (↑S) (fun i => by
        rw [show (⨆ a ∈ (↑S : Set J), W a) = ⨆ a ∈ S, W a from by simp, hS]; exact le_top)
      (fun i i' => c i i' - rho W s hW hW2 f.1 i i') (isCoc_sub W hcoc (rho_isCoc W s hW hW2 hW3 f)) h₀
      (fun a ha b hb => by rw [hf a ha b hb]; ring)
    exact ⟨f, h, fun i i' => by rw [← hh]; ring⟩
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := HO1 s)
  choose fk hfk using fun k => H1.mk_surjective (OAff s) (v k)
  refine ⟨n, fun k => rho W s hW hW2 (fk k).1, fun k => rho_isCoc W s hW hW2 hW3 (fk k), fun c hcoc => ?_⟩
  obtain ⟨f, h, hfh⟩ := hsur c hcoc
  have hmem : H1.mk (OAff s) f ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  have hcl : H1.mk (OAff s) f = H1.mk (OAff s) (∑ k, r k • fk k) := by
    rw [map_sum, ← hr]
    simp only [map_smul, hfk]
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hcl
  have e1 : f.1 = (∑ k, r k • (fk k).1) + d0 (OAff s) g := by
    rw [hg, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    abel
  refine ⟨r, fun i => h i + (-gv s g ⟨W i, hW i⟩), fun i i' => ?_⟩
  rw [hfh, e1, rho_add, rho_sum, rho_d0, map_add, map_add]
  ring

end GlobalTheory.CechFin

open GlobalTheory.CechFin in
theorem GlobalTheory.CechFin.cech_h1_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1), ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i'), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (r : Fin N → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  intro E _ _ _ H X t hP hA U J W hWaff hcov hWU
  obtain ⟨hcomp, hD, htop⟩ := GlobalTheory.T.properSemiAbelian_affineOpen_baseChange_compact_cover E H X t hP U J W hWaff hcov
  have hfin := GlobalTheory.T.structure_h1_finite_affine_open E H X t hP U
  exact GlobalTheory.T.cech_finite_generation_of_affine_base_change t.G.left X t.G.hom U J W hWU
    (cechFG_of_finite Γ(X, U.1) (pullback t.G.hom U.2.fromSpec) (pullback.snd t.G.hom U.2.fromSpec) hfin J _ hD htop)
