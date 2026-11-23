import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.EtaleCohomology.EtaleSheaves.LeafCurveCut
import Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPfEmpty
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CurveMayerVietorisOfDegreeZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsDedekindDomainAffineSectionsOfIsCurve
import Development.AutomorphicArithmetic.CommutativeAlgebra.DedekindSpecOpenIsAffine

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.Cb.CurveInd

private theorem sp_facts (hH0 : H0TwistOverClosedField) (hH : Hyps) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (hq : IsUnit (q : Ω)) (i : ℤ)
    (hB : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B],
      Finite (Ht q (sp B) 1 i))
    (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B] :
    (∀ m : ℤ, Finite (Ht q (sp B) m i)) ∧ ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sp B) m i) := by
  have hH' := hH
  obtain ⟨a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, b7, c1, c2, c3, c4, c5, d1, d2, d3, e1, e2, e3⟩ := hH'
  have hsub : ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sp B) m i) := fun m hm => c2 q Ω B hq m i hm
  refine ⟨fun m => ?_, hsub⟩
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · haveI : Subsingleton (Ht q (sp B) m i) := (a9 (ZMod q) (tw q i)).1 (sp B) m hm
    infer_instance
  · obtain ⟨hfin, hbij⟩ := hH0 hH q Ω hq i
    haveI := hfin
    exact Finite.of_surjective _ (hbij (Spec.map (CommRingCat.ofHom (algebraMap Ω B)))).2
  · rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
    · exact hB B
    · haveI := hsub m hm2
      infer_instance

private theorem aff_facts (hH0 : H0TwistOverClosedField) (hH : Hyps) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (hq : IsUnit (q : Ω)) (i : ℤ)
    (hB : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B],
      Finite (Ht q (sp B) 1 i))
    {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c) (U : C.Opens) (hU : IsAffineOpen U)
    {Y : Scheme.{0}} (j : Y ⟶ C) [IsOpenImmersion j] (hj : j.opensRange ≤ U) :
    (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sch.obj Y) m i) := by
  by_cases hne : (j.opensRange : Set C).Nonempty
  · have hUne : (U : Set C).Nonempty := hne.mono hj
    have hcur := UpperTheory.isDedekindDomain_affine_sections_of_isCurve Ω c hc
    haveI : IsDedekindDomain (Γ(C, U) : Type) := (hcur.1 U hU hUne).1
    have hWa : IsAffineOpen j.opensRange := by
      have h1 : IsAffineOpen (hU.fromSpec ⁻¹ᵁ j.opensRange) := UpperTheory.dedekind_spec_open_isAffine (Γ(C, U) : Type) _
      have h2 := h1.image_of_isOpenImmersion hU.fromSpec
      rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, IsAffineOpen.opensRange_fromSpec,
        inf_eq_right.mpr hj] at h2
    haveI : IsDedekindDomain (Γ(C, j.opensRange) : Type) := (hcur.1 _ hWa hne).1
    have e : j.opensRange ≤ c ⁻¹ᵁ ⊤ := by simp
    letI : Algebra Ω (Γ(C, j.opensRange) : Type) :=
      ((c.appLE ⊤ j.opensRange e).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom).toAlgebra
    haveI : LocallyOfFiniteType c := by
      haveI : IsProper c := hc.2.1
      infer_instance
    haveI : Algebra.FiniteType Ω (Γ(C, j.opensRange) : Type) := by
      have hft := HasRingHomProperty.appLE @LocallyOfFiniteType c inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨j.opensRange, hWa⟩ e
      exact RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _
        (fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom x, by simp⟩))
    obtain ⟨h1, h2⟩ := sp_facts hH0 hH q Ω hq i hB (Γ(C, j.opensRange) : Type)
    have iso : Y ≅ Spec (CommRingCat.of (Γ(C, j.opensRange) : Type)) := j.isoOpensRange ≪≫ hWa.isoSpec
    refine ⟨fun m => ?_, fun m hm => ?_⟩
    · haveI := h1 m
      exact Finite.of_equiv _ (CurveCut.isoH (ZMod q) (tw q i) iso m)
    · haveI := h2 m hm
      exact (CurveCut.isoH (ZMod q) (tw q i) iso m).symm.subsingleton
  · have hr : Set.range j.base = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have iso : Y ≅ ((⊥ : C.Opens) : Scheme.{0}) := IsOpenImmersion.isoOfRangeEq j (⊥ : C.Opens).ι (by
      rw [Scheme.Opens.range_ι]
      simpa using hr)
    have hs : ∀ m : ℤ, Subsingleton (Ht q (sch.obj Y) m i) := fun m =>
      haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := C) (tw q i) m
      (CurveCut.isoH (ZMod q) (tw q i) iso m).symm.subsingleton
    refine ⟨fun m => ?_, fun m _ => hs m⟩
    haveI := hs m
    infer_instance

end UpperTheory.Cb.CurveInd

open UpperTheory.Cb.CurveInd in
theorem UpperTheory.leafCurve_of_leafH0 :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.E4.LeafCurve := by
  intro hH0 hH q _ Ω _ _ hq i hB C c hc
  have hMV := UpperTheory.Cb.curve_mayer_vietoris_of_degree_zero hH0
  haveI : IsProper c := hc.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  have key : ∀ (Y : Scheme.{0}) (j : Y ⟶ C) [IsOpenImmersion j], j.opensRange ≤ ⊤ →
      (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj Y) m i) := by
    refine compact_open_induction_on (P := fun W : C.Opens => ∀ (Y : Scheme.{0}) (j : Y ⟶ C) [IsOpenImmersion j],
      j.opensRange ≤ W →
      (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj Y) m i)) ⊤ ?_ ?_ ?_
    · simpa using (isCompact_univ : IsCompact (Set.univ : Set C))
    · intro Y j _ hj
      obtain ⟨h1, h2⟩ := aff_facts hH0 hH q Ω hq i hB c hc ⊥ (isAffineOpen_bot C) j hj
      exact ⟨h1, fun m hm => h2 m (by omega)⟩
    · intro S _ U ih Y j _ hj
      have hAB : j ⁻¹ᵁ S ⊔ j ⁻¹ᵁ (U : C.Opens) = ⊤ := by
        refine top_le_iff.mp fun y _ => ?_
        have hy : j.base y ∈ S ⊔ (U : C.Opens) := hj ⟨y, rfl⟩
        rcases (TopologicalSpace.Opens.mem_sup).mp hy with h | h
        · exact (TopologicalSpace.Opens.mem_sup).mpr (Or.inl h)
        · exact (TopologicalSpace.Opens.mem_sup).mpr (Or.inr h)
      obtain ⟨fA, sA⟩ := ih (j ⁻¹ᵁ S) ((j ⁻¹ᵁ S).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2)
      obtain ⟨fB, sB⟩ := aff_facts hH0 hH q Ω hq i hB c hc U U.2 ((j ⁻¹ᵁ (U : C.Opens)).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2)
      obtain ⟨fI, sI⟩ := aff_facts hH0 hH q Ω hq i hB c hc U U.2
        ((j ⁻¹ᵁ S ⊓ j ⁻¹ᵁ (U : C.Opens)).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2.2)
      refine ⟨fun m => ?_, fun m hm => ?_⟩
      · obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by ring⟩
        exact CurveCut.finite_of_mv hMV hH (ZMod q) (tw q i) Y _ _ hAB n (fI n) (fA (n + 1)) (fB (n + 1))
      · obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by ring⟩
        exact CurveCut.subsingleton_of_mv hMV hH (ZMod q) (tw q i) Y _ _ hAB n (sI n (by omega))
          (sA (n + 1) hm) (sB (n + 1) (by omega))
  obtain ⟨h1, h2⟩ := key C (𝟙 C) le_top
  exact ⟨h1 1, h1 2, h2⟩
