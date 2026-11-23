import Development.EtaleCohomology.EtaleSheaves.LeafNormalModelPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGlueProperPf

structure Glued (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
    (hAD : A ≤ D) (hBD : B ≤ D) where
  C0 : Scheme.{0}
  c0 : C0 ⟶ Sp Ω
  iA : Sp A ⟶ C0
  iB : Sp B ⟶ C0
  hiA : IsOpenImmersion iA
  hiB : IsOpenImmersion iB
  hcA : iA ≫ c0 = Spec.map (CommRingCat.ofHom (algebraMap Ω A))
  hcB : iB ≫ c0 = Spec.map (CommRingCat.ofHom (algebraMap Ω B))
  agree : Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom) ≫ iA =
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBD).toRingHom) ≫ iB
  cover : Set.range iA.base ∪ Set.range iB.base = Set.univ
  inter : Set.range iA.base ∩ Set.range iB.base =
    Set.range (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom) ≫ iA).base

def GH (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L) : Prop :=
  u ≠ 0 ∧ u ∈ A ∧ u⁻¹ ∈ B ∧ Algebra.FiniteType Ω A ∧ Algebra.FiniteType Ω B ∧
  IsIntegrallyClosed A ∧ IsIntegrallyClosed B ∧ ringKrullDim A = 1 ∧ ringKrullDim B = 1 ∧
  IsFractionRing A L ∧ IsFractionRing B L ∧
  Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((B : Set L) ∪ {u}) ∧
  (∀ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) → (A : Set L) ⊆ V ∨ (B : Set L) ⊆ V)

abbrev Dr (Ω : Type) {L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) (u : L) : Subalgebra Ω L :=
  Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹})

theorem le_Dr_A {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) (u : L) : A ≤ Dr Ω A u :=
  fun x hx => Algebra.subset_adjoin (Set.mem_union_left _ hx)

theorem le_Dr_B {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
    (h : Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((B : Set L) ∪ {u})) : B ≤ Dr Ω A u := by
  intro x hx
  show x ∈ Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹})
  rw [h]; exact Algebra.subset_adjoin (Set.mem_union_left _ hx)

def LeafGlueExists : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u), Nonempty (Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1))

def LeafGlueIntegral : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsIntegral G.C0

def LeafGlueNormal : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  ∀ y : G.C0, IsIntegrallyClosed (G.C0.presheaf.stalk y)

def LeafGlueDim : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  topologicalKrullDim G.C0 = 1

def LeafGlueIsProper : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsProper G.c0

def LeafGlueGeneric : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  ∃ (x : G.C0) (ψ : Spec (G.C0.presheaf.stalk x) ⟶ Sp L), IsGenericPoint x (⊤ : Set G.C0) ∧
    ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = G.C0.fromSpecStalk x ≫ G.c0

theorem LeafGlueProper_of (h1 : LeafGlueExists) (h2 : LeafGlueIntegral) (h3 : LeafGlueNormal) (h4 : LeafGlueDim)
    (h5 : LeafGlueIsProper) (h6 : LeafGlueGeneric) : LateralTheory.E.LeafNormalModelPf.LeafGlueProper := by
  intro Ω L _ _ _ A B u hu huA huB hfA hfB hicA hicB hdA hdB hfrA hfrB hadj hV
  have h : GH Ω L A B u := ⟨hu, huA, huB, hfA, hfB, hicA, hicB, hdA, hdB, hfrA, hfrB, hadj, hV⟩
  obtain ⟨G⟩ := h1 Ω L A B u h
  obtain ⟨x, ψ, hx, hψ⟩ := h6 Ω L A B u h G
  exact ⟨G.C0, G.c0, x, ψ, h2 Ω L A B u h G, h5 Ω L A B u h G, h3 Ω L A B u h G, h4 Ω L A B u h G, hx, hψ⟩

theorem normal_spec (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (p : Sp R) :
    IsIntegrallyClosed ((Sp R).presheaf.stalk p) := by
  let q : PrimeSpectrum R := p
  have : IsIntegrallyClosed ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk q) := by
    haveI : q.asIdeal.IsPrime := q.isPrime
    exact isIntegrallyClosed_of_isLocalization (R := R) _ q.asIdeal.primeCompl
      (fun x hx => mem_nonZeroDivisors_of_ne_zero (fun h => hx (h ▸ q.asIdeal.zero_mem)))
  exact this

theorem normal_of_openImm {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X)
    (h : IsIntegrallyClosed (X.presheaf.stalk x)) : IsIntegrallyClosed (Y.presheaf.stalk (f.base x)) :=
  IsIntegrallyClosed.of_equiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm

theorem glued_affine_curve_stalks_integrally_closed : LeafGlueNormal := by
  intro Ω L _ _ _ A B u h G y
  haveI := G.hiA; haveI := G.hiB
  have hy : y ∈ Set.range G.iA.base ∪ Set.range G.iB.base := G.cover ▸ Set.mem_univ y
  rcases hy with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · haveI := h.2.2.2.2.2.1; exact normal_of_openImm G.iA z (normal_spec A z)
  · haveI := h.2.2.2.2.2.2.1; exact normal_of_openImm G.iB z (normal_spec B z)

theorem LeafGlueProper_of' (h1 : LeafGlueExists) (h2 : LeafGlueIntegral) (h4 : LeafGlueDim)
    (h5 : LeafGlueIsProper) (h6 : LeafGlueGeneric) : LateralTheory.E.LeafNormalModelPf.LeafGlueProper :=
  LeafGlueProper_of h1 h2 glued_affine_curve_stalks_integrally_closed h4 h5 h6

theorem irr_union {X : Type} [TopologicalSpace X] {U V : Set X} (hU : IsIrreducible U) (hV : IsIrreducible V)
    (hVo : IsOpen U) (hi : (U ∩ V).Nonempty) (hc : U ∪ V = Set.univ) : IrreducibleSpace X := by
  have h1 : V ⊆ closure (V ∩ U) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hV.2 hVo (by rwa [Set.inter_comm])
  have h2 : closure U = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hc]
    exact Set.union_subset subset_closure (h1.trans (closure_mono Set.inter_subset_right))
  have := hU.closure
  rw [h2] at this
  exact (irreducibleSpace_def X).2 this

theorem glued_affine_curve_is_integral_scheme : LeafGlueIntegral := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  haveI : IrreducibleSpace G.C0 := by
    have hA := (IrreducibleSpace.isIrreducible_univ (Sp A)).image G.iA.base G.iA.base.hom.continuous.continuousOn
    have hB := (IrreducibleSpace.isIrreducible_univ (Sp B)).image G.iB.base G.iB.base.hom.continuous.continuousOn
    rw [Set.image_univ] at hA hB
    refine irr_union hA hB G.iA.isOpenEmbedding.isOpen_range ?_ G.cover
    rw [G.inter]; exact Set.range_nonempty _
  haveI : ∀ y : G.C0, _root_.IsReduced (G.C0.presheaf.stalk y) := by
    intro y
    have hy : y ∈ Set.range G.iA.base ∪ Set.range G.iB.base := G.cover ▸ Set.mem_univ y
    rcases hy with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact isReduced_of_injective (asIso (G.iA.stalkMap z)).commRingCatIsoToRingEquiv.toRingHom
        (asIso (G.iA.stalkMap z)).commRingCatIsoToRingEquiv.injective
    · exact isReduced_of_injective (asIso (G.iB.stalkMap z)).commRingCatIsoToRingEquiv.toRingHom
        (asIso (G.iB.stalkMap z)).commRingCatIsoToRingEquiv.injective
  haveI : IsReduced G.C0 := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem LeafGlueProper_of'' (h1 : LeafGlueExists) (h4 : LeafGlueDim) (h5 : LeafGlueIsProper) (h6 : LeafGlueGeneric) :
    LateralTheory.E.LeafNormalModelPf.LeafGlueProper :=
  LeafGlueProper_of h1 glued_affine_curve_is_integral_scheme glued_affine_curve_stalks_integrally_closed h4 h5 h6
