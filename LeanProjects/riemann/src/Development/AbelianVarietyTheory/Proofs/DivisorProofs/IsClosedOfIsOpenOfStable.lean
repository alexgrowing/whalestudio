import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqNearFibreOfQuotContracts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDiffUnitSpecialises
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqUnitOfPullbackEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem isClosed_of_isOpen_of_stable {S : Scheme.{0}} [IsLocallyNoetherian S] {L : Set S} (ho : IsOpen L)
    (hs : ∀ t ∈ L, ∀ s, s ∈ closure ({t} : Set S) → s ∈ L) : IsClosed L := by
  rw [← closure_subset_iff_isClosed]
  intro s hsc
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hUa : IsAffineOpen U := hU
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : TopologicalSpace.NoetherianSpace (U : Set S) := noetherianSpace_of_isAffineOpen U hUa
  haveI : QuasiSober (U : Set S) := U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  let s' : (U : Set S) := ⟨s, hsU⟩
  let L' : Set (U : Set S) := Subtype.val ⁻¹' L
  have hL'o : IsOpen L' := ho.preimage continuous_subtype_val
  have hs' : s' ∈ closure L' := by
    rw [mem_closure_iff]
    intro O hO hsO
    obtain ⟨O₀, hO₀, rfl⟩ := isOpen_induced_iff.mp hO
    obtain ⟨x, ⟨hxO, hxU⟩, hxL⟩ := mem_closure_iff.mp hsc (O₀ ∩ U) (hO₀.inter U.isOpen) ⟨hsO, hsU⟩
    exact ⟨⟨x, hxU⟩, hxO, hxL⟩
  let D : Set (U : Set S) := ⋃ Z ∈ {Z ∈ irreducibleComponents (U : Set S) | (Z ∩ L').Nonempty}, Z
  have hD : IsClosed D :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  have hLD : L' ⊆ D := fun y hy =>
    Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents y, y, mem_irreducibleComponent, hy⟩
      mem_irreducibleComponent
  obtain ⟨Z, ⟨hZ, hZL⟩, hsZ⟩ := Set.mem_iUnion₂.mp ((closure_minimal hLD hD) hs')
  have hZi : IsIrreducible Z := hZ.1
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hg : IsGenericPoint hZi.genericPoint Z := by
    have := hZi.isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  have hgL : hZi.genericPoint ∈ L' := (hg.mem_open_set_iff hL'o).mpr hZL
  have hsp : hZi.genericPoint ⤳ s' := by
    rw [specializes_iff_mem_closure, hg.def]; exact hsZ
  exact hs _ hgL s (specializes_iff_mem_closure.mp (hsp.map continuous_subtype_val))

theorem eqLocus_isClosedImmersion : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → (φ' ≫ u.left = φ' ≫ v.left ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A B _ _ u v hA hB hu hv
  haveI := hA.comm
  haveI := hB.comm
  let P : S → Prop := fun t => ∀ x : A.left, A.hom x = t → (u * v⁻¹).left x = (η[B]).left t
  have hloc : ∀ t, P t → ∃ V : S.Opens, t ∈ V ∧ (A.hom ⁻¹ᵁ V).ι ≫ u.left = (A.hom ⁻¹ᵁ V).ι ≫ v.left :=
    fun t ht => eq_near_fibre_of_quot_contracts S A B u v hA hB hu hv t ht
  have hagree : ∀ V : S.Opens, (A.hom ⁻¹ᵁ V).ι ≫ u.left = (A.hom ⁻¹ᵁ V).ι ≫ v.left → ∀ t ∈ V, P t := by
    intro V hV t htV x hx
    have hxV : x ∈ A.hom ⁻¹ᵁ V := by show A.hom x ∈ V; rw [hx]; exact htV
    obtain ⟨y, rfl⟩ : x ∈ Set.range (A.hom ⁻¹ᵁ V).ι := by rw [Scheme.Opens.range_ι]; exact hxV
    let Q : Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ⟶ A := Over.homMk (A.hom ⁻¹ᵁ V).ι rfl
    have hQ : Q ≫ u = Q ≫ v := by ext1; simpa [Q] using hV
    have h1 : Q ≫ (u * v⁻¹) = 1 := by rw [comp_mul, GrpObj.comp_inv, hQ, mul_inv_cancel]
    have h2 : (A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left = ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ≫ (η[B]).left := by
      have := congrArg CommaMorphism.left h1
      simpa [Q, Hom.one_def] using this
    have e1 : ((A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left) y = (((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ≫ (η[B]).left) y := by
      rw [h2]
    simp only [Scheme.Hom.comp_apply] at e1
    rw [e1, hx]
  let L : Set S := {t | P t}
  have hLo : IsOpen L := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨V, htV, hV⟩ := hloc t ht
    exact ⟨V, fun t' ht' => hagree V hV t' ht', V.isOpen, htV⟩
  have hLc : IsClosed L := isClosed_of_isOpen_of_stable hLo fun t ht s hs =>
    hom_diff_unit_specialises S A B u v hA hB hu hv t s hs ht
  let W : S.Opens := ⟨L, hLo⟩
  have hWi : IsClosedImmersion W.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hLc)
  refine ⟨W, W.ι, hWi, ?_⟩
  intro T t A' _ φ' hp
  constructor
  · intro he
    have hr : Set.range t ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨τ, rfl⟩
      exact eq_unit_of_pullback_eq S A B u v hA hB hu hv T t A' φ' hp he τ
    exact ⟨IsOpenImmersion.lift W.ι t hr, IsOpenImmersion.lift_fac _ _ _⟩
  · rintro ⟨z, hz⟩
    have hmem : ∀ y : A'.left, P (t (A'.hom y)) := by
      intro y
      have : t (A'.hom y) ∈ Set.range W.ι := ⟨z (A'.hom y), by rw [← hz, Scheme.Hom.comp_apply]⟩
      rw [Scheme.Opens.range_ι] at this
      exact this
    choose V hVt hV using fun y => hloc _ (hmem y)
    have hw : φ' ≫ A.hom = A'.hom ≫ t := hp.1.w
    let U : A'.left → A'.left.Opens := fun y => φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)
    have hyU : ∀ y, y ∈ U y := by
      intro y
      show A.hom (φ' y) ∈ V y
      rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
      exact hVt y
    have hU : TopologicalSpace.IsOpenCover U :=
      eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
    refine Scheme.Cover.hom_ext (Scheme.openCoverOfIsOpenCover _ U hU) _ _ fun y => ?_
    show (φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)).ι ≫ φ' ≫ u.left = (φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)).ι ≫ φ' ≫ v.left
    rw [← morphismRestrict_ι_assoc, ← morphismRestrict_ι_assoc, hV y]

end GlobalTheory.EndLoc
