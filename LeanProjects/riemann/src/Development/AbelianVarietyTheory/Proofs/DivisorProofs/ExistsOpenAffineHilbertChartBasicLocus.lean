import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackPbMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeModuleComplementSupportCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLinearCombinationOfRankAtStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportQuotientSpanIffOfIsPushoutStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsFiniteFlatRankOfFiniteFlatStatement

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff.Locus

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r N : ℕ}

theorem secs_props {T : Scheme.{0}} (y : (functor A B r).obj (op T)) (U : T.Opens)
    (hU : IsAffineOpen U) :
    letI := ((proj y).app U).hom.toAlgebra
    Module.Finite Γ(T, U) Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) ∧
      Module.Flat Γ(T, U) Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) ∧
      ∀ q : PrimeSpectrum Γ(T, U), Module.rankAtStalk Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) q = r := by
  obtain ⟨h1, h2, h3⟩ := y.2.2
  exact GlobalTheory.T.sections_finite_flat_rank_of_isFinite_flat _ _ (proj y) r h3 U hU

theorem isOpen_bad_compl (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U) :
    IsOpen (bad e σ y U)ᶜ := by
  letI := ((proj y).app U).hom.toAlgebra
  haveI := (secs_props y U hU).1
  exact (Module.isClosed_support (R := Γ(T, U))).isOpen_compl

theorem isCompact_bad_compl (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U) :
    IsCompact (bad e σ y U)ᶜ := by
  letI := ((proj y).app U).hom.toAlgebra
  obtain ⟨h1, h2, h3⟩ := secs_props y U hU
  exact GlobalTheory.T.free_module_complement_support_compact _ _ r h3 (gens e σ y U)

theorem basic_iff (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) :
    Basic A B e σ y ↔ ∀ U : T.affineOpens, bad e σ y U = ∅ := by
  refine forall_congr' fun U => ?_
  letI := ((proj y).app U).hom.toAlgebra
  obtain ⟨h1, h2, h3⟩ := secs_props y U U.2
  have hf : (fun c : Fin r → Γ(T, U) => ∑ k, ((proj y).app U).hom (c k) * gens e σ y U k) =
      Fintype.linearCombination Γ(T, U) (gens e σ y U) := by
    ext c
    simp [Fintype.linearCombination_apply, Algebra.smul_def]
    rfl
  change Function.Bijective (fun c : Fin r → Γ(T, U) =>
    ∑ k, ((proj y).app U).hom (c k) * gens e σ y U k) ↔ _
  rw [hf]
  refine ⟨fun hb => ?_, fun hb => GlobalTheory.T.linearCombination_bijective_of_rankAtStalk_eq _ _ r h3 _ hb⟩
  show Module.support _ _ = ∅
  rw [Module.support_eq_empty_iff, Submodule.Quotient.subsingleton_iff,
    ← Fintype.range_linearCombination, LinearMap.range_eq_top]
  exact hb.2

theorem appLE_congr_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V (e ▸ h) := by
  subst e; rfl

theorem gens_pbMap (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T T' : Scheme.{0}}
    (a : T' ⟶ T) (y : (functor A B r).obj (op T)) (U : T.Opens) (U' : T'.Opens)
    (hleG : proj ((functor A B r).map a.op y) ⁻¹ᵁ U' ≤ pbMap a y ⁻¹ᵁ (proj y ⁻¹ᵁ U)) (k : Fin r) :
    ((pbMap a y).appLE (proj y ⁻¹ᵁ U) _ hleG).hom (gens e σ y U k) =
      gens e σ ((functor A B r).map a.op y) U' k := by
  simp only [gens]
  rw [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]
  rw [appLE_congr_eq (pbMap_fst a y)]

theorem bad_nat (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T T' : Scheme.{0}}
    (a : T' ⟶ T) (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U)
    (U' : T'.Opens) (hU' : IsAffineOpen U') (h : U' ≤ a ⁻¹ᵁ U) (x : T') (hx : x ∈ U') :
    hU'.primeIdealOf ⟨x, hx⟩ ∈ bad e σ ((functor A B r).map a.op y) U' ↔
      hU.primeIdealOf ⟨a x, h hx⟩ ∈ bad e σ y U := by
  have sq := isPullback_pbMap a y
  have hleG : proj ((functor A B r).map a.op y) ⁻¹ᵁ U' ≤ pbMap a y ⁻¹ᵁ (proj y ⁻¹ᵁ U) := by
    intro z hz
    show (pbMap a y ≫ proj y) z ∈ U
    rw [sq.w, Scheme.Hom.comp_apply]
    exact h hz
  haveI : IsFinite (proj y) := y.2.2.1
  have hP := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance hU hU' h hleG
  have fin : ((proj y).app U).hom.Finite := (secs_props y U hU).1
  have H := GlobalTheory.T.mem_support_quotient_span_iff_of_isPushout' _ _ _ _ _ _ _ _ hP fin (gens e σ y U) (hU'.primeIdealOf ⟨x, hx⟩)
  rw [IsAffineOpen.comap_primeIdealOf_appLE U hU U' hU' h hx] at H
  have hg : (fun i => ((pbMap a y).appLE (proj y ⁻¹ᵁ U) _ hleG).hom (gens e σ y U i)) =
      gens e σ ((functor A B r).map a.op y) U' := funext (gens_pbMap e σ a y U U' hleG)
  rw [hg] at H
  exact H

theorem map_id_apply' {T : Scheme.{0}} (y : (functor A B r).obj (op T)) :
    (functor A B r).map (𝟙 T).op y = y := by
  rw [op_id, FunctorToTypes.map_id_apply]

theorem bad_local (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U₁ U₂ : T.Opens) (h₁ : IsAffineOpen U₁) (h₂ : IsAffineOpen U₂)
    (x : T) (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) :
    h₁.primeIdealOf ⟨x, hx₁⟩ ∈ bad e σ y U₁ ↔ h₂.primeIdealOf ⟨x, hx₂⟩ ∈ bad e σ y U₂ := by
  obtain ⟨U₀, hU₀, hx₀, hle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) (show x ∈ U₁ ⊓ U₂ from ⟨hx₁, hx₂⟩)
  have k₁ := bad_nat e σ (𝟙 T) y U₁ h₁ U₀ hU₀ (fun z hz => (hle hz).1) x hx₀
  have k₂ := bad_nat e σ (𝟙 T) y U₂ h₂ U₀ hU₀ (fun z hz => (hle hz).2) x hx₀
  rw [map_id_apply'] at k₁ k₂
  exact k₁.symm.trans k₂

theorem primeIdealOf_fromSpec {T : Scheme.{0}} {U : T.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(T, U)) (h : hU.fromSpec q ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec q, h⟩ = q :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

theorem mem_goodSet_iff (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U) (x : T) (hx : x ∈ U) :
    x ∈ goodSet e σ y ↔ hU.primeIdealOf ⟨x, hx⟩ ∉ bad e σ y U := by
  constructor
  · intro hmem
    obtain ⟨U₁, q, hq, rfl⟩ := Set.mem_iUnion.mp hmem
    have h₁ : IsAffineOpen (U₁ : T.Opens) := U₁.2
    have hx₁ : h₁.fromSpec q ∈ (U₁ : T.Opens) := by
      rw [← SetLike.mem_coe, ← h₁.range_fromSpec]; exact ⟨q, rfl⟩
    have key : h₁.primeIdealOf ⟨h₁.fromSpec q, hx₁⟩ = q := primeIdealOf_fromSpec h₁ q hx₁
    rw [← bad_local e σ y U₁ U h₁ hU _ hx₁ hx, key]
    exact hq
  · intro hq
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, _, hq, hU.fromSpec_primeIdealOf _⟩

theorem goodSet_map (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T T' : Scheme.{0}}
    (a : T' ⟶ T) (y : (functor A B r).obj (op T)) (x : T') :
    x ∈ goodSet e σ ((functor A B r).map a.op y) ↔ a x ∈ goodSet e σ y := by
  obtain ⟨U, hU, hxU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) (show a x ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨U', hU', hxU', hle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T'.isBasis_affineOpens) (show x ∈ a ⁻¹ᵁ U from hxU)
  rw [mem_goodSet_iff e σ _ U' hU' x hxU', mem_goodSet_iff e σ y U hU (a x) hxU,
    bad_nat e σ a y U hU U' hU' hle x hxU']

theorem isOpenMap_fromSpec {T : Scheme.{0}} {U : T.Opens} (hU : IsAffineOpen U) :
    IsOpenMap hU.fromSpec :=
  hU.fromSpec.isOpenEmbedding.isOpenMap

theorem isOpen_goodSet (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : IsOpen (goodSet e σ y) :=
  isOpen_iUnion fun U => isOpenMap_fromSpec U.2 _ (isOpen_bad_compl e σ y U U.2)

theorem basic_iff_goodSet (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : Basic A B e σ y ↔ goodSet e σ y = Set.univ := by
  rw [basic_iff, Set.eq_univ_iff_forall]
  constructor
  · intro h x
    obtain ⟨U, hU, hxU, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) (show x ∈ (⊤ : T.Opens) from trivial)
    rw [mem_goodSet_iff e σ y U hU x hxU, h ⟨U, hU⟩]
    exact Set.notMem_empty _
  · intro h U
    refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => ?_
    have hU : IsAffineOpen (U : T.Opens) := U.2
    have hx : hU.fromSpec q ∈ (U : T.Opens) := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨q, rfl⟩
    have := (mem_goodSet_iff e σ y U hU _ hx).mp (h _)
    rw [primeIdealOf_fromSpec hU q hx] at this
    exact this hq

theorem exists_basic_locus : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0})
    (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)), ∃ W : Z.Opens,
      (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Z), Set.range a ⊆ (W : Set Z) ↔
        GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map a.op y)) ∧
      (CompactSpace Z → IsCompact (W : Set Z)) := by
  intro A B _ _ _ N r e σ Z y
  refine ⟨⟨goodSet e σ y, isOpen_goodSet e σ y⟩, fun Z' a => ?_, fun hZ => ?_⟩
  · rw [basic_iff_goodSet, Set.eq_univ_iff_forall, Set.range_subset_iff]
    exact forall_congr' fun x => (goodSet_map e σ a y x).symm
  · have hcov : Set.univ ⊆ ⋃ U : Z.affineOpens, ((U : Z.Opens) : Set Z) := by
      intro x _
      obtain ⟨U, hU, hxU, -⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens) (show x ∈ (⊤ : Z.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ (fun U : Z.affineOpens => U.1.isOpen) hcov
    have heq : goodSet e σ y = ⋃ U ∈ t, U.2.fromSpec '' (bad e σ y U)ᶜ := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
        refine Set.mem_iUnion₂.mpr ⟨U, hUt, _, (mem_goodSet_iff e σ y U U.2 x hxU).mp hx, ?_⟩
        exact U.2.fromSpec_primeIdealOf _
      · exact Set.iUnion₂_subset fun U _ => Set.subset_iUnion
          (fun U : Z.affineOpens => U.2.fromSpec '' (bad e σ y U)ᶜ) U
    show IsCompact (goodSet e σ y)
    rw [heq]
    exact t.isCompact_biUnion fun U _ =>
      (isCompact_bad_compl e σ y U U.2).image U.2.fromSpec.continuous

end GlobalTheory.HilbAff.Locus
