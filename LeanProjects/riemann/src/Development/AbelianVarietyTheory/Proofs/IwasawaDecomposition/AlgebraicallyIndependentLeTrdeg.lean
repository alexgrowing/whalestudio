import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapResMap
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.FlagGen

namespace GlobalTheory

theorem card_algebraicIndependent_compositum_le_trdeg
    {k K Ω : Type} [Field k] [Field K] [Field Ω] (r : k →+* K) (σ ι : K →+* Ω)
    (hr : σ.comp r = ι.comp r)
    {J : Type} [Fintype J] (e : J → Ω)
    (he : ∀ j, e j ∈ Subfield.closure (Set.range ι ∪ Set.range σ))
    (hind : letI : Algebra K Ω := ι.toAlgebra; AlgebraicIndependent K e) :
    (Fintype.card J : Cardinal) ≤ (letI : Algebra k K := r.toAlgebra; Algebra.trdeg k K) := by
  letI : Algebra k K := r.toAlgebra
  letI : Algebra K Ω := ι.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  have htr : Cardinal.mk s = Algebra.trdeg k K := hs.cardinalMk_eq_trdeg
  set T : Set Ω := σ '' s with hT
  have hmap : ∀ y ∈ Algebra.adjoin k (Set.range ((↑) : s → K)), σ y ∈ Algebra.adjoin K T := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
        obtain ⟨⟨b, hb⟩, rfl⟩ := hx
        exact Algebra.subset_adjoin ⟨b, hb, rfl⟩
    | algebraMap c =>
        have h1 : σ (algebraMap k K c) = algebraMap K Ω (r c) := by
          change σ (r c) = ι (r c)
          exact RingHom.congr_fun hr c
        rw [h1]
        exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy
  let f : Algebra.adjoin k (Set.range ((↑) : s → K)) →+* Algebra.adjoin K T :=
    (σ.comp (Algebra.adjoin k (Set.range ((↑) : s → K))).val.toRingHom).codRestrict
      (Algebra.adjoin K T) (fun y => hmap y.1 y.2)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply σ.injective
    exact congrArg Subtype.val h
  have halgS : ∀ x : K, IsAlgebraic (Algebra.adjoin K T) (σ x) := by
    intro x
    have hx : IsAlgebraic (Algebra.adjoin k (Set.range ((↑) : s → K))) x :=
      hs.isAlgebraic.isAlgebraic x
    exact hx.ringHom_of_comp_eq f σ hf (by ext y; rfl)
  have halgI : ∀ x : K, IsAlgebraic (Algebra.adjoin K T) (ι x) := by
    intro x
    have hm : ι x ∈ Algebra.adjoin K T := Subalgebra.algebraMap_mem _ x
    exact isAlgebraic_algebraMap (⟨ι x, hm⟩ : Algebra.adjoin K T)
  have halg : ∀ j, IsAlgebraic (Algebra.adjoin K T) (e j) := by
    intro j
    refine Subfield.closure_induction (p := fun x _ => IsAlgebraic (Algebra.adjoin K T) x)
      ?_ ?_ ?_ ?_ ?_ ?_ (he j)
    · rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
      exacts [halgI y, halgS y]
    · exact isAlgebraic_one
    · intro x y _ _ hx hy; exact hx.add hy
    · intro x _ hx; exact hx.neg
    · intro x _ hx; exact hx.inv
    · intro x y _ _ hx hy; exact hx.mul hy
  let M := AlgebraicIndependent.matroid K Ω
  have hI : M.Indep (Set.range e) := by
    rw [AlgebraicIndependent.matroid_indep_iff]
    exact hind.to_subtype_range
  have hsub : Set.range e ⊆ M.closure T := by
    rintro _ ⟨j, rfl⟩
    rw [AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe, Subalgebra.mem_algebraicClosure]
    exact halg j
  calc (Fintype.card J : Cardinal) = Cardinal.mk J := (Cardinal.mk_fintype J).symm
    _ = Cardinal.mk (Set.range e) := (Cardinal.mk_range_eq e hind.injective).symm
    _ = M.cRk (Set.range e) := hI.cRk_eq_cardinalMk
    _ ≤ M.cRk (M.closure T) := M.cRk_mono hsub
    _ = M.cRk T := M.cRk_closure T
    _ ≤ Cardinal.mk T := M.cRk_le_cardinalMk T
    _ ≤ Cardinal.mk s := Cardinal.mk_image_le
    _ = Algebra.trdeg k K := htr

end GlobalTheory
