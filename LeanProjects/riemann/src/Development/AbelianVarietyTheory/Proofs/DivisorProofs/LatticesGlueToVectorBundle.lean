import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDescendsToSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplittingOfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSplittingRestrictsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicOpenSectionScaledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSplittingGluesOnCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffOpCoverBasicOpenRefineStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

namespace GlobalTheory.BplusDescent

theorem exists_finiteDimensional_isDescended : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] (B : GlobalTheory.Vert.Model O) (J : Type) [Finite J] (h : ℕ) (L : J → ∀ U : AffOp B.X, Submodule U.Bp (Fin h → U.Bp)) (T : Set (Σ U : AffOp B.X, U.Bp)), T.Finite → (∀ j U, Module.Finite U.Bp (L j U) ∧ Module.Projective U.Bp (L j U) ∧ ∀ x : Fin h → U.Bp, (p : U.Bp) • x ∈ L j U) → (∀ j (U U' : AffOp B.X) (hle : U'.1 ≤ U.1), L j U' = Submodule.span U'.Bp (piMap (AffOp.res hle) (Fin h) '' (L j U : Set (Fin h → U.Bp)))) → ∃ K' : IntermediateField B.X.functionField (Kbar B.X), FiniteDimensional B.X.functionField K' ∧ (∀ t ∈ T, (t.2 : Kbar B.X) ∈ K') ∧ ∀ j U, IsDescended K' U (L j U) := by
  intro O _ _ _ p _ _ B J _ h L T hT hL hc
  haveI : CharZero B.X.functionField := by
    refine charZero_of_injective_ringHom (R := O)
      (f := (B.X.presheaf.germ ⊤ (genericPoint B.X) trivial).hom.comp (algebraMap O Γ(B.X, ⊤))) ?_
    rw [injective_iff_map_eq_zero]
    intro g hg
    by_contra h0
    have h1 : B.const g = 0 := germ_injective_of_isIntegral B.X (U := ⊤) (genericPoint B.X) trivial
      (hg.trans (map_zero _).symm)
    have h2 := B.gen_le_basicOpen h0 B.genericPoint_mem_gen
    rw [h1, Scheme.basicOpen_zero] at h2
    exact h2
  haveI : CharZero (Kbar B.X) := charZero_of_injective_algebraMap (algebraMap B.X.functionField (Kbar B.X)).injective
  obtain ⟨ι, _, W, hW⟩ := GlobalTheory.T.exists_finite_affine_cover_refining_basicOpens B.X
  have hsp : ∀ j i, ∃ (n : ℕ) (g : Fin n → Fin h → (W i).Bp) (S : Fin n → Fin h → Kbar B.X),
      Splits (W i) (L j (W i)) g S := fun j i =>
    GlobalTheory.T.exists_splitting_of_lattice B.X (W i) h (L j (W i)) (p : (W i).Bp) (by simp [Fact.out (p := p.Prime) |>.ne_zero]) (hL j _).1 (hL j _).2.1
      (hL j _).2.2
  choose n g S hS using hsp
  let s : Set (Kbar B.X) := Set.range (fun q : (j : J) × (i : ι) × Fin (n j i) × Fin h => (g q.1 q.2.1 q.2.2.1 q.2.2.2 : Kbar B.X)) ∪
    Set.range (fun q : (j : J) × (i : ι) × Fin (n j i) × Fin h => S q.1 q.2.1 q.2.2.1 q.2.2.2) ∪
    (fun t : (Σ U : AffOp B.X, U.Bp) => (t.2 : Kbar B.X)) '' T
  have hs : s.Finite := ((Set.finite_range _).union (Set.finite_range _)).union (hT.image _)
  haveI : Finite s := hs.to_subtype
  refine ⟨IntermediateField.adjoin B.X.functionField s, IntermediateField.finiteDimensional_adjoin
    fun x _ => Algebra.IsIntegral.isIntegral x, fun t ht => IntermediateField.subset_adjoin _ _ (Or.inr ⟨t, ht, rfl⟩),
    fun j U => ?_⟩
  obtain ⟨m, a, V, ha, hV⟩ := hW U
  choose i hi using fun k => (hV k).2
  have hVU : ∀ k, (V k).1 ≤ U.1 := fun k => (hV k).1 ▸ B.X.basicOpen_le (a k)
  obtain ⟨n', g', S', hsp', hg', hS'⟩ := GlobalTheory.T.lattice_splitting_glues_on_cover B.X (IntermediateField.adjoin B.X.functionField s) U h m a V hVU (L j U)
    (fun k => L j (V k)) (fun k => n j (i k)) (fun k l => piMap (AffOp.res (hi k)) (Fin h) (g j (i k) l))
    (fun k => S j (i k)) ha (Module.Finite.iff_fg.1 (hL j U).1)
    (fun k x => GlobalTheory.T.basic_open_section_scaled B.X U (V k) (a k) (hV k).1 x) (fun k => hc j U (V k) (hVU k))
    (fun k => GlobalTheory.T.lattice_splitting_restricts B.X (W (i k)) (V k) (hi k) h _ (L j (W (i k))) (L j (V k)) _ _ (hc j _ _ (hi k)) (hS j (i k)))
    (fun k l i' => IntermediateField.subset_adjoin _ _ (Or.inl (Or.inl ⟨⟨j, i k, l, i'⟩, rfl⟩)))
    (fun k l i' => IntermediateField.subset_adjoin _ _ (Or.inl (Or.inr ⟨⟨j, i k, l, i'⟩, rfl⟩)))
  exact GlobalTheory.T.lattice_descends_to_subfield B.X _ U h n' (L j U) g' S' hsp' hg' hS'

end GlobalTheory.BplusDescent
