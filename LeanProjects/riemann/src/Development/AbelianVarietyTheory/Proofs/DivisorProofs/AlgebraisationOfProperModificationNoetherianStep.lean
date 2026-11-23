import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseSystemInAlgebraisingClosedSubschemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperInfIdealSheafImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfReductionAgreeOnAffineOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem alg_of_modification : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f →
    QuasiCompact f → ∀ (W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) →
    ∀ K : W.IdealSheafData, (∀ x, x ∉ K.support → x ∈ U) → Alg (π ≫ f) I →
    (∀ k : ℕ, Alg ((K ^ k).subschemeι ≫ f) I) → Alg f I := by
  intro R _ _ I W f hsep hlft hqc W' π U hπ hiso K hK hA' hAK t ht hp
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace f

  have hsys' : IsSystem (π ≫ f) I (fun e => (t e).comap π) := fun e => by
    simp only
    rw [ht e, Scheme.IdealSheafData.comap_sup, (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1]
  have hp' : ∀ e, IsProper (((t e).comap π).subschemeι ≫ π ≫ f) := fun e => by
    have h1 : ((t e).comap π).subschemeι ≫ π ≫ f =
        ((t e).comapIso π).hom ≫ pullback.snd π (t e).subschemeι ≫ (t e).subschemeι ≫ f := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc]
    rw [h1]
    infer_instance
  obtain ⟨T', hT'p, hT'r⟩ := hA' _ hsys' hp'

  have hcov : ∀ x : W, ∃ V : W.affineOpens, x ∈ (V.1 : Set W) := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV⟩, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : W.affineOpens => (V.1 : Set W))
    (fun V => V.1.2) (fun x _ => Set.mem_iUnion.2 (hcov x))
  choose k₀ hk₀ using GlobalTheory.T.idealSheaf_eq_of_reduction_agree_on_affineOpen R I W W' f π U hπ hiso K hK t ht
  let k := s.sup k₀
  obtain ⟨T'', hT''p, hT''r⟩ := GlobalTheory.T.algebraise_system_in_algebraising_closedSubscheme R I W f (K ^ k) (hAK k) t ht hp
  refine ⟨T'.map π ⊓ T'', GlobalTheory.T.isProper_inf_ideal_sheaf_image _ W W' f π hsep hlft T' T'' (by simpa using hT'p) hT''p, fun e => ?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := s) (fun V => V.1) ?_ fun V =>
    hk₀ V.1 k (Finset.le_sup V.2) T' T'' hT'r hT''r e
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, hx⟩

end GlobalTheory.FormalAlg
