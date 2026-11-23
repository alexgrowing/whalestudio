import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionEigenOfLocalisedFormsSection
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PendOf.CenEig

theorem onMt_mem_typeSum (D : D7) (i : D.nd.Loc) (hC : OnMtPreservesTypeV D) (c : MonoidAlgebra ℂ (G0g D.nd))
    (o : Option (D.nd.X i)) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (hF : F ∈ typeSum D i o) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c F ∈ typeSum D i o := by
  have h : typeSum D i o ≤ (typeSum D i o).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c) := by
    refine iSup₂_le fun P hP G hG => ?_
    exact (le_biSup (D.naut.typeV i) hP : D.naut.typeV i P ≤ typeSum D i o) (hC i P c G hG)
  exact h hF

theorem mem_heckeEig_of_mem_typeSum (D : D7) (i : D.nd.Loc) (S : Sec D i) (x : D.nd.X i)
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) (hw : S.Φ w ∈ typeSum D i (some x)) :
    w ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  classical
  have hvtop : w ∈ ⨆ y, heckeEig (D.nd.T i) (D.nd.act i) y := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ w).1 hvtop
  have hΦv : S.Φ w = ∑ y ∈ f.support, S.Φ (f y) := by
    rw [← hsum, Finsupp.sum, map_sum]
  have hind := GlobalTheory.PendOf.PrTypeProof.typeSum_indep D i
  have key : ∀ y, y ≠ x → f y = 0 := by
    intro y hy
    by_cases hs : y ∈ f.support
    · have e : S.Φ (f y) = S.Φ w - ∑ y' ∈ f.support.erase y, S.Φ (f y') := by
        rw [hΦv, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]
      have m2 : S.Φ (f y) ∈ ⨆ (o) (_ : o ≠ some y), typeSum D i o := by
        rw [e]
        refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun y' hy' => ?_)
        · exact Submodule.mem_iSup_of_mem (some x)
            (Submodule.mem_iSup_of_mem (fun e' => hy (Option.some_injective _ e').symm) hw)
        · refine Submodule.mem_iSup_of_mem (some y') (Submodule.mem_iSup_of_mem ?_ (S.eig y' _ (hf y')))
          exact fun e' => Finset.ne_of_mem_erase hy' (Option.some_injective _ e')
      have h0 : S.Φ (f y) = 0 := (Submodule.disjoint_def.1 (hind (some y))) _ (S.eig y _ (hf y)) m2
      exact S.inj (h0.trans (map_zero S.Φ).symm)
    · exact Finsupp.notMem_support_iff.1 hs
  rw [← hsum, Finsupp.sum]
  refine Submodule.sum_mem _ fun y _ => ?_
  by_cases hyp : y = x
  · subst hyp; exact hf y
  · rw [key y hyp]
    exact Submodule.zero_mem _

theorem main : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), OnMtPreservesTypeV D → ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x : D.nd.X i) (u w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)), u ∈ heckeEig (D.nd.T i) (D.nd.act i) x → S.Φ w = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ u) → w ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  intro D i S hC c x u w hu hw
  refine mem_heckeEig_of_mem_typeSum D i S x w ?_
  rw [hw]
  exact onMt_mem_typeSum D i hC c _ _ (S.eig x u hu)

end GlobalTheory.PendOf.CenEig

end
