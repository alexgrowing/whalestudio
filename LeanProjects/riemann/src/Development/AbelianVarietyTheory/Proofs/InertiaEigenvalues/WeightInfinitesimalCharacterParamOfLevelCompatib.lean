import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighestWeightAtConjugateEmbeddingRevNegStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

noncomputable section

namespace GlobalTheory.WeightParamTie

open Formalism.L2

theorem paramV_half (R : Ranks) (h : HCParam R) (j : Fin R.m) :
    NG.paramV R h j (1 / 2) = (param h j).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) := by
  simp only [NG.paramV, param, run, Multiset.map_add, Multiset.map_map]
  congr 1
  · congr 1
    · refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]; push_cast; ring
    · refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]; push_cast; ring
  · refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply]; push_cast; ring

theorem infOf_neg_rev (n : ℕ) (lam : Fin n → ℤ) :
    NG.infOf (fun k => -lam (Fin.rev k)) = (NG.infOf lam).map Neg.neg := by
  have hu : (Finset.univ : Finset (Fin n)).val = Finset.univ.val.map Fin.rev := by
    conv_lhs => rw [← Finset.univ_map_equiv_to_embedding Fin.revPerm]
    rfl
  unfold NG.infOf
  conv_lhs => rw [hu]
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, Fin.rev_rev, Fin.val_rev]
  have hk : (k : ℕ) + 1 ≤ n := k.2
  rw [Nat.cast_sub hk]
  push_cast
  ring

theorem weightParam_of_levelTied : ∀ (D : D7) (M : Formalism.L2.MtFam D) (tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E),
    Formalism.L2.LevelTied D M tup → (∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)}) →
    (∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ),
      (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam) → WeightParam D := by
  intro D M tup hL hEta hLoc i ρ
  set a := GlobalTheory.WtDual.dualWt (M.loc i).wt with ha
  have hd : (M.loc i).wt.IsDual a := GlobalTheory.WtDual.isDual_dualWt _
  obtain ⟨⟨lam, hlam, -⟩, -⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (embT D ρ)
  obtain ⟨⟨lam', hlam', -⟩, -⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (ComplexEmbedding.conjugate (embT D ρ))
  have huniq := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (embT D ρ)).1
  have hsw := GlobalTheory.T.highestWeightAt_conjugate_embedding_rev_neg _ _ a (embT D ρ) lam' hlam'
  have heq : lam = fun k => -lam' (Fin.rev k) := huniq.unique hlam hsw
  have hlam'eq : lam' = fun k => -lam (Fin.rev k) := by
    funext k; rw [heq]; simp [Fin.rev_rev]
  have key : ∀ (k : ℕ) (hk : k = D.nd.j i) (h1 : 1 ≤ k) (h2 : k ≤ D.R.m),
      (M (D.nd.mu i) k h1 h2).wt = (M.loc i).wt := by
    intro k hk h1 h2; subst hk; rfl
  have hj : (liftIdx D i).1 + 1 = D.nd.j i := by
    have := D.nd.j_range i
    simp only [liftIdx]
    omega
  have hwt := hL.wt (D.nd.mu i) (liftIdx D i) ρ (1 / 2) a lam (hEta ρ)
    (by rw [key _ hj]; exact hd) hlam
  have hinf : D.naut.infWt i (embT D ρ) = (PP D i ρ).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) := by
    rw [hLoc i a _ lam hd hlam, hwt, paramV_half]
    rfl
  have e0 : embOver D ρ false = embT D ρ := rfl
  have e1 : embOver D ρ true = ComplexEmbedding.conjugate (embT D ρ) := by
    ext x
    rw [GlobalTheory.JumpDictionaryFoundation.embOver_true_apply, ComplexEmbedding.conjugate_coe_eq]
    rfl
  refine ⟨by rw [e0, hinf], ?_⟩
  rw [e1, hLoc i a _ lam' hd hlam', hlam'eq, infOf_neg_rev, ← hLoc i a _ lam hd hlam, hinf, Multiset.map_map]
  refine Multiset.map_congr rfl fun p _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

end GlobalTheory.WeightParamTie
