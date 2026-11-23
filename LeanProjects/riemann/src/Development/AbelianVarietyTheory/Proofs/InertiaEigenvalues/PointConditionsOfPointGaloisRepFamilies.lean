import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.SemisimpleDecompositionOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.PointConditions

theorem sum_single_jumps {M : Type} [AddCommMonoid M] [One M] (t : ℕ) (a : ℤ) :
    (∑ c ∈ Finset.Icc 1 t, (if a = (c : ℤ) - 1 then (1 : M) else 0)) = if 0 ≤ a ∧ a < t then 1 else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
    rw [Finset.sum_eq_single (n + 1)]
    · rw [if_pos (by push_cast; ring)]
    · intro c _ hne
      rw [if_neg]
      omega
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_Icc]
      omega
  · apply Finset.sum_eq_zero
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [if_neg]
    omega

theorem isSSRep_rhoChiK (D : D7) (i : D.nd.Loc) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i))
    (h : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.BlockSemisimple ρ (D.nd.chi i) D.R.t) : IsSSRep (rhoChiK D i ρ) := by
  rw [GlobalTheory.ComplementCompare.isSSRep_iff]
  refine (GlobalTheory.ComplementCompare.semisimple_congr (splitRT (KK D.nd i) D.R.r D.R.t) ?_).2 h
  intro g v
  change splitRT _ _ _ (((rhoChiK D i ρ g : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) :
      Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec v) = _
  unfold rhoChiK
  rw [blockRep_coe, blockHom_mulVec, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.blockRep_apply]
  refine Prod.ext rfl (funext fun c => ?_)
  show (Matrix.diagonal _).mulVec _ c = _
  rw [Matrix.mulVec_diagonal]
  rfl

theorem main : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (ρ i π) ∧ IsSSRep (rhoChiK D i (ρ i π)) ∧ EmbeddingTypes.ambBlock i (r i) (ρ i) π ∧ TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (r i) (ρ i) π := by
  intro D r ρ h i π hπ
  have hc := h.compl i π hπ
  refine ⟨h.frob i π hπ, isSSRep_rhoChiK D i (ρ i π) hc.ss, ?_, ?_⟩
  · intro _ _ _ w hw C τ
    have hB := h.block i π hπ w hw C.LL C.le τ
    refine ⟨fun a => ?_, fun c hc a => hB.2 c hc a⟩
    have h2 : ∀ c ∈ Finset.Icc 1 D.R.t, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a =
        if a = (c : ℤ) - 1 then 1 else 0 := fun c hc => hB.2 c hc a
    rw [Finset.sum_congr rfl h2, sum_single_jumps]
    exact hB.1 a
  · obtain ⟨e, he⟩ := hc.rho
    refine ⟨e, fun g u => ?_⟩
    have := he g u
    rw [GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.blockRep_apply] at this
    exact this

end GlobalTheory.PointConditions
