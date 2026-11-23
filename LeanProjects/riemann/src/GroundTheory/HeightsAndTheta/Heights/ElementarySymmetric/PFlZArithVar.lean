import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsFlZArithVar
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsFlZIdealEqCoord
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagArithVar
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FlZArithVar

section Rename

variable {K : Type} [Fintype K] {ι ι' : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

omit [Fintype K] in

theorem isMultiHomog_rename_sigma (e : ∀ k, ι k ≃ ι' k) {g : MRing ι} {a : K → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (Equiv.sigmaCongrRight e) g : MRing ι') a := by
  classical
  intro m hm k
  rw [support_rename_of_injective (Equiv.sigmaCongrRight e).injective, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  have h1 : ∀ i : ι' k, Finsupp.mapDomain (Equiv.sigmaCongrRight e) m0 ⟨k, i⟩ = m0 ⟨k, (e k).symm i⟩ := by
    intro i
    have : (⟨k, i⟩ : Σ k, ι' k) = Equiv.sigmaCongrRight e ⟨k, (e k).symm i⟩ := by simp
    rw [this, Finsupp.mapDomain_apply (Equiv.sigmaCongrRight e).injective]
  simp only [h1]
  rw [Equiv.sum_comp (e k).symm (fun j => m0 ⟨k, j⟩)]
  exact hg m0 hm0 k

theorem isArithVar_comap_rename_sigma (e : ∀ k, ι k ≃ ι' k) {P : Ideal (MRing ι')} {d : ℕ}
    (hP : IsArithVar P d) :
    IsArithVar (P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι')) d := by
  obtain ⟨hne, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  let E : MRing ι ≃+* MRing ι' := (renameEquiv ℤ (Equiv.sigmaCongrRight e)).toRingEquiv
  have hQ : P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι') = P.map E.symm := by
    rw [Ideal.map_symm]
    rfl
  have hEs : ∀ g, E.symm g = rename (Equiv.sigmaCongrRight fun k => (e k).symm) g := by
    intro g
    show (renameEquiv ℤ (Equiv.sigmaCongrRight e)).symm g = _
    rw [renameEquiv_symm, Equiv.sigmaCongrRight_symm]
    rfl
  refine ⟨hne, ⟨?_, ⟨E.symm '' S, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact Ideal.comap_isPrime _ _
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := hS g hg
    exact ⟨a, by rw [hEs]; exact isMultiHomog_rename_sigma (fun k => (e k).symm) ha⟩
  · rw [hQ, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨(e k).symm i, fun hj => hi ?_⟩
    rw [Ideal.mem_comap] at hj
    simpa using hj
  · have h : Ideal.comap (C : ℤ →+* MRing ι)
        (P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι')) =
        Ideal.comap (C : ℤ →+* MRing ι') P := by
      ext x
      simp only [Ideal.mem_comap, rename_C]
    unfold IsHorizontal
    rw [h]
    exact hhor
  · rw [← hdim]
    refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ P E ?_)
    show P = Ideal.map (E : MRing ι →+* MRing ι') (Ideal.comap (E : MRing ι →+* MRing ι') P)
    exact (Ideal.map_comap_of_surjective (E : MRing ι →+* MRing ι') E.surjective P).symm

end Rename

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def setIncrEquiv (q : FlBlock Ψ N) : IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZBlk Ψ N q ≃ FlIdx Ψ N q where
  toFun S := ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩
  invFun A := ⟨Finset.univ.image A.1, by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩
  left_inv S := by
    apply Subtype.ext
    simp only
    exact Finset.image_orderEmbOfFin_univ S.1 S.2
  right_inv A := by
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique _ (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) A.2).symm

omit [Fintype Ψ] [DecidableEq Ψ] in

theorem flZIncr_eq : flZIncr Ψ N = Equiv.sigmaCongrRight (setIncrEquiv Ψ N) := rfl

omit [Fintype Ψ] [DecidableEq Ψ] in

theorem flZIncr_isBlockMap : IsBlockMap id (flZIncr Ψ N) := by
  rw [flZIncr_eq]
  refine ⟨Function.injective_id, (Equiv.sigmaCongrRight _).injective, fun _ => rfl, fun q _ => ?_⟩
  exact (Equiv.sigmaCongrRight (setIncrEquiv Ψ N)).surjective q

end FlZArithVar

theorem FlZArithVar.proof (h : FlZIdealEqCoord.Statement) : FlZArithVar.Statement := by
  intro Ψ _ _ _ N hN
  have hA := FlagArithVar.proof Ψ N hN
  have hI : IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZIdeal Ψ N = imageZ (flZIncr Ψ N) (PFl Ψ N) := by
    rw [h Ψ N, PFl]
    exact GroundTheory.Heights₂.Heights.Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v
      (FlZArithVar.flZIncr_isBlockMap Ψ N) (yFl Ψ N)
  rw [hI, imageZ, FlZArithVar.flZIncr_eq]
  exact FlZArithVar.isArithVar_comap_rename_sigma (FlZArithVar.setIncrEquiv Ψ N) hA

end GroundTheory.Heights₂.Heights.LowerBoundFree
