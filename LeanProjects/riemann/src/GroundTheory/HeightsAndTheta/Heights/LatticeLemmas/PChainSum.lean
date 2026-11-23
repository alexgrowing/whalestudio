import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField
open GroundTheory.Heights₂.Heights

universe u v

noncomputable section

namespace ChainSum

theorem deg_eq_of_linearEquiv {K : Type u} [Field K] [NumberField K] (A B : HermitianBundle.{v} K)
    (φ : A.carrier ≃ₗ[𝓞 K] B.carrier)
    (hg : ∀ (σ : K →+* ℂ) (n : ℕ) (s : Fin n → A.carrier),
      GroundTheory.Heights₂.Heights.gramDet A.metric σ s =
        GroundTheory.Heights₂.Heights.gramDet B.metric σ (fun i ↦ φ (s i))) :
    A.deg = B.deg := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := A.carrier)
  have ht : LinearIndependent (𝓞 K) (fun i ↦ φ (s i)) := hs.map' φ.toLinearMap φ.ker
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) A.carrier)) =
      Module.finrank (𝓞 K) B.carrier := by
    rw [Fintype.card_fin]
    exact φ.finrank_eq
  simp only [HermitianBundle.deg, HermitianBundle.arithDegree]
  rw [arithDegree_eq A.metric hs (Fintype.card_fin _), arithDegree_eq B.metric ht hcard]
  simp only [GroundTheory.Heights₂.Heights.degreeWith, hg]
  have hmap : (Submodule.span (𝓞 K) (Set.range s)).map φ.toLinearMap =
      Submodule.span (𝓞 K) (Set.range fun i ↦ φ (s i)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [Nat.card_congr (Submodule.Quotient.equiv _ _ φ hmap).toEquiv]

theorem deg_sub_top {K : Type u} [Field K] [NumberField K] (M : HermitianBundle.{v} K) :
    (M.sub ⊤).deg = M.deg :=
  deg_eq_of_linearEquiv (M.sub ⊤) M Submodule.topEquiv fun σ _ s ↦
    gramDet_comap M.metric (⊤ : Submodule (𝓞 K) M.carrier).subtype (Submodule.injective_subtype _) σ s

theorem deg_sub_comap {K : Type u} [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    {F G : Submodule (𝓞 K) M.carrier} (hGF : G ≤ F) :
    ((M.sub F).sub (G.comap F.subtype)).deg = (M.sub G).deg :=
  deg_eq_of_linearEquiv _ _ (Submodule.comapSubtypeEquivOfLe hGF) fun σ _ s ↦ by
    have e1 := gramDet_comap (M.sub F).metric (G.comap F.subtype).subtype
      (Submodule.injective_subtype _) σ s
    have e2 := gramDet_comap M.metric F.subtype (Submodule.injective_subtype _) σ
      fun i ↦ (G.comap F.subtype).subtype (s i)
    have e3 := gramDet_comap M.metric G.subtype (Submodule.injective_subtype _) σ
      fun i ↦ Submodule.comapSubtypeEquivOfLe hGF (s i)
    exact e1.trans (e2.trans e3.symm)

end ChainSum

theorem ChainSum.proof (h1 : ExactSequence.Statement.{u, v}) : ChainSum.Statement.{u, v} := by
  intro K _ _ M k
  induction k with
  | zero =>
    intro c h0 _ _
    have hl : c (Fin.last 0) = ⊤ := h0
    rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero, hl, ChainSum.deg_sub_top]
  | succ k ih =>
    intro c h0 hmono hc
    have hmono' : Antitone fun a : Fin (k + 1) ↦ c a.castSucc :=
      fun a b hab ↦ hmono (Fin.castSucc_le_castSucc_iff.mpr hab)
    have hIH := ih (fun a ↦ c a.castSucc) h0 hmono' fun a ↦ hc _
    have hle : c (Fin.last (k + 1)) ≤ c (Fin.last k).castSucc :=
      hmono (Fin.castSucc_lt_last _).le
    have hE := h1 K (M.sub (c (Fin.last k).castSucc))
      ((c (Fin.last (k + 1))).comap (c (Fin.last k).castSucc).subtype)
      ((hc (Fin.last (k + 1))).comap_subtype _)
    rw [ChainSum.deg_sub_comap M hle] at hE
    rw [Fin.sum_univ_castSucc, hIH, hE, add_assoc]
    congr 1
    rw [add_comm]
    rfl

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
