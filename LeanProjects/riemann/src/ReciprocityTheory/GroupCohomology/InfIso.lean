import ReciprocityTheory.GroupCohomology.CardLenStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.ResNormalHolds
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.FiniteLevel
import ReciprocityTheory.GroupCohomology.Shapiro
import ReciprocityTheory.GroupCohomology.Section
import ReciprocityTheory.GroupCohomology.InfIsoB

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function Topology

noncomputable section

universe u

namespace InflationIsomorphism

variable {R : Type u} [CommRing R]

theorem H_comm {A B A' B' : Cx R} (i : Hom A B) (i' : Hom A' B') (α : Hom A A') (β : Hom B B')
    (h : ∀ n x, β.f n (i.f n x) = i'.f n (α.f n x)) (n : ℕ) (z : A.H n) :
    β.H n (i.H n z) = i'.H n (α.H n z) := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [InflationRestrictionInvariants.H_mk]
  congr 1
  exact Subtype.ext (h n x)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]

theorem admissible_character_inv (hN : IsClosed (N : Set G)) (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (M : TRep R G) [DiscreteTopology M.V] {Q : TRep R (G ⧸ N)} {P : Pair Q M} (hP : IsInvRep M N Q P)
    {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)} (hC : IsInvRep (CG M) N QC PC)
    {QQ : TRep R (G ⧸ N)} {PQ : Pair QQ (QG M)} (hQ : IsInvRep (QG M) N QQ PQ) :
    admitted (invPair hP hC (iCG M) (iCG_equiv M))
      (invPair hC hQ (pLin M) (pLin_equiv M)) := by
  have := inv_disc hP
  have := inv_disc hC
  have := inv_disc hQ
  refine ⟨rfl, rfl, emb_disc _ fun a b h => ?_, fun c => ?_, ?_⟩
  · have h' := congrArg PC.u h
    rw [invPair_u, invPair_u] at h'
    exact hP.2.1.injective (iCG_inj M h')
  · constructor
    · intro hc
      have h1 := congrArg PQ.u hc
      rw [invPair_u, map_zero, pLin_eq_zero] at h1
      obtain ⟨m, hm⟩ := h1
      have hmN : ∀ g ∈ N, M.rho g m = m := fun g hg => iCG_inj M (by
        rw [iCG_equiv, hm, inv_mem hC c g hg])
      obtain ⟨q, rfl⟩ := (hP.2.2 m).2 hmN
      refine ⟨q, hC.2.1.injective ?_⟩
      rw [invPair_u, hm]
    · rintro ⟨q, rfl⟩
      apply hQ.2.1.injective
      rw [invPair_u, invPair_u, map_zero, pLin_eq_zero]
      exact ⟨_, rfl⟩
  · have hs : Surjective (invPair hC hQ (pLin M) (pLin_equiv M)).u := by
      intro y
      obtain ⟨c, hcN, hc⟩ := inv_lift (R := R) N hN hW (CG M) (QG M) (pLin M)
        (pLin_equiv M) (pLin_surj M) (PQ.u y) (inv_mem hQ y)
      obtain ⟨c', rfl⟩ := (hC.2.2 c).2 hcN
      exact ⟨c', hQ.2.1.injective (by rw [invPair_u, hc])⟩
    exact ⟨surjInv hs, continuous_of_discreteTopology, surjInv_eq hs⟩

theorem main (hN : IsClosed (N : Set G)) (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (n : ℕ) : ∀ (M : TRep R G) [DiscreteTopology M.V] (Q : TRep R (G ⧸ N)) (P : Pair Q M),
    IsInvRep M N Q P → Bijective (P.hom.H n) := by
  induction n with
  | zero => exact fun M _ Q P hP => deg0 M Q P hP
  | succ n ih =>
  intro M _ Q P hP
  have hC := InflationRestrictionInvariants.invariants_isInvRep (CG M) N
  have hQ := InflationRestrictionInvariants.invariants_isInvRep (QG M) N
  have hadm := admissible_character_inv hN hW M hP hC hQ
  have hs := admissibility_holds R (G ⧸ N) _ _ _ _ _ hadm
  have hs' := admissibility_holds R G _ _ _ _ _ (admissible_compact_discrete M)
  obtain ⟨⟨δ, hδ, hL⟩, -⟩ := lES_holds R _ _ _ _ _ hs
  obtain ⟨⟨δ', hδ', hL'⟩, -⟩ := lES_holds R _ _ _ _ _ hs'
  have c1 := invPair_comm hP hC (iCG M) (iCG_equiv M) continuous_of_discreteTopology
  have c2 := invPair_comm hC hQ (pLin M) (pLin_equiv M)
    (pLin_cont M)
  have hnat := connNat_holds R _ _ _ _ _ _ _ _ _ _ P.hom _ _ δ δ' hs hs' c1 c2 hδ hδ'
  have hβ := ih (CG M) _ _ hC
  have hγ := ih (QG M) _ _ hQ
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    obtain ⟨x, rfl⟩ := ((hL.exA n) y).1 (QC_acyc M hC n _)
    rw [← hnat] at hy
    obtain ⟨c, hc⟩ := ((hL'.exC n) _).1 hy
    obtain ⟨c', rfl⟩ := hβ.2 c
    rw [← H_comm _ (pP M).hom _ _ c2 n c'] at hc
    rw [← hγ.1 hc]
    exact ((hL.exC n) _).2 ⟨c', rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := ((hL'.exA n) y).1 (CG_acyc M n _)
    obtain ⟨x', rfl⟩ := hγ.2 x
    exact ⟨δ n x', (hnat n x').symm⟩

end InflationIsomorphism

end

end ReciprocityTheory.Coh
