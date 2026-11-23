import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.propCp :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a : G), a ∈ I.P → ∀ v ∈ fixd π I.N, I.uOp π a v - ((I.Nconj a).relIndex I.N : A) • π a v ∈ I.jacKer π := by
  intro G _ I A M _ _ _ π a ha v _
  have hfin : ((I.Nconj a).subgroupOf I.N).FiniteIndex := ⟨I.fin_N a ha⟩
  haveI : Fintype (I.N ⧸ (I.Nconj a).subgroupOf I.N) := Fintype.ofFinite _
  have hc : (I.Nconj a).relIndex I.N = Fintype.card (I.N ⧸ (I.Nconj a).subgroupOf I.N) := by
    rw [← Nat.card_eq_fintype_card]; rfl
  have hs : (((I.Nconj a).relIndex I.N : ℕ) : A) • π a v
      = ∑ _q : I.N ⧸ (I.Nconj a).subgroupOf I.N, π a v := by
    rw [Finset.sum_const, Finset.card_univ, hc, Nat.cast_smul_eq_nsmul]
  rw [hs, Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun q _ => Submodule.subset_span ?_
  refine ⟨(q.out : I.N), I.N_le (q.out).2, π a v, ?_⟩
  rw [map_mul]; rfl
