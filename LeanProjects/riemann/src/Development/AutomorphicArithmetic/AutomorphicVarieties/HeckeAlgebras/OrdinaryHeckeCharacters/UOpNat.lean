import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.uOpNat :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (A' M' : Type) [CommRing A'] [AddCommGroup M'] [Module A' M'] (π' : Representation A' G M') (f : M →+ M') (a : G), a ∈ I.P → ∀ v, (∀ u ∈ I.N, f (π (u * a) v) = π' (u * a) (f v)) → f (I.uOp π a v) = I.uOp π' a (f v) := by
  intro G _ I A M _ _ _ π A' M' _ _ _ π' f a ha v hv
  have hfin : Finite (↥I.N ⧸ (I.Nconj a).subgroupOf I.N) :=
    Subgroup.index_ne_zero_iff_finite.mp (I.fin_N a ha)
  have _ := Fintype.ofFinite (↥I.N ⧸ (I.Nconj a).subgroupOf I.N)
  unfold Iwa.uOp
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply,
    LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun q _ => hv _ (Quotient.out q).2
