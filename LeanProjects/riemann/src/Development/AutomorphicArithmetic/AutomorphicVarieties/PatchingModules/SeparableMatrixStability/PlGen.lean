import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProBurnside

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pl_gen :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (H : Subgroup Γ) [H.Normal], IsOpen (H : Set Γ) → PL l H = ⊥ → Finite (HomL l H) → TopFG Γ ∧ ∀ b : ℕ, Nat.card (HomL l H) ≤ b → ∃ z : Fin b → H, TopGen (Set.range z) := by
  intro l _ Γ _ _ _ _ _ H _ hH hPL hfin
  have hpro : IsProL l H := ((pl_props l Γ H hH).2.2.2.2.1).1 hPL
  have hcl : IsClosed (H : Set Γ) := Subgroup.isClosed_of_isOpen H hH
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hcl.isCompact
  obtain ⟨-, hgen⟩ := topGen_of_hom l H hpro
  have key : ∀ b : ℕ, Nat.card (HomL l H) ≤ b → ∃ z : Fin b → H, TopGen (Set.range z) := by
    intro b hb
    have hf : {f : H →* Multiplicative (ZMod l) | IsOpen (f.ker : Set H)}.Finite := Set.finite_coe_iff.1 hfin
    have hn : {f : H →* Multiplicative (ZMod l) | IsOpen (f.ker : Set H)}.ncard ≤ l ^ b := by
      rw [← Nat.card_coe_set_eq]
      exact hb.trans (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
    exact hgen b hf hn
  refine ⟨?_, key⟩
  obtain ⟨z, hz⟩ := key _ le_rfl
  haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  refine ⟨Subtype.val '' Set.range z ∪ Set.range (Quotient.out : Γ ⧸ H → Γ),
    ((Set.finite_range z).image _).union (Set.finite_range _), ?_⟩
  rw [topGen_iff]
  set K := (Subgroup.closure (Subtype.val '' Set.range z ∪ Set.range (Quotient.out : Γ ⧸ H → Γ))).topologicalClosure
  have hsub : Subtype.val '' ((Subgroup.closure (Set.range z) : Subgroup H) : Set H) ⊆ (K : Set Γ) := by
    intro y hy
    have hmap : y ∈ (Subgroup.closure (Set.range z)).map H.subtype := hy
    rw [MonoidHom.map_closure] at hmap
    exact Subgroup.le_topologicalClosure _ (Subgroup.closure_mono Set.subset_union_left hmap)
  have hHK : H ≤ K := by
    intro h hh
    have h1 : (⟨h, hh⟩ : H) ∈ closure ((Subgroup.closure (Set.range z) : Subgroup H) : Set H) := hz ⟨h, hh⟩
    have h2 := mem_closure_image continuous_subtype_val.continuousAt h1
    exact closure_minimal hsub (Subgroup.isClosed_topologicalClosure _) h2
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  have hg : g = (QuotientGroup.mk g : Γ ⧸ H).out * (h : Γ)⁻¹ := by
    rw [hh]
    group
  rw [hg]
  refine K.mul_mem ?_ (hHK (H.inv_mem h.2))
  exact Subgroup.le_topologicalClosure _ (Subgroup.subset_closure (Or.inr ⟨_, rfl⟩))
