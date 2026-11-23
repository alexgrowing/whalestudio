import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.InvariantSubmoduleEqSpanEigenbasisOfSeparable
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.CardDvdOfPartitionEqualSize

open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.exists_stabilizer_index_dvd_of_not_irreducible_restriction :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) K), U3.MatIrr ⊤ r →
      ∀ N : Subgroup G, commutator G ≤ N → (∃ u ∈ N, (r u).charpoly.Separable) → ¬ U3.MatIrr N r →
      ∃ (W : Submodule K (Fin n → K)) (S : Subgroup G), W ≠ ⊥ ∧ W ≠ ⊤ ∧ N ≤ S ∧ (∀ g, g ∈ S ↔ ∀ v ∈ W, r g *ᵥ v ∈ W) ∧
        S.index ∣ n := by
  intro K G _ _ _ n r hirr N hN hu hnot
  classical
  obtain ⟨u, huN, hsep⟩ := hu
  have hconj : ∀ g h : G, h ∈ N → g⁻¹ * h * g ∈ N := by
    intro g h hh
    have hc : h⁻¹ * g⁻¹ * h⁻¹⁻¹ * g⁻¹⁻¹ ∈ N :=
      hN (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have e : g⁻¹ * h * g = h * (h⁻¹ * g⁻¹ * h⁻¹⁻¹ * g⁻¹⁻¹) := by
      group
    rw [e]
    exact N.mul_mem hh hc
  have hr1 : ∀ g : G, r g * r g⁻¹ = 1 := by
    intro g
    rw [← map_mul, mul_inv_cancel, map_one]
  have hr2 : ∀ g : G, r g⁻¹ * r g = 1 := by
    intro g
    rw [← map_mul, inv_mul_cancel, map_one]
  let Inv : Submodule K (Fin n → K) → Prop := fun X => ∀ g ∈ N, ∀ v ∈ X, r g *ᵥ v ∈ X
  let tr : G → Submodule K (Fin n → K) → Submodule K (Fin n → K) :=
    fun g X => X.map (Matrix.toLin' (r g))
  have mem_tr : ∀ g X v, v ∈ tr g X ↔ r g⁻¹ *ᵥ v ∈ X := by
    intro g X v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
      exact hx
    · intro hv
      refine Submodule.mem_map.2 ⟨_, hv, ?_⟩
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hr1, Matrix.one_mulVec]
  have tr_inv : ∀ g X, Inv X → Inv (tr g X) := by
    intro g X hX h hh v hv
    rw [mem_tr] at hv ⊢
    have e : r g⁻¹ *ᵥ (r h *ᵥ v) = r (g⁻¹ * h * g) *ᵥ (r g⁻¹ *ᵥ v) := by
      simp only [Matrix.mulVec_mulVec, map_mul, mul_assoc, hr1, mul_one]
    rw [e]
    exact hX _ (hconj g h hh) _ hv
  have htr_mul : ∀ g h X, tr (g * h) X = tr g (tr h X) := by
    intro g h X
    ext v
    rw [mem_tr, mem_tr, mem_tr, _root_.mul_inv_rev, map_mul, ← Matrix.mulVec_mulVec]
  have htr_one : ∀ X, tr 1 X = X := by
    intro X
    ext v
    rw [mem_tr, inv_one, map_one, Matrix.one_mulVec]
  obtain ⟨b, hb⟩ := Ws.invariant_submodule_eq_span_eigenbasis_of_separable K n (r u) hsep
  have hspan : ∀ X, Inv X → X = Submodule.span K (b '' {i | b i ∈ X}) :=
    fun X hX => hb X (hX u huN)
  have hrank : ∀ X, Inv X → Module.finrank K X = {i | b i ∈ X}.ncard := by
    intro X hX
    have e := hspan X hX
    calc Module.finrank K X = Module.finrank K (Submodule.span K (b '' {i | b i ∈ X})) := by
          rw [← e]
      _ = {i | b i ∈ X}.ncard := by
          have hli := b.linearIndependent.comp
            (Subtype.val : {i // i ∈ {i | b i ∈ X}} → Fin n) Subtype.val_injective
          rw [Set.image_eq_range]
          rw [finrank_span_eq_card (R := K) (b := fun x : {i // i ∈ {i | b i ∈ X}} => b x) hli,
            ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  obtain ⟨W0, hW0i, hW0b, hW0t⟩ : ∃ W, Inv W ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
    unfold U3.MatIrr at hnot
    push_neg at hnot
    exact hnot
  have hex : ∃ k, ∃ X, Inv X ∧ X ≠ ⊥ ∧ Module.finrank K X = k := ⟨_, W0, hW0i, hW0b, rfl⟩
  obtain ⟨W, hWi, hWb, hWk⟩ := Nat.find_spec hex
  have hmin : ∀ X, Inv X → X ≠ ⊥ → Module.finrank K W ≤ Module.finrank K X := by
    intro X hX hXb
    rw [hWk]
    exact Nat.find_min' hex ⟨X, hX, hXb, rfl⟩
  have hWt : W ≠ ⊤ := by
    intro h
    have h1 := hmin W0 hW0i hW0b
    have h2 := Submodule.finrank_lt hW0t
    rw [h, finrank_top] at h1
    omega
  have tr_ne : ∀ g X, X ≠ ⊥ → tr g X ≠ ⊥ := by
    intro g X hX h
    apply hX
    rw [eq_bot_iff]
    intro v hv
    have hm : r g *ᵥ v ∈ tr g X := by
      rw [mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
      exact hv
    rw [h, Submodule.mem_bot] at hm
    have e := congrArg (fun w => r g⁻¹ *ᵥ w) hm
    simp only [Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec, Matrix.mulVec_zero] at e
    rw [e]
    exact Submodule.zero_mem _
  have trW_rank : ∀ g, Module.finrank K (tr g W) = Module.finrank K W := fun g =>
    le_antisymm (Submodule.finrank_map_le _ _) (hmin _ (tr_inv g W hWi) (tr_ne g W hWb))
  have key : ∀ g, (∀ v ∈ W, r g *ᵥ v ∈ W) → tr g W = W := by
    intro g hg
    apply Submodule.eq_of_le_of_finrank_le
    · intro v hv
      rw [mem_tr] at hv
      have e : v = r g *ᵥ (r g⁻¹ *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, hr1, Matrix.one_mulVec]
      rw [e]
      exact hg _ hv
    · rw [trW_rank]
  let S : Subgroup G :=
    { carrier := {g | tr g W = W}
      mul_mem' := by
        intro a c ha hc
        simp only [Set.mem_setOf_eq] at ha hc ⊢
        rw [htr_mul, hc, ha]
      one_mem' := htr_one W
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← htr_mul, inv_mul_cancel, htr_one] }
  have hS : ∀ g, g ∈ S ↔ ∀ v ∈ W, r g *ᵥ v ∈ W := by
    intro g
    constructor
    · intro hg v hv
      have hm : r g *ᵥ v ∈ tr g W := by
        rw [mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
        exact hv
      have hg' : tr g W = W := hg
      rw [hg'] at hm
      exact hm
    · exact key g
  refine ⟨W, S, hWb, hWt, fun g hg => (hS g).2 (hWi g hg), hS, ?_⟩
  have huniq : ∀ g1 g2 i, b i ∈ tr g1 W → b i ∈ tr g2 W → tr g1 W = tr g2 W := by
    intro g1 g2 i h1 h2
    have hI : Inv (tr g1 W ⊓ tr g2 W) := fun h hh v hv =>
      ⟨tr_inv g1 W hWi h hh v hv.1, tr_inv g2 W hWi h hh v hv.2⟩
    have hne : tr g1 W ⊓ tr g2 W ≠ ⊥ := by
      intro h
      have hm : b i ∈ tr g1 W ⊓ tr g2 W := ⟨h1, h2⟩
      rw [h, Submodule.mem_bot] at hm
      exact b.ne_zero i hm
    have hm := hmin _ hI hne
    have e1 : tr g1 W ⊓ tr g2 W = tr g1 W :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [trW_rank]; exact hm)
    have e2 : tr g1 W ⊓ tr g2 W = tr g2 W :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [trW_rank]; exact hm)
    exact e1.symm.trans e2
  have hcover : ∀ i, ∃ g, b i ∈ tr g W := by
    by_contra hc
    push_neg at hc
    obtain ⟨i, hi⟩ := hc
    have hUi : ∀ g ∈ (⊤ : Subgroup G), ∀ v ∈ ⨆ h, tr h W, r g *ᵥ v ∈ ⨆ h, tr h W := by
      intro g _ v hv
      refine Submodule.iSup_induction (fun h => tr h W)
        (motive := fun v => r g *ᵥ v ∈ ⨆ h, tr h W) hv ?_ ?_ ?_
      · intro h x hx
        refine Submodule.mem_iSup_of_mem (g * h) ?_
        rw [htr_mul, mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
        exact hx
      · show r g *ᵥ 0 ∈ ⨆ h, tr h W
        rw [Matrix.mulVec_zero]
        exact Submodule.zero_mem _
      · intro x y hx hy
        show r g *ᵥ (x + y) ∈ ⨆ h, tr h W
        rw [Matrix.mulVec_add]
        exact add_mem hx hy
    have hU := hirr _ hUi
    have hUb : (⨆ h, tr h W) ≠ ⊥ := by
      intro h
      apply hWb
      rw [eq_bot_iff, ← h]
      have := le_iSup (fun h => tr h W) 1
      rw [htr_one] at this
      exact this
    have hUt := hU.resolve_left hUb
    have hbi : b i ∈ ⨆ h, tr h W := by
      rw [hUt]
      exact Submodule.mem_top
    have hz : ∀ v ∈ ⨆ h, tr h W, b.repr v i = 0 := by
      intro v hv
      refine Submodule.iSup_induction (fun h => tr h W)
        (motive := fun v => b.repr v i = 0) hv ?_ ?_ ?_
      · intro g x hx
        have hx' : x ∈ tr g W := hx
        rw [hspan _ (tr_inv g W hWi), Module.Basis.mem_span_image] at hx'
        by_contra h0
        exact hi g (hx' (Finsupp.mem_support_iff.2 h0))
      · simp
      · intro x y hx hy
        simp only [map_add, Finsupp.add_apply]
        rw [hx, hy, add_zero]
    have := hz _ hbi
    simp at this
  let T : G ⧸ S → Set (Fin n) := fun q => {i | b i ∈ tr q.out W}
  have hT1 : ∀ q, (T q).ncard = Module.finrank K W := by
    intro q
    rw [← trW_rank q.out, hrank _ (tr_inv _ W hWi)]
  have hT2 : ∀ i, ∃! q, i ∈ T q := by
    intro i
    obtain ⟨g, hg⟩ := hcover i
    refine ⟨(g : G ⧸ S), ?_, ?_⟩
    · show b i ∈ tr (g : G ⧸ S).out W
      obtain ⟨a, ha⟩ : ∃ a, a = (g : G ⧸ S).out := ⟨_, rfl⟩
      rw [← ha]
      have hm : a⁻¹ * g ∈ S := by
        rw [ha]
        exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : G ⧸ S))
      have hm' : tr (a⁻¹ * g) W = W := hm
      have e : tr (a * (a⁻¹ * g)) W = tr a W := by
        rw [htr_mul, hm']
      rw [mul_inv_cancel_left] at e
      rw [← e]
      exact hg
    · intro q hq
      have e := huniq _ _ i hq hg
      have hm : q.out⁻¹ * g ∈ S := by
        show tr _ W = W
        rw [htr_mul, ← e, ← htr_mul, inv_mul_cancel, htr_one]
      exact (QuotientGroup.out_eq' q).symm.trans (QuotientGroup.eq.mpr hm)
  have hc := Ws.card_dvd_of_partition_equal_size (Fin n) (G ⧸ S) T (Module.finrank K W) hT1 hT2
  have hn : Nat.card (Fin n) = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)
  rw [hn] at hc
  exact hc
