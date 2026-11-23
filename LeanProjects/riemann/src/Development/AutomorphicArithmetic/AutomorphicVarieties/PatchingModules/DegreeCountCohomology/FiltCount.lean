import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.filtCount :
    ∀ (Z Y : Type) [AddCommGroup Z] [AddCommGroup Y] (r : ℕ) (f : Fin r → Z →+ Y) (P : Fin r → Set Y), (∀ z, (∀ i, f i z = 0) → z = 0) → (∀ i, (P i).Finite) → (∀ i z, (∀ j, j < i → f j z = 0) → f i z ∈ P i) → Finite Z ∧ Nat.card Z ≤ ∏ i, (P i).ncard := by
  intro Z Y _ _ r
  induction r generalizing Z with
  | zero =>
    intro f P hinj _ _
    have hsub : Subsingleton Z := ⟨fun a b => by
      rw [hinj a (fun i => i.elim0), hinj b (fun i => i.elim0)]⟩
    refine ⟨inferInstance, ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact Finite.card_le_one_iff_subsingleton.2 hsub
  | succ r ih =>
    intro f P hinj hP hfilt
    obtain ⟨hKfin, hKcard⟩ := ih (f 0).ker (fun i => (f i.succ).comp (f 0).ker.subtype)
      (fun i => P i.succ)
      (by
        intro z hz
        have h0 : f 0 z.1 = 0 := AddMonoidHom.mem_ker.1 z.2
        apply Subtype.ext
        apply hinj
        intro i
        cases i using Fin.cases with
        | zero => exact h0
        | succ j => exact hz j)
      (fun i => hP i.succ)
      (by
        intro i z hz
        apply hfilt i.succ z.1
        intro j hj
        cases j using Fin.cases with
        | zero => exact AddMonoidHom.mem_ker.1 z.2
        | succ j' => exact hz j' (Fin.succ_lt_succ_iff.1 hj))
    have hrange : ((f 0).range : Set Y) ⊆ P 0 := by
      rintro _ ⟨z, rfl⟩
      exact hfilt 0 z (fun j hj => absurd hj (Fin.not_lt_zero j))
    haveI : Finite (f 0).range := ((hP 0).subset hrange).to_subtype
    have e := QuotientAddGroup.quotientKerEquivRange (f 0)
    haveI : Finite (Z ⧸ (f 0).ker) := Finite.of_equiv _ e.toEquiv.symm
    haveI : Finite Z := Finite.of_addSubgroup_quotient (f 0).ker
    refine ⟨inferInstance, ?_⟩
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (f 0).ker, Nat.card_congr e.toEquiv,
      Fin.prod_univ_succ]
    refine Nat.mul_le_mul ?_ hKcard
    calc Nat.card (f 0).range = ((f 0).range : Set Y).ncard := Nat.card_coe_set_eq _
      _ ≤ (P 0).ncard := Set.ncard_le_ncard hrange (hP 0)
