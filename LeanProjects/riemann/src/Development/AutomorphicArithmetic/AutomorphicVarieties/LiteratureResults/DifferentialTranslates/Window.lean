import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.WindowOne

noncomputable section

namespace UpperTheory.V.Lit.Dr

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}

private def stab (G : Geo Γ V S d) (s : S) : Subgroup Γ where
  carrier := {γ | G.σ γ s = s}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Equiv.Perm.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, Equiv.Perm.inv_eq_iff_eq, ha]

private def geoStab (G : Geo Γ V S d) (s : S) : Geo (stab G s) V Unit d where
  ρ := G.ρ.comp (stab G s).subtype
  σ := 1
  ξ := 1
  Y := G.Y
  isOpen := G.isOpen
  maps γ := G.maps γ.1

private theorem geoStab_proper (G : Geo Γ V S d) (hG : G.Proper) (s : S) : (geoStab G s).Proper := by
  intro K hK hKc u u'
  refine ((hG K hK hKc s s).preimage (f := fun γ : stab G s => γ.1) Subtype.val_injective.injOn).subset ?_
  rintro γ ⟨-, h⟩
  exact ⟨γ.2, h⟩

private theorem exists_rep (G : Geo Γ V S d) :
    ∃ r : S → S, (∀ s, ∃ δ : Γ, G.σ δ⁻¹ s = r s) ∧ ∀ (γ : Γ) s, r (G.σ γ s) = r s := by
  let R : Setoid S :=
    { r := fun a b => ∃ γ : Γ, G.σ γ a = b
      iseqv :=
        ⟨fun a => ⟨1, by simp⟩,
          fun ⟨γ, h⟩ => ⟨γ⁻¹, by rw [map_inv, Equiv.Perm.inv_eq_iff_eq, h]⟩,
          fun ⟨γ, h⟩ ⟨δ, h'⟩ => ⟨δ * γ, by rw [map_mul, Equiv.Perm.mul_apply, h, h']⟩⟩ }
  refine ⟨fun s => (Quotient.mk R s).out, fun s => ?_, fun γ s => ?_⟩
  · obtain ⟨γ, h⟩ : R.r (Quotient.mk R s).out s := Quotient.exact (Quotient.out_eq _)
    exact ⟨γ, by rw [map_inv, Equiv.Perm.inv_eq_iff_eq, h]⟩
  · have h : Quotient.mk R s = Quotient.mk R (G.σ γ s) := Quotient.sound ⟨γ, rfl⟩
    beta_reduce
    rw [← h]

theorem window : Window := by
  intro Γ V S _ _ _ _ d G hG
  classical
  obtain ⟨r, hr, hrr⟩ := exists_rep G
  choose W hW using fun s => windowOne _ V Unit d (geoStab G s) inferInstance (geoStab_proper G hG s)
  refine ⟨fun s => if r s = s then W s () else ∅, fun s => ?_, fun s p hp => ?_, fun s p hp => ?_⟩
  · beta_reduce
    split_ifs
    · exact (hW s).1 ()
    · exact ⟨isOpen_empty, Set.empty_subset _⟩
  · obtain ⟨δ, hδ⟩ := hr s
    obtain ⟨h, hh⟩ := (hW (r s)).2.1 () _ (G.maps δ⁻¹ p hp)
    have h1 : G.σ (δ * h.1)⁻¹ s = r s := by
      rw [mul_inv_rev, map_mul, Equiv.Perm.mul_apply, hδ]
      exact (h⁻¹).2
    have h2 : r (r s) = r s := by
      conv_lhs => rw [← hδ]
      exact hrr _ _
    refine ⟨δ * h.1, ?_⟩
    beta_reduce
    rw [h1, if_pos h2, mul_inv_rev, map_mul]
    exact hh
  · obtain ⟨δ, hδ⟩ := hr s
    obtain ⟨N, hN, hfin⟩ := (hW (r s)).2.2 () _ (G.maps δ⁻¹ p hp)
    refine ⟨G.ρ δ⁻¹ ⁻¹' N, (G.ρ δ⁻¹).continuous.continuousAt.preimage_mem_nhds hN,
      (hfin.image fun h => δ * h.1).subset ?_⟩
    rintro γ ⟨x, hx, hγ⟩
    beta_reduce at hγ
    split_ifs at hγ with h0
    · have h1 : G.σ γ⁻¹ s = r s := by rw [← h0, hrr]
      have h2 : δ⁻¹ * γ ∈ stab G (r s) := by
        change G.σ (δ⁻¹ * γ) (r s) = r s
        have h3 : G.σ γ (r s) = s := by rw [← h1, map_inv]; simp
        rw [map_mul, Equiv.Perm.mul_apply, h3, hδ]
      refine ⟨⟨_, h2⟩, ⟨_, hx, ?_⟩, by simp⟩
      rw [h1] at hγ
      change G.ρ (δ⁻¹ * γ)⁻¹ (G.ρ δ⁻¹ x) ∈ W (r s) ()
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_rev, inv_inv, mul_inv_cancel_right]
      exact hγ
    · exact hγ.elim

end UpperTheory.V.Lit.Dr
