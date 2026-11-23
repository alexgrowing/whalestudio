import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb.PushforwardPsi

private theorem exF {Γ A C : Type} [Group Γ] [CommGroup A] [CommGroup C] (c : Γ →* A) (ψ : Γ →* C)
    (h : ∀ s, c s = 1 → ψ s = 1) : ∃ f : A → C, ∀ a s, f (a * (c s)⁻¹) = f a * ψ s := by
  have h1 : ∀ a : A, ∃ s, c s = a⁻¹ * (QuotientGroup.mk a : A ⧸ c.range).out := fun a =>
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk a : A ⧸ c.range)).symm
  choose σ hσ using h1
  refine ⟨fun a => ψ (σ a), fun a s => ?_⟩
  have e : (QuotientGroup.mk (a * (c s)⁻¹) : A ⧸ c.range) = QuotientGroup.mk a :=
    QuotientGroup.eq.2 ⟨s, by simp⟩
  have h2 := h ((σ (a * (c s)⁻¹))⁻¹ * (σ a * s)) (by
    rw [map_mul, map_mul, map_inv, hσ, hσ, e, inv_mul_eq_one, mul_inv, inv_inv, mul_right_comm])
  rw [map_mul, map_inv, inv_mul_eq_one, map_mul] at h2
  exact h2

private theorem exC (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] :
    ∃ c : (Ω ≃ₐ[ℚ] Ω) →* (ZMod M)ˣ, ∀ s, cycM M s = c s ∧ ∀ z : Ω, z ^ M = 1 → s z = z ^ (c s : ZMod M).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨hζ.autToPow ℚ, fun s => ?_⟩
  have hs : ∀ z : Ω, z ^ M = 1 → s z = z ^ (hζ.autToPow ℚ s : ZMod M).val := fun w hw => by
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
    rw [map_pow, ← hζ.autToPow_spec ℚ s, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨?_, hs⟩
  have hM := cycM_spec M s ⟨_, hs⟩
  apply Units.ext
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ((hM ζ hζ.pow_eq_one).symm.trans (hs ζ hζ.pow_eq_one))

private theorem push_prod {Γ A B B' V : Type} [Group Γ] [AddCommMonoid V] [Fintype A] [Fintype B'] [DecidableEq B]
    {i1 : Fintype (A × B')} {i2 : DecidableEq (A × B)} (g : B' → B) (Z : Γ → A × B' → V) (s : Γ) (a : A) (y : B) :
    @push Γ (A × B) (A × B') i1 i2 V _ (Prod.map id g) Z s (a, y) = ∑ y', if g y' = y then Z s (a, y') else 0 := by
  obtain rfl : i1 = instFintypeProd A B' := Subsingleton.elim _ _
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun y' _ => ?_
  by_cases h : g y' = y <;> simp [h]

end UpperTheory.V.Z.Kato.Nb.PushforwardPsi

open UpperTheory.V.Z.Kato.Nb.PushforwardPsi in
theorem UpperTheory.V.Z.Kato.Nb.sPushPsi :
    UpperTheory.V.Z.Kato.Nb.SPushPsi := by
  intro l _ Ω _ _ _ cf ρ p n _ ψw hψ Y hc hp hcont hO
  obtain ⟨c, hcs⟩ := exC Ω p
  obtain ⟨f, hf⟩ := exF c ψw fun s hs => hψ s fun z hz => by
    rw [(hcs s).2 z hz, hs, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hz, pow_one]
  refine ⟨fun r s x => ∑ t, if f t = x.1 then Y r s (t, x.2) else 0, fun r s s' x => ?_, fun r x i => ?_,
    fun r s x i => ?_, fun r s => ?_, fun r s y => ?_⟩
  · have e : ∑ t, (if f t = (x * (ψw.prod (cycMod ℚ Ω l r)⁻¹) s).1 then
        Y r s' (t, (x * (ψw.prod (cycMod ℚ Ω l r)⁻¹) s).2) else 0) =
        ∑ t, if f t = x.1 then Y r s' ((t, x.2) * cycT l r p s) else 0 := by
      symm
      refine Fintype.sum_equiv (Equiv.mulRight (c s)⁻¹) _ _ fun t => ?_
      simp [hf, cycT, (hcs s).1]
    beta_reduce
    rw [e, Matrix.mulVec_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · exact hc r s s' _
    · simp
  · simp only [Finset.sum_apply]
    refine continuous_finset_sum _ fun t _ => ?_
    split_ifs
    · exact hcont r _ i
    · exact continuous_const
  · simp only [Finset.sum_apply]
    refine sum_mem fun t _ => ?_
    split_ifs
    · exact hO r s _ i
    · exact zero_mem _
  · funext ⟨a, y⟩
    rw [push_prod]
    have e : ∀ t, Y r s (t, y) = ∑ y', if redL l r y' = y then Y (r + 1) s (t, y') else 0 := fun t => by
      rw [hp r, push_prod]
    simp only [e]
    have e2 : ∀ (P : Prop) [Decidable P] {ι : Type} [Fintype ι] (v : ι → Fin 2 → Qbar l),
        (if P then ∑ j, v j else 0) = ∑ j, if P then v j else 0 := fun P _ _ _ v => by split_ifs <;> simp
    simp only [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun t _ => ?_
    change (if f t = a then if redL l r y' = y then _ else 0 else 0) = if redL l r y' = y then if f t = a then _ else 0 else 0
    split_ifs <;> rfl
  · rw [Finset.sum_comm]
    simp
