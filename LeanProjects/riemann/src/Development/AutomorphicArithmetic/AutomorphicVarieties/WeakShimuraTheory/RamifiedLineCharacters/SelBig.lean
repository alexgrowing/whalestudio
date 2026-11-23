import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GwLower
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.RamCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.LocHoms

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.selBig :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (S₀ S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), S₀ ⊆ S → ContainsAbove S₀ l → ContAction ρ →
      (∀ v ∈ S, v ∉ S₀ → TrivAt l (ρ.comp (toGS Ω _)) v) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ m0 : M, m0 ≠ 0 →
        2 ^ (S.card - S₀.card) ≤ Nat.card (gysSel S₀ S ρ Av m0) * (Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ (Module.finrank ℚ F + S₀.card)) := by
  classical
  intro P F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl S₀ S ρ hSS hS₀ hρ htr Av hA m0 hm0
  have hS : ContainsAbove S l := fun v hv => hSS (hS₀ v hv)
  have e := gwLower P.gf P.gw F Ω l M hl S ρ hS hρ Av hA (gysL S₀ S ρ Av m0)
  have h0 : ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) ≤ Nat.card M ^ S.card := by
    have := Finset.prod_le_pow_card Finset.univ (fun v : S => Nat.card (H0 (ρ.comp (locFam S Av v)))) (Nat.card M)
      (fun v _ => Nat.card_le_card_of_injective _ Subtype.val_injective)
    rwa [Finset.card_univ, Fintype.card_coe] at this
  have hloc : ∀ v : S, (if v.1 ∈ S₀ then 1 else 2 * Nat.card M) ≤ Nat.card (gysL S₀ S ρ Av m0 v) := by
    intro v
    by_cases hv : v.1 ∈ S₀
    · rw [if_pos hv, show gysL S₀ S ρ Av m0 v = ⊥ from if_pos hv]
      exact Nat.card_pos
    · rw [if_neg hv, show gysL S₀ S ρ Av m0 v = _ from if_neg hv]
      have ht := htr v.1 v.2 hv (Av v) (hA v)
      obtain ⟨φ₁, h1, φ₂, h2, a1, a2, g, a3, a4⟩ := locHoms P.loc.lt P.loc.le P.uo F Ω l (Av v) v.1 (hA v)
        (fun h => hv (hS₀ _ h)) (fun g hg => (ht g hg).2)
      have hc : ContAction (ρ.comp (locFam S Av v)) := hρ.comp ((continuous_locFam S Av v).prodMap continuous_id)
      obtain ⟨-, f1, -, -⟩ := P.loc.lf F Ω l 1 M (Av v) _ v.1 one_pos (hA v) hc
      exact ramCard _ _ M _ _ m0 (fun g => (ht g.1 g.2).1) hm0 f1 φ₁ h1 φ₂ h2 a1 a2 ⟨g, a3, a4⟩
  have h1 : (2 * Nat.card M) ^ (S.card - S₀.card) ≤ ∏ v : S, Nat.card (gysL S₀ S ρ Av m0 v) := by
    refine le_trans (le_of_eq ?_) (Finset.prod_le_prod' fun v _ => hloc v)
    rw [Finset.prod_coe_sort S (fun v => if v ∈ S₀ then 1 else 2 * Nat.card M), Finset.prod_ite, Finset.prod_const_one, one_mul,
      Finset.prod_const, ← Finset.sdiff_eq_filter, Finset.card_sdiff_of_subset hSS]
  have hpos : 0 < Nat.card M ^ (S.card - S₀.card) := pow_pos Nat.card_pos _
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [← mul_pow]
  refine h1.trans (e.trans ((Nat.mul_le_mul_left _ h0).trans (le_of_eq ?_)))
  have hc : Nat.card M ^ S.card = Nat.card M ^ S₀.card * Nat.card M ^ (S.card - S₀.card) := by
    rw [← pow_add, Nat.add_sub_cancel' (Finset.card_le_card hSS)]
  rw [hc, pow_add]
  ring
