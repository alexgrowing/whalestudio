import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Strict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical
open scoped Pointwise

theorem UpperTheory.V.Ws.tate_shafarevich_card_mod_l :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (Av : S → ValuationSubring Ω) (K : Subgroup (G F Ω)) (r : ℕ), (∀ v, IsPlaceOver (Av v) v.1) → K.Normal → ¬ l ∣ K.index → (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) → XRk l 1 K r → CardLe (Sha1 ρ (locFam S Av) (continuous_locFam S Av)) (Nat.card M ^ (r + 1)) := by
  intro F Ω _ _ _ _ _ l hl M _ _ _ _ _ S ρ Av K r hA hN hK hρ hX
  have hM : ∀ m : M, l • m = 0 := by
    intro m
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ 1)) l m]
    have h0 : ((l : ℕ) : ZMod (l ^ 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 (by rw [pow_one])
    rw [h0, zero_smul]
  have hB := UpperTheory.V.Ws.card_cocycles_vanishing_on_inertia_le_pow F Ω l (ZMod (l ^ 1)) M hM (ρ.comp (toGS Ω _)) K r hK hρ hX
  obtain ⟨p1, p2, -, -⟩ := UpperTheory.V.Kum.placeDict F Ω
  have hmem : ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) ∈ Sha1 ρ (locFam S Av) (continuous_locFam S Av) →
      (fun g => z.1 (toGS Ω _ g)) ∈ cocOff (ρ.comp (toGS Ω _)) (ineOff F Ω 1 ∩ K) := by
    intro z hz
    have hz1 : z.1 1 = 0 := by
      have := z.2.2 1 1
      rw [one_mul, map_one, Module.End.one_apply] at this
      exact left_eq_add.1 this
    have hc : ∀ a b : G F Ω, z.1 (toGS Ω _ (a * b)) = z.1 (toGS Ω _ a) + ρ (toGS Ω _ a) (z.1 (toGS Ω _ b)) :=
      fun a b => by rw [map_mul, z.2.2]
    refine ⟨(IsLocallyConstant.iff_continuous _).2 (z.2.1.comp (continuous_toGS Ω _)), hc, ?_⟩
    rintro u ⟨⟨A, -, hu⟩, huK⟩
    show z.1 (toGS Ω _ u) = 0
    by_cases hT : A = ⊤
    · subst hT
      rw [p1, Subgroup.mem_bot] at hu
      rw [hu, map_one, hz1]
    obtain ⟨v, hv⟩ := p2 A hT
    by_cases hvS : v ∈ S
    · obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA ⟨v, hvS⟩) hv
      have hd : g⁻¹ * u * g ∈ Dec (F := F) (Av ⟨v, hvS⟩) := by
        have h : u • g • Av ⟨v, hvS⟩ = g • Av ⟨v, hvS⟩ := Ine_le_Dec _ hu
        show (g⁻¹ * u * g) • Av ⟨v, hvS⟩ = Av ⟨v, hvS⟩
        rw [mul_smul, mul_smul, h, inv_smul_smul]
      have hk : g⁻¹ * u * g ∈ K := by simpa using hN.conj_mem u huK g⁻¹
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 ((Submodule.mem_iInf _).1 hz ⟨v, hvS⟩))
      have h0 : z.1 (toGS Ω _ (g⁻¹ * u * g)) = 0 := (hm ⟨_, hd⟩).trans (sub_eq_zero.2 (hρ _ hk m))
      have h1 := hc g (g⁻¹ * u * g)
      rw [h0, map_zero, add_zero, mul_assoc, mul_inv_cancel_left, hc, hρ u huK] at h1
      exact add_eq_right.1 h1
    · have hn : u ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) := by
        apply Subgroup.le_topologicalClosure
        apply Subgroup.subset_normalClosure
        simp only [Set.mem_iUnion]
        exact ⟨v, hvS, A, hv, hu⟩
      have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) u = 1 := (QuotientGroup.eq_one_iff _).2 hn
      rw [this, hz1]
  choose s hs using Submodule.Quotient.mk_surjective ((B1 ρ).comap (Z1 ρ).subtype)
  refine hB.of_injective (fun x => ⟨_, hmem (s x.1) ((hs x.1).symm ▸ x.2)⟩) fun x y h => ?_
  apply Subtype.ext
  rw [← hs x.1, ← hs y.1]
  congr 1
  apply Subtype.ext
  funext a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  exact congrFun (congrArg Subtype.val h) g
