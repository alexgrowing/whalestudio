import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.CharacterH1GaloisQuotient

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem cast_toZModPow_one (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (x : ℤ_[l]) :
    ZMod.castHom (dvd_pow_self l one_ne_zero) k (PadicInt.toZModPow 1 x) =
      ZMod.castHom (dvd_refl l) k (PadicInt.toZMod x) := by
  have hx : x - (PadicInt.zmodRepr x : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := PadicInt.sub_zmodRepr_mem x
  have h1 : PadicInt.toZMod (x - (PadicInt.zmodRepr x : ℤ_[l])) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod]; exact hx
  have h2 : PadicInt.toZModPow 1 (x - (PadicInt.zmodRepr x : ℤ_[l])) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p]; exact hx
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2]
  simp only [map_natCast]

theorem UpperTheory.V.GC.h1 :
    Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → Finite k → (∀ v, ∃ s, Φ.om k (Φ.loc v s) ≠ 1) → ∀ C₀ : ℕ, clRk l (K ⊓ (cycMod F Ω l 1).ker) ≤ C₀ → Module.rank k (H1C (k := k) (W := k) Φ.loc (chRep (1 : Φ.Γ →* kˣ)) fun _ => ⊤) ≤ 1 + C₀ := by
  intro hP F Ω _ _ _ _ _ l _ k _ _ Φ S K π ι A pl e c hL hk hom C₀ hC
  have hS : ∀ v : S, ∃ u, pl u = v.1 := fun v => (hL.loc.mem v.1).2 (hL.only v.1 v.2)
  choose u hu using hS
  have hA : ∀ v : S, IsPlaceOver (A (u v)) v.1 := fun v => hu v ▸ hL.loc.isOver (u v)
  have hc : ∀ w : InfinitePlace F, IsCCAt w (c (e.symm w)) := fun w => by
    simpa using hL.cc (e.symm w)
  have h := character_H1_galois_quotient hP F Ω l hL.real S K Φ.Γ π hL.g k 1 (fun _ _ => rfl) (fun w => c (e.symm w)) hc
    (fun v => A (u v)) hA C₀ hC Φ.V Φ.Gv Φ.loc
  have hcyc : ∀ g, Φ.om k (π g) = cycF F Ω l k g := fun g => by
    apply Units.ext
    have := cast_toZModPow_one l k (cycZ F Ω l g : ℤ_[l])
    simp only [Frame.om, cycF, cycMod, MonoidHom.comp_apply, hL.eps, Units.coe_map]
    exact this.symm
  have hE : IsEmpty {v : S // ∀ g ∈ Dec (F := F) (A (u v)), (1 : Φ.Γ →* kˣ) (π g) = cycF F Ω l k g} := by
    refine ⟨fun ⟨v, hv⟩ => ?_⟩
    obtain ⟨s, hs⟩ := hom (u v)
    apply hs
    rw [hL.loc_eq, hcyc, ← hv _ (by rw [← hL.loc.range]; exact ⟨s, rfl⟩)]
    rfl
  have e1 : Nat.card {w : InfinitePlace F // (1 : Φ.Γ →* kˣ) (π (c (e.symm w))) = 1} = finrank ℚ F := by
    haveI := hL.real
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => MonoidHom.one_apply _), Nat.card_eq_fintype_card,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, IsTotallyReal.finrank, add_zero]
  have e2 : Nat.card {_u : Unit // (1 : Φ.Γ →* kˣ) = 1} = 1 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)]; simp
  rw [e1, e2, Nat.card_of_isEmpty, add_zero] at h
  push_cast at h
  exact (Cardinal.add_nat_le_add_nat_iff _).1 h
