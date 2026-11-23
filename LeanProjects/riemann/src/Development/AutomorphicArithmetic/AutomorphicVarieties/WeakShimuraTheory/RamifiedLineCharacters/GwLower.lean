import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CcOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.gwLower :
    GlobalFiniteness → GreenbergWiles → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContainsAbove S l → ContAction ρ →
      ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ L : LocCond ρ (locFam S Av),
        ∏ v : S, Nat.card (L v) ≤ Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) * (Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ Module.finrank ℚ F) *
          ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) := by
  classical
  intro hGF hGW F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl S ρ hS hρ Av hA L
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := F) (Ω := Ω) (l := l) (r := 1) (S := S) hS
  obtain ⟨c, hc⟩ := UpperTheory.V.Ws.Gys.ccEx F Ω
  have e := hGW F Ω l 1 M S ρ one_pos hl hS hρ μ hμ Av hA c hc L
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI hfd : Finite (TDual (ZMod (l ^ 1)) M) := DFunLike.finite _
  haveI hf1 : Finite (H1 ρ) := (hGF F Ω l 1 M S ρ one_pos hS hρ).2.1
  have hM : 0 < Nat.card M := Nat.card_pos
  have p1 : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have p2 : 0 < Nat.card (H0 (twDual μ ρ)) := Nat.card_pos
  have p3 : 0 < ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have p4 : 0 < archH0Card S ρ c := by
    unfold archH0Card
    refine Nat.mul_pos (Finset.prod_pos fun w _ => ?_) (pow_pos hM _)
    haveI : Nonempty {m : M // ρ (toGS Ω _ (c w)) m = m} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  have b2 : Nat.card (H0 (twDual μ ρ)) ≤ Nat.card (TDual (ZMod (l ^ 1)) M) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have b4 : archH0Card S ρ c ≤ Nat.card M ^ Module.finrank ℚ F := by
    unfold archH0Card
    have h1 : (∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
        Nat.card {m : M // ρ (toGS Ω _ (c w)) m = m}) ≤ Nat.card M ^ InfinitePlace.nrRealPlaces F := by
      have h2 := Finset.prod_le_pow_card (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal))
        (fun w => Nat.card {m : M // ρ (toGS Ω _ (c w)) m = m}) (Nat.card M)
        (fun w _ => Nat.card_le_card_of_injective _ Subtype.val_injective)
      have h3 : (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal)).card = InfinitePlace.nrRealPlaces F := by
        rw [InfinitePlace.nrRealPlaces, Fintype.card_subtype]
      rwa [h3] at h2
    refine (Nat.mul_le_mul_right _ h1).trans ?_
    rw [← pow_add]
    refine Nat.pow_le_pow_right hM ?_
    have := InfinitePlace.card_add_two_mul_card_eq_rank F
    omega
  have hpos := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p1 p2) p3) p4
  refine (Nat.le_of_dvd hpos (Dvd.intro_left _ e.symm)).trans ?_
  calc _ = Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) * (Nat.card (H0 (twDual μ ρ)) * archH0Card S ρ c) *
          ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul b2 b4))
