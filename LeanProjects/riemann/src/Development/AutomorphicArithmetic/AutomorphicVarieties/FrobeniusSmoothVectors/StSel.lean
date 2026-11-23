import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.DualNontriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StDesc

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem toGS_eq_one_of_mem_inertia_of_notMem (Ω : Type) [Field Ω] [CharZero Ω] (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ S) (A : ValuationSubring Ω) (hA : IsPlaceOver A v)
    (s : G ℚ Ω) (hs : s ∈ Ine (F := ℚ) A) : toGS Ω S s = 1 := by
  unfold toGS
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  unfold ReciprocityTheory.Gal.NS
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff]
  exact ⟨v, hv, A, hA, hs⟩

private theorem continuous_toGS' (Ω : Type) [Field Ω] [CharZero Ω] (S : Set (HeightOneSpectrum (𝓞 ℚ))) :
    Continuous (toGS Ω S) := by
  unfold toGS
  exact continuous_quot_mk

private theorem toGS_surjective' (Ω : Type) [Field Ω] [CharZero Ω] (S : Set (HeightOneSpectrum (𝓞 ℚ))) :
    Function.Surjective (toGS Ω S) := by
  unfold toGS
  exact QuotientGroup.mk'_surjective _

set_option maxHeartbeats 200000 in
theorem UpperTheory.V.Fr.st_sel :
    GC.Hypotheses₂ → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (κ : G ℚ Ω →* kˣ), IsOpen (κ.ker : Set (G ℚ Ω)) → (∃ σ : G ℚ Ω, IsCC σ ∧ κ σ ≠ 1) → (∃ s, κ s ≠ GC.cycF ℚ Ω l k s) → ∀ S : Finset (HeightOneSpectrum (𝓞 ℚ)), ContainsAbove S l → (∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := ℚ) A ≤ κ.ker) → ∀ v₀ ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ v₀.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A v₀ → Dec (F := ℚ) A ≤ κ.ker ⊓ (GC.cycF ℚ Ω l k).ker) → (∀ v ∈ S, v ≠ v₀ → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∃ s ∈ Dec (F := ℚ) A, κ s ≠ 1) → ∃ y : G ℚ Ω → k, IsLocallyConstant y ∧ (∀ s t, y (s * t) = y s + κ s * y t) ∧ (¬ ∃ b, ∀ s, y s = κ s * b - b) ∧ (∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ s ∈ Ine (F := ℚ) A, y s = 0) ∧ ∀ v ∈ S, v ≠ v₀ → ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ ∃ b, ∀ s ∈ Dec (F := ℚ) A, y s = κ s * b - b := by
  intro hP Ω _ _ _ l _ hl2 k _ _ _ κ hκo hCC hs0ex S hSA hIne v₀ hv₀ hlv₀ hD0 hDo
  obtain ⟨σ, hσ, hσκ⟩ := hCC
  obtain ⟨s0, hs0⟩ := hs0ex
  have hdvd : l ∣ l ^ 1 := by simp
  haveI : Fact (l ^ 1).Prime := ⟨by simpa using (Fact.out : l.Prime)⟩
  letI alg : Algebra (ZMod (l ^ 1)) k := (ZMod.castHom hdvd k).toAlgebra
  letI : TopologicalSpace k := ⊥
  haveI : DiscreteTopology k := ⟨rfl⟩
  obtain ⟨κS, hκS, hκSlc⟩ := st_desc Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) kˣ κ hκo
    (fun v hv A hA => hIne v hv A hA)
  have hκS' : ∀ g, κS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g) = κ g := fun g => by
    rw [← MonoidHom.comp_apply, hκS]
  let ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) k :=
    (Algebra.lmul (ZMod (l ^ 1)) k).toRingHom.toMonoidHom.comp ((Units.coeHom k).comp κS)
  have hρ : ∀ g m, ρ g m = (κS g : k) * m := fun g m => rfl
  have hcont : ReciprocityTheory.Gal.ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    have hc : Continuous fun g => (κS g : k) :=
      (hκSlc.comp (fun u : kˣ => (u : k))).continuous
    exact (hc.comp continuous_fst).mul continuous_snd
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := 1) hSA
  let Av : S → ValuationSubring Ω := fun v => (exists_isPlaceOver Ω v.1).choose
  have hAv : ∀ v : S, IsPlaceOver (Av v) v.1 := fun v => (exists_isPlaceOver Ω v.1).choose_spec
  have kill : ∀ (a : kˣ) (m : k), a ≠ 1 → (a : k) * m = m → m = 0 := by
    intro a m ha hm
    have h2 : ((a : k) - 1) * m = 0 := by rw [sub_mul, one_mul, hm, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (fun h => ha (Units.val_eq_one.mp h)))
  have hfix : ∀ m : k, ρ (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) σ) m = m → m = 0 := by
    intro m hm
    rw [hρ, hκS'] at hm
    exact kill _ m hσκ hm
  have hdual : H0 (twDual μ ρ) = ⊥ := by
    refine st_dual l k _ μ ρ (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) s0) (κ s0 : k) (fun m => by rw [hρ, hκS']) ?_
    intro h
    apply hs0
    apply Units.ext
    have hμs : μ (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) s0) = cycMod ℚ Ω l 1 s0 := by
      rw [← MonoidHom.comp_apply, hμ]
    rw [h, hμs]
    rfl
  have hother : ∀ v : S, v ≠ ⟨v₀, hv₀⟩ → H0 (MonoidHom.comp ρ (locFam S Av v)) = ⊥ := by
    intro v hv
    ext m
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, Submodule.mem_bot]
    constructor
    · intro hm
      obtain ⟨s, hs, hκs⟩ := hDo v.1 v.2 (fun h => hv (Subtype.ext h)) (Av v) (hAv v)
      have h1 := hm ⟨s, hs⟩
      change (κS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) s) : k) * m = m at h1
      rw [hκS'] at h1
      exact kill _ m hκs h1
    · rintro rfl g
      exact map_zero _
  have hloc : Nat.card (H0 (MonoidHom.comp ρ (locFam S Av ⟨v₀, hv₀⟩))) <
      Nat.card (H1 (MonoidHom.comp ρ (locFam S Av ⟨v₀, hv₀⟩))) := by
    refine st_loc hP.1.lf hP.1.lt hP.1.le Ω l k (Av ⟨v₀, hv₀⟩) v₀ (hAv ⟨v₀, hv₀⟩) hlv₀ ?_ _ ?_
    · intro g hg
      have h1 : GC.cycF ℚ Ω l k g = 1 := (hD0 (Av ⟨v₀, hv₀⟩) (hAv ⟨v₀, hv₀⟩) hg).2
      apply Units.ext
      apply (ZMod.castHom hdvd k).injective
      have h2 := congrArg Units.val h1
      rw [Units.val_one, map_one]
      exact h2
    · intro g m
      change (κS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g.1) : k) * m = m
      have h1 : κ g.1 = 1 := (hD0 (Av ⟨v₀, hv₀⟩) (hAv ⟨v₀, hv₀⟩) g.2).1
      rw [hκS', h1, Units.val_one, one_mul]
  obtain ⟨z, hz, hzB, hzloc⟩ := st_count hP.1.gf hP.gw Ω l hl2 k S ρ hSA hcont μ hμ Av hAv σ hσ hfix
    hdual ⟨v₀, hv₀⟩ hother hloc
  rw [mem_Z1_iff_cocycle] at hz
  obtain ⟨hzc, hzco⟩ := hz
  have hz1 : z 1 = 0 := by
    have h1 := hzco 1 1
    rw [mul_one, hρ, map_one, Units.val_one, one_mul] at h1
    linear_combination (-1 : k) * h1
  refine ⟨fun s => z (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) s), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((IsLocallyConstant.iff_continuous z).2 hzc).comp_continuous (continuous_toGS' Ω _)
  · intro s t
    simp only [map_mul]
    rw [hzco, hρ, hκS']
  · rintro ⟨b, hb⟩
    apply hzB
    rw [mem_coboundaries1]
    refine ⟨b, fun g => ?_⟩
    obtain ⟨s, rfl⟩ := toGS_surjective' Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g
    have hbs := hb s
    beta_reduce at hbs
    rw [hbs, hρ, hκS']
  · intro v hv A hA s hs
    simp only
    rw [toGS_eq_one_of_mem_inertia_of_notMem Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) v hv A hA s hs, hz1]
  · intro v hv hne
    obtain ⟨m, hm⟩ := hzloc ⟨v, hv⟩ (fun h => hne (congrArg Subtype.val h))
    exact ⟨Av ⟨v, hv⟩, hAv _, m, fun s hs => by
      beta_reduce
      rw [hm s hs, hρ, hκS']⟩
