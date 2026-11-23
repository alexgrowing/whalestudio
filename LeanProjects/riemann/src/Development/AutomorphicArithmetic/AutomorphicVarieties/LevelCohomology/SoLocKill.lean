import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoContLev
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLocCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoScal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDualEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDecNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private def lkRepZ {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M] (N : ℕ) [Module (ZMod N) M]
    (ρ : Representation O Γ M) : Representation (ZMod N) Γ M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap N
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul, Module.End.mul_apply]

theorem UpperTheory.V.X.So.locKill :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ n : ℤ, n ≠ 0 → n ≠ 1 → ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v → ((l : ℕ) : 𝓞 k) ∉ v.asIdeal → ∃ B : ℕ, ∀ (a : O) (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation O (Dec (F := k) A) M), IsLev a ((ψ * chiO k Ω l O ^ n).comp (Dec (F := k) A).subtype) ρ → Finite (H1 ρ) ∧ Nat.card (H1 ρ) ≤ B := by
  intro hFin hTate hEul k Ω _ _ _ _ _ l _ O _ _ _ _ _ ψ hψ n hn0 hn1 v A hA hl
  obtain ⟨g₁, hg₁D, hg₁⟩ := So.decNe k Ω l O ψ hψ n hn0 v A hA
  have hψ' : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
    have hk : (ψ⁻¹).ker = ψ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hk]
    exact hψ
  obtain ⟨g₂, hg₂D, hg₂⟩ :=
    So.decNe k Ω l O ψ⁻¹ hψ' (1 - n) (sub_ne_zero.mpr (Ne.symm hn1)) v A hA
  set d₁ : O := (((ψ * chiO k Ω l O ^ n) g₁ : Oˣ) : O) - 1 with hd₁
  set d₂ : O := (((ψ⁻¹ * chiO k Ω l O ^ (1 - n)) g₂ : Oˣ) : O) - 1 with hd₂
  have hd₁0 : d₁ ≠ 0 := by
    intro h
    apply hg₁
    apply Units.ext
    simpa [hd₁, sub_eq_zero] using h
  have hd₂0 : d₂ ≠ 0 := by
    intro h
    apply hg₂
    apply Units.ext
    simpa [hd₂, sub_eq_zero] using h
  obtain ⟨hM0fin, ⟨r₀, -, hr₀k⟩, -⟩ :=
    So.levFacts l O d₂ hd₂0 (O ⧸ Ideal.span {d₂}) ⟨LinearEquiv.refl O _⟩
  haveI := hM0fin
  haveI : NeZero (l ^ r₀) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Module (ZMod (l ^ r₀)) (O ⧸ Ideal.span {d₂}) := AddCommGroup.zmodModule hr₀k
  obtain ⟨ι₀, -, hι₀rng, -⟩ :=
    So.dualEmb l O d₂ hd₂0 r₀ (O ⧸ Ideal.span {d₂}) ⟨LinearEquiv.refl O _⟩
  haveI hTfin : Finite (TDual (ZMod (l ^ r₀)) (O ⧸ Ideal.span {d₂})) := by
    unfold TDual Module.Dual
    exact Finite.of_injective
      (fun f : (O ⧸ Ideal.span {d₂}) →ₗ[ZMod (l ^ r₀)] ZMod (l ^ r₀) => (f : (O ⧸ Ideal.span {d₂}) → ZMod (l ^ r₀)))
      (fun f g h => LinearMap.ext (congrFun h))
  refine ⟨Nat.card (O ⧸ Ideal.span {d₁}) *
    Nat.card (TDual (ZMod (l ^ r₀)) (O ⧸ Ideal.span {d₂})), ?_⟩
  intro a M _ _ _ _ ρ hρ
  obtain ⟨hMfin, ⟨r, hr, hrk⟩, hMt⟩ := So.levFacts l O a hρ.ne M hρ.cyc
  haveI := hMfin
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Module (ZMod (l ^ r)) M := AddCommGroup.zmodModule hrk
  set ρZ := lkRepZ (l ^ r) ρ with hρZ
  have hρZapp : ∀ g m, ρZ g m = ρ g m := fun g m => rfl
  let ρG : Representation O (G k Ω) M :=
    (Module.toModuleEnd O (S := O) M).toMonoidHom.comp
      ((Units.coeHom O).comp (ψ * chiO k Ω l O ^ n))
  have hρG : IsLev a (ψ * chiO k Ω l O ^ n) ρG := ⟨hρ.ne, hρ.cyc, fun g m => rfl⟩
  have hcG := So.contLev k Ω l O ψ n hψ a M ρG hρG
  have hcZ : ReciprocityTheory.Gal.ContAction ρZ := by
    have hf : (fun p : Dec (F := k) A × M => ρZ p.1 p.2) =
        (fun p : G k Ω × M => ρG p.1 p.2) ∘ (fun p : Dec (F := k) A × M => ((p.1 : G k Ω), p.2)) := by
      funext p
      rw [hρZapp, hρ.act]
      rfl
    unfold ReciprocityTheory.Gal.ContAction
    rw [hf]
    exact hcG.comp (continuous_subtype_val.prodMap continuous_id)
  let τ : Representation (ZMod (l ^ r)) (Dec (F := k) A) (TDual (ZMod (l ^ r)) M) :=
    { toFun := fun g => ((cycMod k Ω l r (g : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • (ρZ g⁻¹).dualMap
      map_one' := by
        refine LinearMap.ext fun φ => LinearMap.ext fun m => ?_
        show ((cycMod k Ω l r ((1 : Dec (F := k) A) : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
          φ (ρZ 1⁻¹ m) = φ m
        simp
      map_mul' := by
        intro g h
        refine LinearMap.ext fun φ => LinearMap.ext fun m => ?_
        show ((cycMod k Ω l r ((g * h : Dec (F := k) A) : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
            φ (ρZ (g * h)⁻¹ m) =
          ((cycMod k Ω l r (g : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
            (((cycMod k Ω l r (h : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * φ (ρZ h⁻¹ (ρZ g⁻¹ m)))
        rw [mul_inv_rev, map_mul, Module.End.mul_apply, Subgroup.coe_mul, map_mul, Units.val_mul, mul_assoc] }
  have hτ : ∀ (g : Dec (F := k) A) (φ : TDual (ZMod (l ^ r)) M) (m : M),
      τ g φ m = ((cycMod k Ω l r (g : G k Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * φ (ρZ g⁻¹ m) :=
    fun g φ m => rfl
  have hEq := (hEul k Ω l r M A ρZ v hr hA hcZ).2 hl
  obtain ⟨hH1f, -, hH2⟩ := So.locCard hFin hTate k Ω l r hr v A hA M ρZ hcZ τ hτ
  have hB1 : Nat.card (H0 ρZ) ≤ Nat.card (O ⧸ Ideal.span {d₁}) := by
    have hmem : ∀ x : H0 ρZ, d₁ • (x : M) = 0 := by
      intro x
      have hx := (Representation.mem_invariants ρZ (x : M)).mp x.2 ⟨g₁, hg₁D⟩
      rw [hρZapp, hρ.act] at hx
      rw [hd₁, sub_smul, one_smul, sub_eq_zero]
      exact hx
    refine le_trans ?_ (hMt d₁ hd₁0)
    refine Nat.card_le_card_of_injective (fun x => ⟨(x : M), hmem x⟩) ?_
    intro x y h
    exact Subtype.ext (congrArg (fun z : {m : M // d₁ • m = 0} => (z : M)) h)
  have hB2 : Nat.card (H0 τ) ≤ Nat.card (TDual (ZMod (l ^ r₀)) (O ⧸ Ideal.span {d₂})) := by
    obtain ⟨ι, hιinj, -, hιact⟩ := So.dualEmb l O a hρ.ne r M hρ.cyc
    have hu : (algebraMap ℤ_[l] O) ((cycZ k Ω l g₂ : ℤ_[l]ˣ) : ℤ_[l]) *
        (((ψ * chiO k Ω l O ^ n) g₂⁻¹ : Oˣ) : O) =
        (((ψ⁻¹ * chiO k Ω l O ^ (1 - n)) g₂ : Oˣ) : O) := by
      have hc : (algebraMap ℤ_[l] O) ((cycZ k Ω l g₂ : ℤ_[l]ˣ) : ℤ_[l]) =
          ((chiO k Ω l O g₂ : Oˣ) : O) := rfl
      rw [hc, ← Units.val_mul]
      congr 1
      simp only [map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply, zpow_sub,
        zpow_one, mul_inv, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hmem : ∀ φ : H0 τ, ι (φ : TDual (ZMod (l ^ r)) M) ∈ Set.range ι₀ := by
      intro φ
      rw [← hι₀rng]
      have hinv := (Representation.mem_invariants τ (φ : TDual (ZMod (l ^ r)) M)).mp φ.2 ⟨g₂, hg₂D⟩
      have key := hιact ((cycZ k Ω l g₂ : ℤ_[l]ˣ) : ℤ_[l]) (((ψ * chiO k Ω l O ^ n) g₂⁻¹ : Oˣ) : O)
        (φ : TDual (ZMod (l ^ r)) M) (τ ⟨g₂, hg₂D⟩ φ) (fun m => by
          rw [hτ, hρZapp, hρ.act]
          rfl)
      rw [hinv, hu] at key
      rw [hd₂, sub_smul, one_smul, ← key, sub_self]
    refine Nat.card_le_card_of_injective (fun φ => Classical.choose (hmem φ)) ?_
    intro φ₁ φ₂ h
    have h1 := Classical.choose_spec (hmem φ₁)
    have h2 := Classical.choose_spec (hmem φ₂)
    apply Subtype.ext
    apply hιinj
    rw [← h1, ← h2]
    exact congrArg ι₀ h
  obtain ⟨-, ⟨e1⟩, -⟩ := So.scal O (ZMod (l ^ r)) (Dec (F := k) A) M ρ ρZ (fun g m => rfl)
  haveI := hH1f
  refine ⟨Finite.of_equiv _ e1.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e1.toEquiv, hEq, hH2]
  exact Nat.mul_le_mul hB1 hB2
