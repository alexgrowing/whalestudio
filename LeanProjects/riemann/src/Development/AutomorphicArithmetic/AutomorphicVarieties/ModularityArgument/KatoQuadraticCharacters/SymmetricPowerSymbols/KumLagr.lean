import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem kum_lagr {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (c : (L ≃ₐ[K] L) → K) (h0 : ∀ g, c g ≠ 0) (hm : ∀ g h, c (g * h) = c g * c h)
    (B : Finset L) (hB : ∀ g h : L ≃ₐ[K] L, (∀ b ∈ B, g b = h b) → c g = c h) :
    ∃ θ : L, θ ≠ 0 ∧ ∀ g : L ≃ₐ[K] L, g θ = algebraMap K L (c g) * θ := by
  classical
  let F : IntermediateField K L := (FiniteGaloisIntermediateField.adjoin K (B : Set L)).toIntermediateField
  haveI : FiniteDimensional K F := (FiniteGaloisIntermediateField.adjoin K (B : Set L)).finiteDimensional
  haveI : IsGalois K F := (FiniteGaloisIntermediateField.adjoin K (B : Set L)).isGalois
  have hBF : ∀ b ∈ B, b ∈ F := fun b hb =>
    FiniteGaloisIntermediateField.subset_adjoin K (B : Set L) hb
  have hagree : ∀ (g : L ≃ₐ[K] L) (σ : F ≃ₐ[K] F), (∀ x : F, g (x : L) = (σ x : L)) →
      c g = c (σ.liftNormal L) := by
    intro g σ hgσ
    apply hB
    intro b hb
    have h1 := hgσ ⟨b, hBF b hb⟩
    have h2 := σ.liftNormal_commutes L ⟨b, hBF b hb⟩
    simp only [IntermediateField.algebraMap_apply] at h2
    rw [h1, h2]
  let cE : (F ≃ₐ[K] F) → K := fun σ => c (σ.liftNormal L)
  have hlift : ∀ (σ : F ≃ₐ[K] F) (x : F), σ.liftNormal L (x : L) = (σ x : L) := by
    intro σ x
    have := σ.liftNormal_commutes L x
    simpa only [IntermediateField.algebraMap_apply] using this
  have hcEmul : ∀ σ τ, cE (σ * τ) = cE σ * cE τ := by
    intro σ τ
    have : c ((σ * τ).liftNormal L) = c (σ.liftNormal L * τ.liftNormal L) := by
      symm
      apply hagree
      intro x
      simp only [AlgEquiv.mul_apply, hlift]
    simp only [cE, this, hm]
  have hcE0 : ∀ σ, algebraMap K F (cE σ) ≠ 0 := fun σ => by
    simpa using h0 (σ.liftNormal L)
  let f : (F ≃ₐ[K] F) → Fˣ := fun σ => Units.mk0 _ (hcE0 σ)
  have hcoc : groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    ext
    simp [f, hcEmul, mul_comm]
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hcoc
  refine ⟨((β : F) : L), by simp, fun g => ?_⟩
  set σ := g.restrictNormal F
  have hgσ : ∀ x : F, g (x : L) = (σ x : L) := by
    intro x
    have := g.restrictNormal_commutes F x
    simpa only [IntermediateField.algebraMap_apply] using this.symm
  have hσβ : (σ (β : F)) = algebraMap K F (cE σ) * (β : F) := by
    have := congrArg (fun u : Fˣ => (u : F)) (hβ σ)
    simp [f, div_eq_iff (β.ne_zero)] at this
    simpa using this
  rw [hgσ, hσβ, hagree g σ hgσ]
  simp [cE]

theorem UpperTheory.V.Z.Kato.Sym.kum :
    UpperTheory.V.Z.Kato.Sym.Kum := by
  intro Ω _ _ _ ε X m hm
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
  haveI : IsGalois X.K (Kb X) := IsGalois.mk
  obtain ⟨hprim, hL2, hL3, -, -, -, -⟩ := lgB Ω ε X m hm
  set ζK : X.K := algebraMap Ω X.K (eOm ε (1 / (m : ℚ))) with hζK
  have hzt : zt X m = io X ζK := rfl
  have hinj : Function.Injective (io X) := (io X).injective
  have hζm : ζK ^ m = 1 := by
    apply hinj
    rw [map_pow, ← hzt, hprim.pow_eq_one, map_one]
  have hζ0 : ζK ≠ 0 := by
    intro h
    rw [h, zero_pow hm.ne'] at hζm
    exact zero_ne_one hζm
  have hpowmod : ∀ n, ζK ^ (n % m) = ζK ^ n := fun n => by
    conv_rhs => rw [← Nat.mod_add_div n m, pow_add, pow_mul, hζm, one_pow, mul_one]
  have hInDalg : ∀ g : Kb X ≃ₐ[X.K] Kb X, InD X g.toRingEquiv := fun g x => g.commutes x
  let toAlg : ∀ h : RingAut (Kb X), InD X h → (Kb X ≃ₐ[X.K] Kb X) :=
    fun h hh => AlgEquiv.ofRingEquiv (f := h) hh
  have htoAlg : ∀ h hh, (toAlg h hh).toRingEquiv = h := fun h hh => rfl
  have hfixed : ∀ x : Kb X, (∀ h : RingAut (Kb X), InD X h → h x = x) → ∃ a : X.K, io X a = x := by
    intro x hx
    have hbot : x ∈ (⊥ : IntermediateField X.K (Kb X)) :=
      (InfiniteGalois.mem_bot_iff_fixed x).mpr fun g => hx g.toRingEquiv (hInDalg g)
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hbot
    exact ⟨a, ha⟩
  have hne : ∀ (θ : Kb X) (f : X.Kˣ), θ ^ m = io X (f : X.K) → θ ≠ 0 := by
    intro θ f hθ h0
    rw [h0, zero_pow hm.ne'] at hθ
    exact f.ne_zero (hinj (by rw [← hθ, map_zero]))
  have hact : ∀ (θ : Kb X) (f : X.Kˣ), θ ^ m = io X (f : X.K) → ∀ h : RingAut (Kb X), InD X h →
      h θ = zt X m ^ (ka X m θ h).val * θ := by
    intro θ f hθ h hh
    apply hL2 _ _ (hne θ f hθ)
    rw [← map_pow, hθ, hh]
  refine ⟨fun φ hadd hLC => ?_, fun φ φ' f f' hK hφ => ?_⟩
  · obtain ⟨B, hB⟩ := hLC
    let c : (Kb X ≃ₐ[X.K] Kb X) → X.K := fun g => ζK ^ (φ g.toRingEquiv).val
    have hc0 : ∀ g, c g ≠ 0 := fun g => pow_ne_zero _ hζ0
    have hcm : ∀ g h, c (g * h) = c g * c h := by
      intro g h
      have e : (g * h).toRingEquiv = g.toRingEquiv * h.toRingEquiv := RingEquiv.ext fun _ => rfl
      simp only [c, e, hadd _ _ (hInDalg g) (hInDalg h), ZMod.val_add, hpowmod, pow_add]
    have hcB : ∀ g h : Kb X ≃ₐ[X.K] Kb X, (∀ b ∈ B, g b = h b) → c g = c h := by
      intro g h hgh
      simp only [c, hB _ _ (hInDalg g) (hInDalg h) hgh]
    obtain ⟨θ, hθ0, hθ⟩ := kum_lagr c hc0 hcm B hcB
    obtain ⟨a, ha⟩ := hfixed (θ ^ m) (by
      intro h hh
      rw [map_pow, show h θ = (toAlg h hh) θ from rfl, hθ, mul_pow, ← map_pow, ← pow_mul,
        mul_comm _ m, pow_mul, hζm, one_pow, map_one, one_mul])
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at ha
      exact pow_ne_zero m hθ0 ha.symm
    refine ⟨Units.mk0 a ha0, θ, by simp [ha], fun h hh => ?_⟩
    apply hL3 _ _ _ hθ0
    rw [show h θ = (toAlg h hh) θ from rfl, hθ]
    show io X (ζK ^ (φ (toAlg h hh).toRingEquiv).val) * θ = zt X m ^ (φ h).val * θ
    rw [htoAlg, hzt, map_pow]
  · obtain ⟨θ, hθm, hθ⟩ := hK
    have hθ0 := hne θ f hθm
    have hθact : ∀ h, InD X h → h θ = zt X m ^ (φ h).val * θ := fun h hh => by
      rw [hact θ f hθm h hh, hθ h hh]
    constructor
    · rintro ⟨θ', hθ'm, hθ'⟩
      have hθ'0 := hne θ' f' hθ'm
      obtain ⟨u, hu⟩ := hfixed (θ' / θ) (by
        intro h hh
        rw [map_div₀, hθact h hh, hact θ' f' hθ'm h hh, hθ' h hh, ← hφ h hh]
        field_simp [hθ0, hθ'0, pow_ne_zero _ (hprim.ne_zero hm.ne')])
      have hu0 : u ≠ 0 := by
        intro h0
        rw [h0, map_zero, eq_comm, div_eq_zero_iff] at hu
        exact hu.elim hθ'0 hθ0
      refine ⟨Units.mk0 u hu0, Units.ext (hinj ?_)⟩
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, hu,
        ← hθ'm, ← hθm]
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero m hθ0)]
    · rintro ⟨v, hv⟩
      refine ⟨θ * io X (v : X.K), ?_, fun h hh => ?_⟩
      · rw [mul_pow, hθm, ← map_pow, ← map_mul, hv, Units.val_mul, Units.val_pow_eq_pow_val]
      · apply hL3 _ _ _ (mul_ne_zero hθ0 ((map_ne_zero _).mpr v.ne_zero))
        rw [map_mul, hh, hθact h hh, hφ h hh, mul_assoc]
