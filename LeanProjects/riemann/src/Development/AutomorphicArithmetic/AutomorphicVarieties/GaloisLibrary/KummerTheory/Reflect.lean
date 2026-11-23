import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ReflMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ReflTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ReflRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.UnitMinus
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadXDual

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem reflect_card {A B S T : Type} [AddCommGroup A] [AddCommGroup B] [Finite S] [Finite T] (f : A →+ B)
    (i : f.ker → S) (hi : Function.Injective i) (j : f.range → T) (hj : Function.Injective j) :
    Nat.card A ≤ Nat.card S * Nat.card T := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, mul_comm]
  exact Nat.mul_le_mul (Nat.card_le_card_of_injective i hi) (Nat.card_le_card_of_injective j hj)

private theorem reflect_conj {K : Type} [Field K] [NumberField K] [IsCMField K] {n : ℕ} (hn : n ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : cE K ζ = ζ⁻¹ := by
  obtain ⟨j⟩ : Nonempty (K →+* ℂ) := inferInstance
  apply j.injective
  have h1 : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) hn
  have h2 : j (cE K ζ) = starRingEnd ℂ (j ζ) := IsCMField.complexEmbedding_complexConj K j ζ
  rw [h2, map_inv₀]
  apply eq_inv_of_mul_eq_one_left
  rw [Complex.conj_mul', h1]
  simp

private theorem reflect_tors {K : Type} [Field K] [NumberField K] [IsCMField K] {n : ℕ} (hn : Odd n) (a : Kˣ)
    (ha : a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n) (h1 : radCl n a = 1)
    (hc : a * Units.map (cE K).toMonoidHom a ∈ powK K n) :
    ∃ t b : Kˣ, IsOfFinOrder t ∧ a = t * b ^ n := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  have h2 := (UpperTheory.V.Kum.radClKer K ∅ n hn0 a ha).1 (h1 ▸ one_mem _)
  obtain ⟨u, hu, p, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 h2
  have hb : powMonoidHom n b * Units.map (cE K).toMonoidHom (powMonoidHom n b) ∈ powK K n :=
    ⟨b * Units.map (cE K).toMonoidHom b, by simp only [powMonoidHom_apply, mul_pow, map_pow]⟩
  have hu' : u * Units.map (cE K).toMonoidHom u ∈ powK K n := by
    rw [map_mul, mul_mul_mul_comm] at hc
    exact (Subgroup.mul_mem_cancel_right _ hb).1 hc
  obtain ⟨t, ht, q, ⟨d, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 ((UpperTheory.V.Kum.unitMinus K n u hu hu').2 hn)
  exact ⟨t, d * b, ht, by simp only [powMonoidHom_apply, mul_pow, mul_assoc]⟩

theorem UpperTheory.V.Kum.reflect :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K) [Normal F K] [IsCMField K] (χ ψ : G F Ω →* (ZMod n)ˣ) (σ : Ω ≃+* Ω), U = galOf F K Ω → Odd n → IsPrimitiveRoot ζ n → (∀ g : G F Ω, g (algebraMap K Ω ζ) = (algebraMap K Ω ζ) ^ (χ g : ZMod n).val) → IsConjOm σ →
    Nat.card (EqEig N U (scalRep (ZMod n) ψ) σ 1) ≤ Nat.card (scalRep (ZMod n) ψ).invariants * Nat.card (ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) : Subgroup (ClassGroup (𝓞 K))) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ _ _ χ ψ σ hU hn hζ hχ hσ
  have hn0 : n ≠ 0 := NeZero.ne n
  obtain ⟨κ, hκ, -⟩ := UpperTheory.V.Kum.reflMap F Ω K U n N ζ hU hζ
  obtain ⟨hR, hfin⟩ := UpperTheory.V.Kum.reflRoot F Ω K U n N ζ ψ hU hζ
  have hX := (UpperTheory.V.Kum.radXDual F Ω K U n N ζ hU hζ).1
  have hle : EqEig N U (scalRep (ZMod n) ψ) σ 1 ≤ XDual N U (ZMod n) (ZMod n) := fun φ h => h.1.1
  let f : EqEig N U (scalRep (ZMod n) ψ) σ 1 →+ Additive (ClassGroup (𝓞 K)) :=
    κ.comp (Submodule.inclusion hle).toAddMonoidHom
  have key : ∀ φ : EqEig N U (scalRep (ZMod n) ψ) σ 1, ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1 β ∧
      β ^ n = algebraMap K Ω a ∧ a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n ∧ f φ = Additive.ofMul (radCl n a) ∧
      a * Units.map (cE K).toMonoidHom a ∈ powK K n ∧ radCl n a ∈ ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) := by
    intro φ
    obtain ⟨β, a, h1, h2, h3⟩ := hX φ.1 (hle φ.2)
    obtain ⟨h4, h5⟩ := UpperTheory.V.Kum.reflTw F Ω K U n N ζ χ ψ φ.1 β a hU hζ hχ φ.2.1 h1 h2
    obtain ⟨h6, h7⟩ := h5 (cE K) σ hσ.isLift (reflect_conj hn0 hζ) φ.2.2
    exact ⟨β, a, h1, h2, h3, hκ ⟨φ.1, hle φ.2⟩ β a h1 h2, h6, h4, h7⟩
  have hker : ∀ φ : f.ker, ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1.1 β ∧ β ^ n = algebraMap K Ω a ∧
      IsOfFinOrder β := by
    intro φ
    obtain ⟨β, a, h1, h2, h3, h4, h5, -⟩ := key φ.1
    have h0 : radCl n a = 1 := Additive.ofMul.injective (h4.symm.trans φ.2)
    obtain ⟨t, b, ht, rfl⟩ := reflect_tors hn a h3 h0 h5
    have hb : algebraMap K Ω b ≠ 0 := (map_ne_zero _).2 b.ne_zero
    have hp : (β / algebraMap K Ω b) ^ n = algebraMap K Ω t := by
      rw [div_pow, h2, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, mul_div_cancel_right₀ _ (pow_ne_zero _ hb)]
    refine ⟨β / algebraMap K Ω b, t, ⟨div_ne_zero h1.1 hb, fun u => ?_⟩, hp, ?_⟩
    · have hu : u.1 ∈ galOf F K Ω := hU ▸ u.2
      rw [map_div₀, h1.2 u, hu (b : K), mul_div_assoc]
    · refine IsOfFinOrder.of_pow ?_ hn0
      rw [hp]
      exact ((algebraMap K Ω).toMonoidHom.comp (Units.coeHom K)).isOfFinOrder ht
  have hran : ∀ c : f.range, Additive.toMul c.1 ∈ ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) := by
    rintro ⟨c, φ, rfl⟩
    obtain ⟨β, a, -, -, -, h4, -, h6⟩ := key φ
    show Additive.toMul (f φ) ∈ _
    rw [h4]
    exact h6
  refine le_trans (reflect_card f (fun φ => (⟨φ.1.1, φ.1.2.1, hker φ⟩ : {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β})) ?_
    (fun c => (⟨Additive.toMul c.1, hran c⟩ : (ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) : Subgroup (ClassGroup (𝓞 K))))) ?_)
    (Nat.mul_le_mul_right _ hR)
  · intro x y h
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  · intro x y h
    exact Subtype.ext (Additive.toMul.injective (Subtype.mk.inj h))
