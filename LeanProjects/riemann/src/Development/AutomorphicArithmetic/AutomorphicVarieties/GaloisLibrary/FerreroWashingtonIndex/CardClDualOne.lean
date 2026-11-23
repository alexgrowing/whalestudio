import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardTors
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HomLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.desc :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L], IsTotallyComplex L → (powR (Cl K) l).index ≤ Module.finrank K L * (powR (Cl L) l).index := by
  intro l _ K _ _ L _ _ _ hL
  classical
  let Ω := AlgebraicClosure L
  haveI : IsAlgClosure K Ω := IsAlgClosure.ofAlgebraic K L Ω
  obtain ⟨-, -, hidx⟩ := galEmbTop K L Ω
  haveI : (galOf K L Ω).FiniteIndex := ⟨by rw [hidx]; exact Module.finrank_pos.ne'⟩
  have hK := (cardTors (ClassGroup (𝓞 K))).2 l
  have hL' := (cardTors (ClassGroup (𝓞 L))).2 l
  change _ ≤ _ * (powR (ClassGroup (𝓞 L)) l).index
  change (powR (ClassGroup (𝓞 K)) l).index ≤ _
  rw [← hK, ← hL', ← hidx]
  let Ψ : (ClassGroup (𝓞 K) →* Multiplicative (ZMod l)) →* (galOf K L Ω → Multiplicative (ZMod l)) :=
    { toFun := fun φ u => φ (artCl K Ω (u : G K Ω))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hpull := pullOnto K Ω L (galOf K L Ω) le_rfl 1 (ZMod l) (ZMod l) one_ne_zero le_rfl (Or.inl hL)
  have hmem : ∀ φ : ClassGroup (𝓞 K) →* Multiplicative (ZMod l),
      (fun u => Multiplicative.toAdd (Ψ φ u)) ∈ XDual 1 (galOf K L Ω) (ZMod l) (ZMod l) := by
    intro φ
    simp only [XDual]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ((artSurj K Ω).2.comp_continuous continuous_subtype_val).comp _
    · intro a b
      simp [Ψ, map_mul]
    · intro A a hi
      simp [Ψ, (artIne K Ω).1 A _ hi]
    · intro A hA
      simp at hA
  have hsurj := (artSurj K Ω).1
  obtain ⟨hfin, hle⟩ := homLe l (G K Ω) (galOf K L Ω)
  have hker : Nat.card Ψ.ker ≤ (galOf K L Ω).index := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun φ : Ψ.ker => (⟨fun g => Multiplicative.toAdd ((φ : ClassGroup (𝓞 K) →* Multiplicative (ZMod l)) (artCl K Ω g)), ?_, ?_⟩ :
        { φ : G K Ω → ZMod l // (∀ (a b : G K Ω), φ (a * b) = φ a + φ b) ∧ ∀ u ∈ galOf K L Ω, φ u = 0 })) ?_) hle
    · intro a b
      simp [map_mul]
    · intro u hu
      have h1 := congrFun φ.2 ⟨u, hu⟩
      simpa [Ψ] using h1
    · intro φ ψ h
      apply Subtype.ext
      ext c
      obtain ⟨g, rfl⟩ := hsurj c
      have := congrFun (congrArg Subtype.val h) g
      simpa using this
  have hch : ∀ x : Ψ.range, ∃ θ ∈ ClDual L 1 (ZMod l) (ZMod l),
      clPull L le_rfl (ZMod l) (ZMod l) θ = fun u => Multiplicative.toAdd ((x : galOf K L Ω → Multiplicative (ZMod l)) u) := by
    rintro ⟨x, φ, rfl⟩
    have h := hmem φ
    rw [← hpull] at h
    obtain ⟨θ, hθ, e⟩ := h
    exact ⟨θ, hθ, e⟩
  choose θ hθ he using hch
  have hadd : ∀ x, ∀ a b, θ x (a * b) = θ x a + θ x b := by
    intro x
    have := hθ x
    simp only [ClDual] at this
    exact this.1
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (ClassGroup (𝓞 L) →* Multiplicative (ZMod l)) :=
    Finite.of_injective (fun f : ClassGroup (𝓞 L) →* Multiplicative (ZMod l) => (f : ClassGroup (𝓞 L) → Multiplicative (ZMod l))) DFunLike.coe_injective
  have hrange : Nat.card Ψ.range ≤ Nat.card (ClassGroup (𝓞 L) →* Multiplicative (ZMod l)) := by
    refine Nat.card_le_card_of_injective
      (fun x => ({ toFun := fun c => Multiplicative.ofAdd (θ x c)
                   map_one' := ?_
                   map_mul' := ?_ } : ClassGroup (𝓞 L) →* Multiplicative (ZMod l))) ?_
    · have := hadd x 1 1
      simp only [mul_one] at this
      simp [show θ x 1 = 0 by simpa using this]
    · intro a b
      simp [hadd x a b, ofAdd_add]
    · intro x y h
      have h2 : θ x = θ y := by
        funext c
        have := DFunLike.congr_fun h c
        simpa using this
      apply Subtype.ext
      funext u
      have := congrFun (he y) u
      rw [← h2, he x] at this
      exact this
  rw [← Subgroup.card_mul_index Ψ.ker, Subgroup.index_ker]
  exact Nat.mul_le_mul hker hrange
