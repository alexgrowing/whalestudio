import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.TameGen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem exists_char_of_index {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (l : ℕ) [Fact l.Prime] (H : Subgroup Γ) (ho : IsOpen (H : Set Γ)) (hc : commutator Γ ≤ H)
    (hi : H.index = l) :
    ∃ φ : Γ → ZMod l, IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ a, φ a = 0 ↔ a ∈ H := by
  have hN : H.Normal := by
    refine ⟨fun a ha g => ?_⟩
    have hc' : g * a * g⁻¹ * a⁻¹ ∈ H :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top a))
    have h2 := H.mul_mem hc' ha
    simpa using h2
  have hQ : Nat.card (Γ ⧸ H) = l := hi
  have hM : Nat.card (Multiplicative (ZMod l)) = l := by
    rw [Nat.card_eq_fintype_card]
    simp
  haveI : IsCyclic (Γ ⧸ H) := isCyclic_of_prime_card hQ
  haveI : IsCyclic (Multiplicative (ZMod l)) := isCyclic_of_prime_card hM
  let e : (Γ ⧸ H) ≃* Multiplicative (ZMod l) := mulEquivOfCyclicCardEq (hQ.trans hM.symm)
  let f : Γ →* Multiplicative (ZMod l) := (e : (Γ ⧸ H) →* Multiplicative (ZMod l)).comp (QuotientGroup.mk' H)
  have hadd : ∀ a b, Multiplicative.toAdd (f (a * b)) = Multiplicative.toAdd (f a) + Multiplicative.toAdd (f b) := by
    intro a b
    rw [map_mul, toAdd_mul]
  have hker : ∀ a, Multiplicative.toAdd (f a) = 0 ↔ a ∈ H := by
    intro a
    have h1 : Multiplicative.toAdd (f a) = 0 ↔ f a = 1 := by
      constructor
      · intro h
        exact Multiplicative.toAdd.injective (by simpa using h)
      · intro h
        rw [h]
        rfl
    rw [h1]
    simp only [f, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply, MonoidHom.coe_coe,
      MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  refine ⟨fun a => Multiplicative.toAdd (f a), ?_, hadd, hker⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun h => x * h) '' (H : Set Γ), isOpenMap_mul_left x _ ho, ⟨1, H.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  show Multiplicative.toAdd (f (x * h)) = Multiplicative.toAdd (f x)
  rw [hadd, (hker h).2 hh, add_zero]

theorem UpperTheory.V.Fr.st_tame :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (A : ValuationSubring Ω), ¬ A.valuation (l : Ω) < 1 → ∀ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ H → H.index = l → ¬ Ine (F := ℚ) A ≤ H → ∀ y : G ℚ Ω → k, IsLocallyConstant y → (∀ s ∈ Ine (F := ℚ) A, ∀ t ∈ Ine (F := ℚ) A, y (s * t) = y s + y t) → ∀ s ∈ Ine (F := ℚ) A ⊓ H, y s = 0 := by
  intro Ω _ _ _ l _ k _ _ A hA H ho hc hi hIH y hy hyadd s hs
  obtain ⟨φ, hφc, hφa, hφk⟩ := exists_char_of_index l H ho hc hi
  obtain ⟨γ, hγ⟩ := UpperTheory.V.Two.tameGen ℚ Ω l A hA
  let φI : ↥(Ine (F := ℚ) A) → ZMod l := fun σ => φ σ
  have hφIc : IsLocallyConstant φI := hφc.comp_continuous continuous_subtype_val
  have hφIa : ∀ a b : ↥(Ine (F := ℚ) A), φI (a * b) = φI a + φI b := fun a b => hφa _ _
  have hγne : φI γ ≠ 0 := by
    intro h0
    apply hIH
    intro σ hσ
    exact (hφk σ).1 (hγ φI hφIc hφIa h0 ⟨σ, hσ⟩)
  letI : Algebra (ZMod l) k := ZMod.algebra k l
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod l)]
  intro μ
  let c : ZMod l := μ (y γ) / φI γ
  let ψ : ↥(Ine (F := ℚ) A) → ZMod l := fun σ => μ (y σ) - c * φI σ
  have hyI : IsLocallyConstant (fun σ : ↥(Ine (F := ℚ) A) => y σ) := hy.comp_continuous continuous_subtype_val
  have hψc : IsLocallyConstant ψ := IsLocallyConstant.comp₂ hyI hφIc (fun u v => μ u - c * v)
  have hψa : ∀ a b : ↥(Ine (F := ℚ) A), ψ (a * b) = ψ a + ψ b := by
    intro a b
    simp only [ψ]
    rw [hφIa, Subgroup.coe_mul, hyadd _ a.2 _ b.2, map_add]
    ring
  have hψγ : ψ γ = 0 := by
    simp only [ψ, c]
    rw [div_mul_cancel₀ _ hγne, sub_self]
  have h := hγ ψ hψc hψa hψγ ⟨s, hs.1⟩
  have h0 : φI ⟨s, hs.1⟩ = 0 := (hφk s).2 hs.2
  simp only [ψ] at h
  rw [h0, mul_zero, sub_zero] at h
  exact h
