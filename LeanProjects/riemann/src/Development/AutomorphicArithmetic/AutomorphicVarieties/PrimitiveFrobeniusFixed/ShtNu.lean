import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.shtNu :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F : ℕ) (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → ∀ δ : G ℚ Ω, IsUnit ((α δ : O) - 1) → ∀ a : O, a ∣ (l : O) ^ m → ∀ c ∈ ShT (QO l O) α δ F a,
    IsNu (l ^ m) F F α c ∧ ((∀ u ∈ fixMu ℚ Ω F, c u = 0) → c = 0) ∧
    ∀ (q : ℕ) (A : ValuationSubring Ω) (φ : G ℚ Ω), q.Prime → q ≡ 1 [MOD F] → Over A q → IsFrob (F := ℚ) A q φ → c φ = 0 →
      ∀ A' : ValuationSubring Ω, Over A' q → ∀ g ∈ Dec (F := ℚ) A', c g = 0 := by
  intro Ω _ _ _ l _ O _ _ _ _ _ N₀ m F α hD δ hδ a ha c hc
  obtain ⟨⟨hlc, hcoc⟩, hcδ, hac, hunr, -⟩ := hc
  have hkill : ∀ x ∈ fixMu ℚ Ω F, ∀ w : QO l O, a • w = 0 → (α x : O) • w = w := by
    intro x hx w hw
    obtain ⟨t, ht⟩ := hD.triv x hx
    obtain ⟨b, hb⟩ := ha
    have h1 : ((α x : O) - 1) • w = 0 := by
      rw [ht, hb, show a * b * t = (b * t) * a by ring, mul_smul, hw, smul_zero]
    rwa [sub_smul, one_smul, sub_eq_zero] at h1
  have h1 : c 1 = 0 := by
    have e := hcoc 1 1
    simp only [mul_one, map_one, Units.val_one, one_smul] at e
    simpa using e
  have heqv : ∀ g u, u ∈ fixMu ℚ Ω F → c (g * u * g⁻¹) = (α g : O) • c u := by
    intro g u hu
    have e1 := hcoc (g * u) g⁻¹
    have e2 := hcoc g u
    have e3 := hcoc g g⁻¹
    rw [mul_inv_cancel, h1] at e3
    rw [e1, e2, map_mul, Units.val_mul, mul_smul, hkill u hu _ (hac _), add_right_comm, ← e3, zero_add]
  have hF : F ≠ 0 := by
    rw [hD.lev]
    have hl : l.Prime := Fact.out
    have hN : N₀ ≠ 0 := by
      rintro rfl
      exact hl.one_lt.ne' ((Nat.coprime_zero_left _).mp hD.cop)
    exact mul_ne_zero hN (pow_ne_zero _ hl.ne_zero)
  obtain ⟨-, hopen, hcomm, -, -, -, -, -, -, -⟩ := galBasic Ω F hF
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u hu v _
    rw [hcoc, hkill u hu _ (hac _)]
  · exact hlc.comp_continuous continuous_subtype_val
  · exact heqv
  · intro u _
    obtain ⟨b, hb⟩ := ha
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, hb, mul_comm, mul_smul, hac, smul_zero]
  · exact hunr
  · intro hz
    refine funext fun g => ?_
    have hk := hcomm g δ
    have e : g * δ = (g * δ * g⁻¹ * δ⁻¹) * (δ * g) := by group
    have e1 := hcoc g δ
    rw [hcδ, smul_zero, add_zero, e, hcoc _ (δ * g), hz _ hk, zero_add,
      hkill _ hk _ (hac _), hcoc δ g, hcδ, zero_add] at e1
    have e2 : ((α δ : O) - 1) • c g = 0 := by rw [sub_smul, one_smul, e1, sub_self]
    exact (hδ.smul_eq_zero).mp e2
  · intro q A φ hq hq1 hA hφ hcφ A' hA' x hx
    obtain ⟨-, -, -, hcopNot, hIne, -, hPows, hconj, hplace, hact⟩ := placeBasic Ω
    have hcop : q.Coprime F := hq1.gcd_eq.trans (Nat.gcd_one_left F)
    have hAF : ¬Over A F := hcopNot A q F hcop hA
    have hφF : φ ∈ fixMu ℚ Ω F := by
      intro y hy
      rw [hPows A q F φ hφ hAF y hy, pow_eq_pow_mod q hy, hq1, ← pow_eq_pow_mod 1 hy, pow_one]
    let K : Subgroup (G ℚ Ω) :=
      { carrier := {g | g ∈ fixMu ℚ Ω F ∧ c g = 0}
        mul_mem' := fun {u v} hu hv =>
          ⟨mul_mem hu.1 hv.1, by rw [hcoc, hu.2, hkill _ hu.1 _ (hac _), hv.2, add_zero]⟩
        one_mem' := ⟨one_mem _, h1⟩
        inv_mem' := fun {u} hu => by
          refine ⟨inv_mem hu.1, ?_⟩
          have e := hcoc u u⁻¹
          rw [mul_inv_cancel, h1, hu.2, zero_add, hkill _ hu.1 _ (hac _)] at e
          exact e.symm }
    have hKo : IsOpen (K : Set (G ℚ Ω)) := hopen.inter (hlc.isOpen_fiber 0)
    have hIK : Ine A ≤ K := fun g hg => ⟨hIne A F hAF hg, hunr A hAF g hg⟩
    obtain ⟨v, hv, hnv, -⟩ := hplace A q hq hA
    have hfr : IsFrob A (normV v) φ := by rw [hnv]; exact hφ
    have hDec : Dec A ≤ K := Kum.decGen ℚ Ω A v φ K hv hfr hKo hIK ⟨hφF, hcφ⟩
    obtain ⟨g, rfl⟩ := hconj A A' q hq hA hA'
    have hy := hDec (((hact A g).1 x).mp hx)
    have ex : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [ex, heqv g _ hy.1, hy.2, smul_zero]
