import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

variable (L : Type) [Field L] [NumberField L]

def compAt (v : HeightOneSpectrum (𝓞 L)) (a : (AdeleRing (𝓞 L) L)ˣ) : v.adicCompletion L :=
  (a : AdeleRing (𝓞 L) L).2 v

theorem compAt_mul (v : HeightOneSpectrum (𝓞 L)) (a b : (AdeleRing (𝓞 L) L)ˣ) :
    compAt L v (a * b) = compAt L v a * compAt L v b := rfl

theorem compAt_one (v : HeightOneSpectrum (𝓞 L)) : compAt L v 1 = 1 := rfl

def levSub (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) : Subgroup (AdeleRing (𝓞 L) L)ˣ where
  carrier := {a | ∀ v, Valued.v (compAt L v a) = 1 ∧ (v ∈ S → Valued.v (compAt L v a - 1) ≤ WithZero.exp (-(N : ℤ)))}
  one_mem' := fun v => by
    refine ⟨by rw [compAt_one, map_one], fun _ => ?_⟩
    rw [compAt_one, sub_self, map_zero]
    exact zero_le
  mul_mem' := fun {a b} ha hb v => by
    rw [compAt_mul]
    refine ⟨by rw [map_mul, (ha v).1, (hb v).1, one_mul], fun hv => ?_⟩
    have e : compAt L v a * compAt L v b - 1 = compAt L v a * (compAt L v b - 1) + (compAt L v a - 1) := by ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ((ha v).2 hv))
    rw [map_mul, (ha v).1, one_mul]
    exact (hb v).2 hv
  inv_mem' := fun {a} ha v => by
    have h1 : compAt L v a * compAt L v a⁻¹ = 1 := by rw [← compAt_mul, mul_inv_cancel, compAt_one]
    have hv1 : Valued.v (compAt L v a⁻¹) = 1 := by
      have := congrArg Valued.v h1
      rwa [map_mul, (ha v).1, one_mul, map_one] at this
    refine ⟨hv1, fun hv => ?_⟩
    have e : compAt L v a⁻¹ - 1 = -(compAt L v a⁻¹ * (compAt L v a - 1)) := by
      linear_combination h1
    rw [e, Valuation.map_neg, map_mul, hv1, one_mul]
    exact (ha v).2 hv

end GlobalTheory.LevelChars

open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

theorem finite_chars {G : Type} [CommGroup G] (H : Subgroup G) [H.FiniteIndex] :
    {ψ : G →* ℂˣ | H ≤ ψ.ker}.Finite := by
  classical
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : NeZero (Nat.card (G ⧸ H)) := ⟨Nat.card_pos.ne'⟩
  let f : {ψ : G →* ℂˣ | H ≤ ψ.ker} → (G ⧸ H → rootsOfUnity (Nat.card (G ⧸ H)) ℂ) := fun ψ q =>
    ⟨QuotientGroup.lift H ψ.1 ψ.2 q, by
      rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]⟩
  have hf : Function.Injective f := by
    rintro ⟨ψ, hψ⟩ ⟨ψ', hψ'⟩ h
    refine Subtype.ext (MonoidHom.ext fun g => ?_)
    have := congrArg (fun F => ((F (QuotientGroup.mk g) : rootsOfUnity _ ℂ) : ℂˣ)) h
    simpa [f] using this
  exact Set.finite_coe_iff.1 (Finite.of_injective f hf)

theorem heckeFin_of
    (hA : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L),
      (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ levSub L S N, ψ.1 a = 1)
    (hC : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex) :
    ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite := by
  intro L _ _ I _ φ n S N hS
  classical
  rcases Set.eq_empty_or_nonempty {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧
    ∀ v ∈ S, χ.LevelLe v N} with h | ⟨χ0, hχ0⟩
  · rw [h]; exact Set.finite_empty
  haveI := hC L S N hS
  refine ((finite_chars ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N)).preimage (f := fun χ : Formalism.L2.Host.HChar L => (χ * χ0⁻¹).1)
    (fun χ _ χ' _ h => mul_right_cancel (Subtype.ext h))).subset ?_
  intro χ hχ
  show _ ≤ MonoidHom.ker _
  refine sup_le ?_ fun a ha => MonoidHom.mem_ker.2 (hA L S N (χ * χ0⁻¹) (fun k => ?_) (fun v hv x hx => ?_) (fun v hv x hx hle => ?_) a ha)
  · rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.2 ((χ * χ0⁻¹).2.2 k)
  · have e : χ.inf k = χ0.inf k := Units.ext ((hχ.1 k).trans (hχ0.1 k).symm)
    rw [Formalism.L2.Host.HChar.inf_mul, Formalism.L2.Host.HChar.inf_inv, e, mul_inv_cancel]
  · rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, hχ.2.1 v hv x hx, hχ0.2.1 v hv x hx, inv_one, one_mul]
  · rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, hχ.2.2 v hv x hx hle, hχ0.2.2 v hv x hx hle, inv_one,
      one_mul]

end GlobalTheory.LevelChars
