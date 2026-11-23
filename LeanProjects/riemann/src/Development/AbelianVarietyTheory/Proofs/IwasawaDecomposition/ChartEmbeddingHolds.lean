import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import ReciprocityTheory.GaloisValuations.GlobalB

noncomputable section

open NumberField IsDedekindDomain Pointwise
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Cht.EmbExt

def ballPre {Ω C : Type} [Field Ω] [NormedField C] [IsUltrametricDist C] (ι : Ω →+* C) : ValuationSubring Ω where
  toSubring := (intO C).comap ι
  mem_or_inv_mem' x := by
    change ‖ι x‖ ≤ 1 ∨ ‖ι x⁻¹‖ ≤ 1
    rw [map_inv₀, norm_inv]
    rcases le_total ‖ι x‖ 1 with h | h
    · exact Or.inl h
    · exact Or.inr (inv_le_one_of_one_le₀ h)

theorem mem_ballPre {Ω C : Type} [Field Ω] [NormedField C] [IsUltrametricDist C] (ι : Ω →+* C) (x : Ω) :
    x ∈ ballPre ι ↔ ‖ι x‖ ≤ 1 := Iff.rfl

theorem val_lt_one_iff {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (x : Ω) :
    A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]

theorem ballPre_lt_one {Ω C : Type} [Field Ω] [NormedField C] [IsUltrametricDist C] (ι : Ω →+* C) (x : Ω) :
    (ballPre ι).valuation x < 1 ↔ ‖ι x‖ < 1 := by
  rw [val_lt_one_iff, mem_ballPre, map_inv₀, norm_inv, not_le]
  by_cases hx : x = 0
  · simp [hx]
  · have h0 : 0 < ‖ι x‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hx)
    simp [hx, one_lt_inv₀ h0]

def idl (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) : Ideal (𝓞 F) :=
  (ReciprocityTheory.Gal.primeBelow (F := F) A).under (𝓞 F)

theorem mem_idl {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (x : 𝓞 F) :
    x ∈ idl F A ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := Iff.rfl

theorem idl_isPrime {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) :
    (idl F A).IsPrime := by
  unfold idl; infer_instance

theorem exists_ext {F Ω C : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] (A : ValuationSubring Ω) (f : F →+* C)
    (n : ℕ) (hn : n ≠ 0) (hp : ‖(n : C)‖ < 1) (h : ∀ x : F, algebraMap F Ω x ∈ A → ‖f x‖ ≤ 1) :
    ∃ ι : Ω →+* C, (∀ x, ι (algebraMap F Ω x) = f x) ∧ ∀ x ∈ A, ‖ι x‖ ≤ 1 := by
  letI : Algebra F C := f.toAlgebra
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  let ι₀ : Ω →ₐ[F] C := IsAlgClosed.lift
  have hι₀ : ∀ x, (ι₀ : Ω →+* C) (algebraMap F Ω x) = f x := fun x => ι₀.commutes x
  let A' := ballPre (ι₀ : Ω →+* C)
  have hle : idl F A' ≤ idl F A := by
    intro x hx
    rw [mem_idl, val_lt_one_iff] at hx ⊢
    refine hx.imp id fun h1 h2 => h1 ?_
    rw [← map_inv₀] at h2 ⊢
    rw [mem_ballPre, hι₀]
    exact h _ h2
  have hne : idl F A' ≠ ⊥ := by
    intro e
    have : (n : 𝓞 F) ∈ idl F A' := by
      rw [mem_idl, ballPre_lt_one]
      simpa using hp
    rw [e, Ideal.mem_bot] at this
    exact hn (by exact_mod_cast this)
  let v : HeightOneSpectrum (𝓞 F) := ⟨idl F A', idl_isPrime A', hne⟩
  have heq : idl F A' = idl F A := v.isMaximal.eq_of_le (idl_isPrime A).ne_top hle
  obtain ⟨g, hg⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over (A := A) (A' := A') (v := v)
    (fun x => by rw [← mem_idl, ← heq]) (fun x => by rw [← mem_idl])
  refine ⟨(ι₀ : Ω →+* C).comp (g : Ω →+* Ω), fun x => ?_, fun x hx => ?_⟩
  · rw [RingHom.comp_apply, ← hι₀]
    exact congrArg _ (g.commutes x)
  · have : g • x ∈ g • A := ValuationSubring.smul_mem_pointwise_smul_iff.2 hx
    rw [hg] at this
    exact this

end GlobalTheory.LocM.Cht.EmbExt

namespace GlobalTheory.LocM.Cht

theorem embSt : EmbSt := by
  intro p W F C f hp hW hF h
  haveI : NumberField ↥F := ⟨⟩
  have hle : F ≤ algebraicClosure ℚ ℂ := le_algebraicClosure ℚ ℂ F
  letI : Algebra ↥F ↥(algebraicClosure ℚ ℂ) := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ ↥F ↥(algebraicClosure ℚ ℂ) := IsScalarTower.of_algebraMap_eq fun x => by simp
  haveI : Algebra.IsAlgebraic ℚ ↥(algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : IsAlgClosure ↥F ↥(algebraicClosure ℚ ℂ) :=
    ⟨(algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed,
      Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have hpC : ‖(p : ↥C.S)‖ < 1 := by
    rw [C.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  obtain ⟨ι, h1, h2⟩ := EmbExt.exists_ext (W.comap (algebraicClosure ℚ ℂ).val.toRingHom) f p hp.ne_zero hpC
    (fun x hx => h x hx)
  exact ⟨ι, fun x _ => h1 x, fun x hx => h2 x hx⟩

end GlobalTheory.LocM.Cht
