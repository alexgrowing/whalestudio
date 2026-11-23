import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandOperatorExtensionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandValuesShiftStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocalStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.InfCharExt

variable {n : ℕ}

theorem kset_sub_ujset (ε : Fin n → Bool) : ∀ g ∈ Kset ε, g ∈ UJset ε := by
  intro g hg
  obtain ⟨hu, hc⟩ := hg
  show gᴴ * Jm ε * g = Jm ε
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc]
  rw [show gᴴ = star g from rfl, h1, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem ext_eq_on_su {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hE : Ext ε m π' π) : ∀ g ∈ SUset ε, π g = π' g := by
  intro g hg
  have := hE 1 (by simp) g hg
  simpa using this

theorem kfin_to_kfinS {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hE : Ext ε m π' π) {v : H} (hv : IsKFin ε π v) : IsKFinS ε π' v := by
  obtain ⟨S, hS, hvS, hst⟩ := hv
  refine ⟨S, hS, hvS, ?_⟩
  intro g hg x hx
  have hgS : g ∈ SUset ε := ⟨kset_sub_ujset ε g hg.1, hg.2⟩
  rw [← ext_eq_on_su hE g hgS]
  exact hst g hg.1 x hx

theorem coeff_shift {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hE : Ext ε m π' π) (v w : H) :
    ∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, (fun g => ⟪w, π g v⟫_ℂ) (z • g) = z ^ m * (fun g => ⟪w, π' g v⟫_ℂ) g := by
  intro z hz g hg
  simp only
  rw [hE z hz g hg, ContinuousLinearMap.smul_apply, inner_smul_right]

end GlobalTheory.InfCharExt

theorem GlobalTheory.infChar_of_ext : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π →
    ∀ χ : Fin n → ℂ, HasInfCharS ε χ π' → HasInfChar ε (fun a => χ a + (m : ℂ) / n) π := by
  intro n hn ε H _ _ m π' π hE χ hχ v w hv hw
  have hv' := GlobalTheory.InfCharExt.kfin_to_kfinS hE hv
  have hw' := GlobalTheory.InfCharExt.kfin_to_kfinS hE hw
  obtain ⟨hsm, heig⟩ := hχ v w hv' hw'
  obtain ⟨hG1, hG2⟩ := GlobalTheory.T.gelfand_operator_extension n hn ε m (fun g => ⟪w, π g v⟫_ℂ) (fun g => ⟪w, π' g v⟫_ℂ)
    (GlobalTheory.InfCharExt.coeff_shift hE v w) hsm
  refine ⟨hG1, ?_⟩
  intro k g hg
  obtain ⟨hsplit, -, -⟩ := GlobalTheory.T.unitary_to_special_unitary_local n hn ε
  obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := hsplit g hg
  obtain ⟨hval, hval0, -⟩ := GlobalTheory.T.gelfand_values_shift n χ
  rw [hG2 k z hz g₀ hg₀, GlobalTheory.InfCharExt.coeff_shift hE v w z hz g₀ hg₀, hval]
  conv_rhs => rw [Finset.sum_range_succ', hval0]
  have hS : ∀ j ∈ range (k + 1), ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k - j) *
      gelfS ε j (fun g => ⟪w, π' g v⟫_ℂ) g₀ =
      ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k + 1 - (j + 1)) * gelfVal χ (j + 1) *
        ⟪w, π' g₀ v⟫_ℂ := by
    intro j _
    rw [heig j g₀ hg₀, Nat.add_sub_add_right]
    ring
  rw [Finset.sum_congr rfl hS, ← Finset.sum_mul]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
  ring
