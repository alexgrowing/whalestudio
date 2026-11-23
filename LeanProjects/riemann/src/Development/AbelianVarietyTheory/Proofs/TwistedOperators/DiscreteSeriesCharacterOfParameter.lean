import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacterSUTrivialTwo
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsGlobalCharDetPow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraPermute
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraParameterDescent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCharFnExt

noncomputable section

namespace GlobalTheory.DSUFromSU.Small

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.HCChar GlobalTheory.FormalDegree.Model
open GlobalTheory.Dec (IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep IsCharFn IsRegSS)

def Concl {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) (lam : Fin n → ℝ) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
    (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h : IsSqIntIrr ε σ),
    (∃ S : Submodule ℂ V, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S) ∧
    (∀ (ν : Fin n → ℝ) (S : Submodule ℂ V), IsKTypeOf ε σ ν S → ∃ c : Fin n → Fin n → ℕ,
      (∀ a b, c a b ≠ 0 → a < b) ∧ ν = Formalism.QuantumDeterminants.lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) ∧
    ∃ Θ, IsCharFn (ujMat ε) μ (ujRep h.2.2.1) Θ ∧
      ∀ θ : Fin n → ℝ, IsRegSS (ujMat ε (torusPt ε θ)) → Θ (torusPt ε θ) = dsChar ε lam θ

theorem diag_mem_K {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    (diagonal fun a => Complex.exp (θ a * Complex.I)) ∈ Kset ε := by
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 ?_, ?_⟩
  · rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  · simp only [Jm, diagonal_mul_diagonal, mul_comm]

theorem wt_unique {n : ℕ} (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (ℂ →L[ℂ] ℂ)) {ν ν' : Fin n → ℝ}
    {v v' : ℂ} (hv : v ≠ 0) (hv' : v' ≠ 0) (h : IsWtOn (Kset ε) σ ν v) (h' : IsWtOn (Kset ε) σ ν' v') : ν = ν' := by
  have key : ∀ θ : Fin n → ℝ, Complex.exp ((∑ a, ν a * θ a : ℝ) * Complex.I) =
      Complex.exp ((∑ a, ν' a * θ a : ℝ) * Complex.I) := fun θ => by
    have e := h θ (diag_mem_K ε θ)
    have e' := h' θ (diag_mem_K ε θ)
    set T := σ (diagonal fun a => Complex.exp (θ a * Complex.I))
    have t : ∀ w : ℂ, T w = T 1 * w := fun w => by
      rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    rw [t, smul_eq_mul] at e e'
    exact (mul_right_cancel₀ hv e).symm.trans (mul_right_cancel₀ hv' e')
  funext a
  by_contra hne
  have hd : ν a - ν' a ≠ 0 := sub_ne_zero.2 hne
  have := key (Pi.single a (Real.pi / (ν a - ν' a)))
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  have e : ν a * (Real.pi / (ν a - ν' a)) = ν' a * (Real.pi / (ν a - ν' a)) + Real.pi := by field_simp; ring
  rw [e, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I] at this
  exact Complex.exp_ne_zero _ (by linear_combination (-1 / 2 : ℂ) * this)

theorem concl_detPow (n : ℕ) (s : Bool) (m : ℤ) (μ : Measure (UJ fun _ : Fin n => s)) [μ.IsHaarMeasure] :
    Formalism.QuantumDeterminants.IsHCParam (lamDet n m) ∧ Concl (fun _ : Fin n => s) μ (lamDet n m) := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.HCChar.Model.ds_case n s m μ
  obtain ⟨Θ, h3, h4⟩ := h2 h1.2.2.1
  refine ⟨h0, ℂ, inferInstance, inferInstance, inferInstance, detPow n m,
    ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1⟩, h1.2.2.2.2.2.1, fun ν S hS => ⟨0, by simp, ?_⟩, Θ, h3.1, h4⟩
  obtain ⟨S', hS'⟩ := h1.2.2.2.2.2.1
  obtain ⟨v, -, hv, hw⟩ := hS.2.2.2.1
  obtain ⟨v', -, hv', hw'⟩ := hS'.2.2.2.1
  simpa using wt_unique _ _ hv hv' hw hw'

theorem rank_zero (ε : Fin 0 → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (lam : Fin 0 → ℝ) : Concl ε μ lam := by
  obtain rfl : ε = fun _ => true := Subsingleton.elim _ _
  obtain rfl : lam = lamDet 0 0 := Subsingleton.elim _ _
  exact (concl_detPow 0 true 0 μ).2

theorem rank_one (ε : Fin 1 → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (lam : Fin 1 → ℝ)
    (h : Formalism.QuantumDeterminants.IsHCParam lam) : Concl ε μ lam := by
  obtain ⟨s, rfl⟩ : ∃ s, ε = fun _ => s := ⟨ε 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨m, hm⟩ := h.2 0
  obtain rfl : lam = lamDet 1 m := by
    funext a
    rw [Subsingleton.elim a 0]
    simp [lamDet, Formalism.QuantumDeterminants.rhoStd] at hm ⊢
    exact hm
  exact (concl_detPow 1 s m μ).2

end GlobalTheory.DSUFromSU.Small

end

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.HCChar GlobalTheory.SUChar GlobalTheory.Published
open GlobalTheory.Orb (ujMat ujRep IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset IsParS IsParU IsHCS IsHCU Ext exists_isHaarMeasure_SUJ)
open GlobalTheory.DSId (IsHCDS)
open GlobalTheory.SqIntSU (scalarMul unitScalar)

namespace GlobalTheory.DSUFromSU

variable {n : ℕ}

theorem isRegSS_diagonal_iff (d : Fin n → ℂ) : IsRegSS (diagonal d) ↔ Function.Injective d := by
  rw [IsRegSS, charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]

theorem isRegSS_diagonal_mul (d : Fin n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    IsRegSS (diagonal d) → IsRegSS (diagonal fun a => d a * c) := by
  rw [isRegSS_diagonal_iff, isRegSS_diagonal_iff]
  exact fun h a b e => h (mul_right_cancel₀ hc e)

theorem torusPt_eq_scalarMul (ε : Fin n → Bool) (θ : Fin n → ℝ) (φ : ℝ) (h : ∑ a, (θ a - φ) = 0) :
    torusPt ε θ = scalarMul ε (Circle.exp φ, suTorusPt ε (fun a => θ a - φ) h) := by
  apply Subtype.ext
  apply Units.ext
  show diagonal (fun a => Complex.exp (θ a * Complex.I)) =
    (Circle.exp φ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun a => Complex.exp (((θ a - φ : ℝ) : ℂ) * Complex.I))
  rw [Matrix.smul_mul, Matrix.one_mul, ← diagonal_smul]
  congr 1
  funext a
  rw [Pi.smul_apply, smul_eq_mul, Circle.coe_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem weylDenom_sub_const (θ : Fin n → ℝ) (φ : ℝ) : weylDenom (fun a => θ a - φ) = weylDenom θ := by
  simp only [weylDenom, sub_sub_sub_cancel_right]

theorem wtVal_twist (hn : n ≠ 0) (lam θ : Fin n → ℝ) (m : ℤ) (hm : ∑ a, lam a = m) (w : Equiv.Perm (Fin n)) :
    wtVal (lam ∘ w.symm) θ = (Circle.exp ((∑ a, θ a) / n) : ℂ) ^ m *
      wtVal ((fun a => lam a - (m : ℝ) / n) ∘ w.symm) (fun a => θ a - (∑ b, θ b) / n) := by
  have hsum : ∑ a, lam (w.symm a) = m := by rw [Equiv.sum_comp w.symm lam]; exact hm
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [Circle.coe_exp, wtVal, wtVal, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  have key : (∑ a, (lam ∘ w.symm) a * θ a) = (m : ℝ) * ((∑ a, θ a) / n) +
      ∑ a, ((fun a => lam a - (m : ℝ) / n) ∘ w.symm) a * (θ a - (∑ b, θ b) / n) := by
    simp only [Function.comp_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
    field_simp
    ring
  rw [key]
  push_cast
  ring

theorem dsChar_twist (ε : Fin n → Bool) (hn : n ≠ 0) (lam θ : Fin n → ℝ) (m : ℤ) (hm : ∑ a, lam a = m) :
    dsChar ε lam θ = (Circle.exp ((∑ a, θ a) / n) : ℂ) ^ m *
      dsChar ε (fun a => lam a - (m : ℝ) / n) (fun a => θ a - (∑ b, θ b) / n) := by
  simp only [dsChar, wtVal_twist hn lam θ m hm, weylDenom_sub_const]
  have : ∀ s : Finset (Equiv.Perm (Fin n)), ∀ (c : ℂ) (f g : Equiv.Perm (Fin n) → ℂ),
      ∑ w ∈ s, f w * (c * g w) = c * ∑ w ∈ s, f w * g w := fun s c f g => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

end GlobalTheory.DSUFromSU

namespace GlobalTheory.DSUFromSU

theorem discreteSeriesCharacterOfParameter (hP : DiscreteSeriesCharacterSU) : DiscreteSeriesCharacterOfParameter := by
  intro n ε μ _ lam hlam
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact Small.rank_zero ε μ lam
    · exact Small.rank_one ε μ lam hlam
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hU : IsParU lam := ⟨hlam.1.injective, hlam.2⟩
  obtain ⟨m, hm, hS, -⟩ := GlobalTheory.SUtoU.extension_main n hn1 ε ℂ (fun _ => 0) lam hU
  obtain ⟨μ', hμ'⟩ := exists_isHaarMeasure_SUJ ε
  obtain ⟨V, i1, i2, i3, σ, hσ, Θ', hΘ', hform⟩ := hP n hn ε μ' _ hS
  obtain ⟨m2, hm2, -, hext⟩ := GlobalTheory.SUtoU.extension_main n hn1 ε V σ lam hU
  have e : m2 = m := by exact_mod_cast hm2.symm.trans hm
  rw [e] at hext
  obtain ⟨π, hE, hHC⟩ := hext hσ
  have hDS : IsHCDS ε lam π := by
    have h := GlobalTheory.DSSU.Chamber.vChamber n ε V π lam 1 (fun a b h _ => h) hlam.1 hHC
    simpa only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Function.comp_id, Matrix.submatrix_id_id] using h
  obtain ⟨Θ, hΘ, hΘf⟩ := GlobalTheory.ExtChar.exists_isCharFn_ext n hn1 ε μ μ' V m σ π hσ.1.2.2.1 hDS.1.2.2.1 hE Θ' hΘ'
  refine ⟨V, i1, i2, i3, π, hDS.1, hDS.2.2.1.exists, hDS.2.2.2, Θ, hΘ, fun θ hreg => ?_⟩
  have hθ' : ∑ a, (θ a - (∑ b, θ b) / n) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hreg' : IsRegSS (suMat ε (suTorusPt ε (fun a => θ a - (∑ b, θ b) / n) hθ')) := by
    rw [suMat_suTorusPt]
    rw [ujMat_torusPt] at hreg
    have h := isRegSS_diagonal_mul _ (Complex.exp_ne_zero ((-((∑ b, θ b) / n : ℝ) : ℂ) * Complex.I)) hreg
    convert h using 3 with a
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hanti : StrictAnti fun a => lam a - (m : ℝ) / n := fun a b h => sub_lt_sub_right (hlam.1 h) _
  rw [torusPt_eq_scalarMul ε θ _ hθ', hΘf _ _ hreg', hform _ hθ' hreg', chamberChar_of_strictAnti ε hanti,
    dsChar_twist ε hn0 lam θ m hm]

end GlobalTheory.DSUFromSU
