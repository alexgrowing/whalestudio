import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondIffRhoOfGoodPoint
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAlgebraMapPadicIntLeOne

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.CobConj

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_memO (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
  exact norm_le_one_of_isIntegral x (hi.map c.O.val)

def Sm (n : ℕ) (v : Fin 2 → Qbar l) : Prop := ∀ i, ‖v i‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖

theorem sm_add {n : ℕ} {a b : Fin 2 → Qbar l} (ha : Sm n a) (hb : Sm n b) : Sm n (a + b) := fun i =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))

theorem sm_neg {n : ℕ} {a : Fin 2 → Qbar l} (ha : Sm n a) : Sm n (-a) := fun i => by
  simpa using ha i

theorem sm_sub {n : ℕ} {a b : Fin 2 → Qbar l} (ha : Sm n a) (hb : Sm n b) : Sm n (a - b) := by
  rw [sub_eq_add_neg]; exact sm_add ha (sm_neg hb)

theorem sm_mulVec (c : Coef l) {n : ℕ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O)
    {a : Fin 2 → Qbar l} (ha : Sm n a) : Sm n (M *ᵥ a) := fun i => by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (norm_le_one_of_memO c (hM _ _)) (ha _) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])

theorem cv_iff {n : ℕ} {a b : Fin 2 → Qbar l} : Cv n a b ↔ Sm n (a - b) := Iff.rfl

theorem key_identity (Mσ Ms Mτ : Matrix (Fin 2) (Fin 2) (Qbar l)) (hτσ : Mτ * Mσ = 1)
    (zs' zσ zsτ zs zτ z1 x : Fin 2 → Qbar l) :
    zs' - ((Mσ * Ms * Mτ) *ᵥ (Mσ *ᵥ x - zσ) - (Mσ *ᵥ x - zσ)) =
      (zs' - (zσ + Mσ *ᵥ zsτ)) + Mσ *ᵥ (zsτ - (zs + Ms *ᵥ zτ)) + Mσ *ᵥ (zs - (Ms *ᵥ x - x))
        - Mσ *ᵥ (Ms *ᵥ (z1 - (z1 + (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z1)))
        - Mσ *ᵥ (Ms *ᵥ (z1 - (zτ + Mτ *ᵥ zσ))) := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.one_mulVec, Matrix.mul_assoc, hτσ,
    Matrix.mul_one]
  abel

theorem cob_conj : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (q : Pl) (B B' : ValuationSubring Ω), (∀ s i j, mat W s i j ∈ c.O) → Coc1 c n W ⊤ z → IsPlaceOver B q → IsPlaceOver B' q → Cob1 c n W (Ine (F := ℚ) B) z → Cob1 c n W (Ine (F := ℚ) B') z := by
  intro l _ Ω _ _ _ W c n z q B B' hW hC hB hB' hcob
  obtain ⟨x, hxO, hx⟩ := hcob
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hB hB'
  have hcoc : ∀ a b : G ℚ Ω, Sm n (z (a * b) - (z a + mat W a *ᵥ z b)) := fun a b =>
    hC.2.2 a (Subgroup.mem_top a) b (Subgroup.mem_top b)
  have hτσ : mat W σ⁻¹ * mat W σ = 1 := by
    simp only [mat, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h1 : mat W 1 = 1 := by simp [mat]
  refine ⟨mat W σ *ᵥ x - z σ, fun i => ?_, fun s' hs' => ?_⟩
  · simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.sub_mem (c.O.add_mem (c.O.mul_mem (hW _ _ _) (hxO _)) (c.O.mul_mem (hW _ _ _) (hxO _))) (hC.2.1 σ i)
  set s := σ⁻¹ * s' * σ with hsdef
  have hs : s ∈ Ine (F := ℚ) B := GlobalTheory.ParamRepCompare.conj_mem_Ine_of_smul_eq hσ hs'
  have e : s' = σ * (s * σ⁻¹) := by rw [hsdef]; group
  have hM : mat W s' = mat W σ * mat W s * mat W σ⁻¹ := by
    rw [e]; simp only [mat, map_mul, Units.val_mul, Matrix.mul_assoc]
  rw [cv_iff, hM, key_identity _ _ _ hτσ (z s') (z σ) (z (s * σ⁻¹)) (z s) (z σ⁻¹) (z 1) x]
  have hA : Sm n (z s' - (z σ + mat W σ *ᵥ z (s * σ⁻¹))) := by
    have := hcoc σ (s * σ⁻¹); rwa [← e] at this
  have hD : Sm n (z 1 - (z 1 + (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z 1)) := by
    have := hcoc 1 1; rwa [mul_one, h1] at this
  have hE : Sm n (z 1 - (z σ⁻¹ + mat W σ⁻¹ *ᵥ z σ)) := by
    have := hcoc σ⁻¹ σ; rwa [inv_mul_cancel] at this
  exact sm_sub (sm_sub (sm_add (sm_add hA (sm_mulVec c (hW σ) (hcoc s σ⁻¹))) (sm_mulVec c (hW σ) (hx s hs)))
    (sm_mulVec c (hW σ) (sm_mulVec c (hW s) hD))) (sm_mulVec c (hW σ) (sm_mulVec c (hW s) hE))

end GlobalTheory.Ord2.CobConj
