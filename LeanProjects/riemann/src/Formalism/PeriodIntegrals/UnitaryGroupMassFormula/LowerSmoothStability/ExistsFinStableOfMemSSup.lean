import Mathlib
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.LowCyc
import Formalism.PeriodIntegrals.KFinSmooth

open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.LowSmooth

open PI.UpqRep

section Directed

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type*}

def FinStable (G : Set ι) (ρ : ι → H →L[ℂ] H) : Set (Submodule ℂ H) :=
  {S | FiniteDimensional ℂ S ∧ ∀ g ∈ G, ∀ x ∈ S, ρ g x ∈ S}

theorem finStable_bot (G : Set ι) (ρ : ι → H →L[ℂ] H) : (⊥ : Submodule ℂ H) ∈ FinStable G ρ := by
  refine ⟨inferInstance, fun g _ x hx => ?_⟩
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]

theorem finStable_directed (G : Set ι) (ρ : ι → H →L[ℂ] H) :
    DirectedOn (· ≤ ·) (FinStable G ρ) := by
  intro S hS T hT
  refine ⟨S ⊔ T, ⟨?_, ?_⟩, le_sup_left, le_sup_right⟩
  · haveI := hS.1
    haveI := hT.1
    infer_instance
  · intro g hg x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (hS.2 g hg y hy) (hT.2 g hg z hz)

theorem exists_finStable_of_mem_sSup (G : Set ι) (ρ : ι → H →L[ℂ] H) {F : Set (Submodule ℂ H)}
    (hF : F ⊆ FinStable G ρ) {x : H} (hx : x ∈ sSup F) : ∃ S ∈ FinStable G ρ, x ∈ S := by
  have hx' : x ∈ sSup (FinStable G ρ) := sSup_le_sSup hF hx
  exact (Submodule.mem_sSup_of_directed ⟨⊥, finStable_bot G ρ⟩ (finStable_directed G ρ)).mp hx'

end Directed

section Transport

variable {k r : ℕ}

theorem conj_mem_Kset {ε : Fin (2 * r + k + 1) → Bool} {P g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : IsCayleyU k r ε P)
    (hg : g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)) :
    P * g * P⁻¹ ∈ Kset ε ∧ P⁻¹ * (P * g * P⁻¹) * P = g := by
  obtain ⟨⟨_, hJ⟩, hPu⟩ := hP
  obtain ⟨hgH, hgu⟩ := hg
  have hPs : P * Pᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hPu
    rwa [Matrix.star_eq_conjTranspose] at this
  have hsP : Pᴴ * P = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hPu
    rwa [Matrix.star_eq_conjTranspose] at this
  have hgs : g * gᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hgu
    rwa [Matrix.star_eq_conjTranspose] at this
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hsP
  have hgH' : gᴴ * Hpk k r * g = Hpk k r := hgH

  have hcomm : g * Hpk k r = Hpk k r * g := by
    calc g * Hpk k r = g * (gᴴ * Hpk k r * g) := by rw [hgH']
      _ = (g * gᴴ) * Hpk k r * g := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * g := by rw [hgs, Matrix.one_mul]
  have hJm : Jm ε = P * Hpk k r * Pᴴ := by
    rw [← hJ]
    simp only [← Matrix.mul_assoc]
    rw [hPs, Matrix.one_mul, Matrix.mul_assoc, hPs, Matrix.mul_one]
  rw [hinv]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hPs' : Pᴴ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      exact hsP
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hPu hgu) hPs'
  · rw [hJm]
    calc P * g * Pᴴ * (P * Hpk k r * Pᴴ) = P * g * (Pᴴ * P) * Hpk k r * Pᴴ := by
          simp only [Matrix.mul_assoc]
      _ = P * (g * Hpk k r) * Pᴴ := by
          rw [hsP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = P * (Hpk k r * g) * Pᴴ := by rw [hcomm]
      _ = P * Hpk k r * (Pᴴ * P) * g * Pᴴ := by
          rw [hsP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = P * Hpk k r * Pᴴ * (P * g * Pᴴ) := by simp only [Matrix.mul_assoc]
  · calc Pᴴ * (P * g * Pᴴ) * P = (Pᴴ * P) * g * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hsP, Matrix.one_mul, Matrix.mul_one]

end Transport

theorem isKFinHpk_of_lowUnit {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {w : H}
    (hlow : IsLowUnitH k r ε lam σ w) : IsKFinHpk (k := k) (r := r) σ w := by
  obtain ⟨P, hP, -, hw⟩ := hlow
  obtain ⟨S, ⟨hfin, hst⟩, hwS⟩ := exists_finStable_of_mem_sSup (Kset ε) (fun h => σ (P⁻¹ * h * P))
    (F := {S | IsKTypeOf ε (fun h => σ (P⁻¹ * h * P)) (lowK ε lam) S})
    (fun S hS => ⟨hS.1, hS.2.1⟩) hw
  refine ⟨S, hfin, hwS, fun g hg x hx => ?_⟩
  obtain ⟨hK, hback⟩ := conj_mem_Kset hP hg
  have := hst _ hK x hx
  beta_reduce at this
  rwa [hback] at this

theorem lowSmooth_of_kFinSmooth (hK : PI.KFinSmooth) : PI.LowSmooth := by
  intro k r ε lam H _ _ _ σ w hHC hDS hlow
  exact hK k r ε lam H σ hHC hDS w (isKFinHpk_of_lowUnit hlow)

end PI.UnitaryGroupMassFormula.LowSmooth
