import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfK
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfA
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfAs

noncomputable section

open Formalism.L2.Theta Formalism.IndefR.Datum Matrix Filter Topology
open scoped ComplexOrder

namespace Formalism.IndefR.Tow.SobPf

section Gen

variable {n : ℕ}

theorem det_G_unit {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsUnit G.det := by
  rw [isUnit_iff_ne_zero]
  have h1 := hs.2.2.det_pos.ne'
  rw [Matrix.det_mul] at h1
  exact left_ne_zero_of_mul h1

theorem det_UH_unit {G g : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    IsUnit g.det := by
  have h : gᴴ * G * g = G := hg
  have h' := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h'
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h'
  exact hG.ne_zero h'.symm

theorem inv_mem_UH {G g : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have hd := det_UH_unit hG hg
  have h : gᴴ * G * g = G := hg
  show (g⁻¹)ᴴ * G * g⁻¹ = G
  calc (g⁻¹)ᴴ * G * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * G * g) * g⁻¹ := by rw [h]
    _ = (g * g⁻¹)ᴴ * G * (g * g⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [mul_assoc]
    _ = G := by rw [Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one, one_mul, mul_one]

theorem conj_mem_lieG {G g X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (hX : X ∈ lieG G) : g⁻¹ * X * g ∈ lieG G := by
  have hd := det_UH_unit hG hg
  have h : gᴴ * G * g = G := hg
  have hX' : Xᴴ * G + G * X = 0 := hX
  have e0 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hd
  have e1 : G * g⁻¹ = gᴴ * G := by
    calc G * g⁻¹ = gᴴ * G * g * g⁻¹ := by rw [h]
      _ = gᴴ * G := by rw [Matrix.mul_assoc, e0, Matrix.mul_one]
  have e2 : (g⁻¹)ᴴ * G = G * g := by
    calc (g⁻¹)ᴴ * G = (g⁻¹)ᴴ * (gᴴ * G * g) := by rw [h]
      _ = (g * g⁻¹)ᴴ * G * g := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G * g := by rw [e0, Matrix.conjTranspose_one, Matrix.one_mul]
  show (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = gᴴ * Xᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * X * g := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * G + G * X) * g := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem deriv_clm_inv (A B : H →L[ℂ] H) (hBA : ∀ v, B (A v) = v) (f : ℝ → H) :
    deriv (fun t => A (f t)) 0 = A (deriv f 0) := by
  by_cases hf : DifferentiableAt ℝ f 0
  · exact ((A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hf.hasDerivAt).deriv
  · have hAf : ¬ DifferentiableAt ℝ (fun t => A (f t)) 0 := by
      intro h
      apply hf
      have e : (fun t => B (A (f t))) = f := funext fun t => hBA (f t)
      rw [← e]
      exact (B.restrictScalars ℝ).differentiableAt.comp 0 h
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hAf, map_zero]

theorem dRep_rep {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) (hG : IsUnit G.det) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (u : H) :
    dRep π X (π g u) = π g (dRep π (g⁻¹ * X * g) u) := by
  have hd := det_UH_unit hG hg
  have hY := conj_mem_lieG hG hg hX
  have hfun : (fun t : ℝ => π (NormedSpace.exp (t • X)) (π g u)) =
      fun t : ℝ => π g (π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) := by
    funext t
    have he : NormedSpace.exp (t • X) * g = g * NormedSpace.exp (t • (g⁻¹ * X * g)) := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul,
        Matrix.exp_conj' g (t • X) ((Matrix.isUnit_iff_isUnit_det _).2 hd)]
      simp only [← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul]
    calc π (NormedSpace.exp (t • X)) (π g u) = π (NormedSpace.exp (t • X) * g) u := by
          rw [hπ.2.1 _ (expS_mem_UH hX t) _ hg]; rfl
      _ = π (g * NormedSpace.exp (t • (g⁻¹ * X * g))) u := by rw [he]
      _ = π g (π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) := by
          rw [hπ.2.1 _ hg _ (expS_mem_UH hY t)]; rfl
  have hBA : ∀ v, π g⁻¹ (π g v) = v := by
    intro v
    rw [← ContinuousLinearMap.comp_apply, ← hπ.2.1 _ (inv_mem_UH hG hg) _ hg, Matrix.nonsing_inv_mul _ hd, hπ.1]
    rfl
  show deriv (fun t : ℝ => π (NormedSpace.exp (t • X)) (π g u)) 0 =
    π g (deriv (fun t : ℝ => π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) 0)
  rw [hfun]
  exact deriv_clm_inv (π g) (π g⁻¹) hBA _

theorem dL_rep {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) (hG : IsUnit G.det) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ lieG G) (u : H) :
    dL π l (π g u) = π g (dL π (l.map fun X => g⁻¹ * X * g) u) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    show dRep π X (dL π l (π g u)) = π g (dRep π (g⁻¹ * X * g) (dL π (l.map fun X => g⁻¹ * X * g) u))
    rw [ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)), dRep_rep hπ hG hg (hl X (by simp)) _]

end Gen

theorem isOpen_near {n : ℕ} (δ : ℝ) (f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f) :
    IsOpen {k | ∀ i j, ‖f k i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ} := by
  have hcont : ∀ i j, Continuous fun k => ‖f k i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ :=
    fun i j => ((hf.matrix_elem i j).sub continuous_const).norm
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt (hcont i j) continuous_const

theorem foldBddK_of (h4 : SobChart) : FoldBddK := by
  intro n H _ _ G s π hs hπ w hw l hl
  have hG := det_G_unit hs
  have hc1 : Cont1 := continuity_of_sobolev_chart h4 foldCont_holds
  have hcont : ContinuousOn (fun k : Fin n → Fin n → ℂ => dL π l (π (Matrix.of k) w))
      {k | Matrix.of k ∈ KAt G s} := by
    intro k0 hk0
    have hk0K : Matrix.of k0 ∈ KAt G s := hk0
    have hk0U : Matrix.of k0 ∈ Formalism.QuantumDeterminants.UH G := hk0K.1
    have hd := det_UH_unit hG hk0U
    have hl' : ∀ X ∈ l.map (fun X => (Matrix.of k0)⁻¹ * X * Matrix.of k0), X ∈ lieG G := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact conj_mem_lieG hG hk0U (hl Y hY)
    refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hδ'⟩ := hc1 G s π hs hπ w hw _ hl' ε hε
    have hO : IsOpen {k : Fin n → Fin n → ℂ |
        ∀ i j, ‖((Matrix.of k0)⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ} := by
      have hc : ∀ i j, Continuous fun k : Fin n → Fin n → ℂ =>
          ‖((Matrix.of k0)⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ := fun i j =>
        (((continuous_const.matrix_mul
          (continuous_id' : Continuous fun k : Fin n → Fin n → ℂ => Matrix.of k)).matrix_elem i j).sub
            continuous_const).norm
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt (hc i j) continuous_const
    have hk0O : ∀ i j, ‖((Matrix.of k0)⁻¹ * Matrix.of k0) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ := by
      intro i j
      rw [Matrix.nonsing_inv_mul _ hd, sub_self, norm_zero]
      exact hδ
    obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO k0 hk0O
    refine ⟨ρ, hρ, fun {k} hk hdk => ?_⟩
    have hkK : Matrix.of k ∈ KAt G s := hk
    have hkU : Matrix.of k ∈ Formalism.QuantumDeterminants.UH G := hkK.1
    have hg : (Matrix.of k0)⁻¹ * Matrix.of k ∈ Formalism.QuantumDeterminants.UH G := mul_mem_UH₂ G _ (inv_mem_UH hG hk0U) _ hkU
    have hnear := hρO (Metric.mem_ball.2 hdk)
    have hkk : π (Matrix.of k) w = π (Matrix.of k0) (π ((Matrix.of k0)⁻¹ * Matrix.of k) w) := by
      rw [← ContinuousLinearMap.comp_apply, ← hπ.2.1 _ hk0U _ hg, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
    rw [dist_eq_norm]
    rw [hkk, dL_rep hπ hG hk0U l hl, dL_rep hπ hG hk0U l hl, ← map_sub, hπ.2.2.1 _ hk0U]
    exact hδ' _ hg hnear
  have hK : IsCompact {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isCompact_KAt hs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  exact ⟨C, fun k hk => hC (Matrix.of.symm k) hk⟩

end Formalism.IndefR.Tow.SobPf

end
