import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.I.WL

variable {F : Type} [Field F] [NumberField F]

private theorem comp_signed_mem {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (ε : κ → F)
    (hε : ∀ k, ε k * ε k = 1) {G : (κ → A F) → ℂ} (hG : G ∈ schwartzBruhatPi F κ) :
    (fun x : ι → A F => G fun k => rt (ε k) * x (e k)) ∈ schwartzBruhatPi F ι := by
  have hD : Matrix.diagonal ε * Matrix.diagonal ε = (1 : Matrix κ κ F) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact hε k
  let M : Matrix κ ι F := (Matrix.diagonal ε).submatrix id e.symm
  let N : Matrix ι κ F := (Matrix.diagonal ε).submatrix e.symm id
  have hNM : N * M = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) e.symm id e.symm
      Function.bijective_id
    rw [hD, Matrix.submatrix_one_equiv] at h
    exact h.symm
  have hMN : M * N = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) id e.symm id
      e.symm.bijective
    rw [hD, Matrix.submatrix_id_id] at h
    exact h.symm
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hG
  have hx : ∀ x : ι → A F, (M.map (algebraMap F (A F)) *ᵥ x) = fun k => rt (ε k) * x (e k) := by
    intro x
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.submatrix_apply, id]
    rw [← e.sum_comp]
    simp only [Matrix.diagonal_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simpa only [hx] using h

private def eS : Fin 3 ⊕ Unit ≃ Fin 4 where
  toFun := Sum.elim ![0, 2, 3] fun _ => 1
  invFun := ![.inl 0, .inr (), .inl 1, .inl 2]
  left_inv := by
    rintro (i | ⟨⟩)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

private def sn : Fin 3 ⊕ Unit → F := Sum.elim 1 fun _ => -1

private def FF (φ : V4 F → ℂ) (z : Fin 3 ⊕ Unit → A F) : ℂ := φ fun i => z (eS.symm i)

private theorem FF_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi F (Fin 4)) :
    FF φ ∈ schwartzBruhatPi F (Fin 3 ⊕ Unit) := by
  have h := comp_signed_mem (F := F) eS.symm (fun _ => 1) (fun _ => by simp) hφ
  have he : FF φ = fun x => φ fun k => rt ((fun _ => 1 : Fin 4 → F) k) * x (eS.symm k) := by
    funext x
    simp [FF]
  rw [he]
  exact h

private theorem hat_eq (φ : V4 F → ℂ) (x : V4 F) :
    hat φ x = GroundTheory.Heights₂.Theta.partialFourierPi (FF φ) fun k => rt (sn k) * x (eS k) := by
  have hmp := measurePreserving_funUnique (adeleMeasure F) Unit
  have h := hmp.integral_comp' (g := fun s => φ (Function.update x 1 s) * ψ (-(s * x 1)))
  rw [hat, ← h, GroundTheory.Heights₂.Theta.partialFourierPi, adelicFourierPi, adeleMeasurePi]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h1 : Function.update x 1 (MeasurableEquiv.funUnique Unit (A F) y) =
      fun i => (Sum.elim (fun i => rt (sn (Sum.inl i)) * x (eS (Sum.inl i))) y
        : Fin 3 ⊕ Unit → A F) (eS.symm i) := by
    funext i
    fin_cases i <;> simp [eS, sn]
  have h2 : ψ (-(MeasurableEquiv.funUnique Unit (A F) y * x 1)) =
      ((adelicChar F (∑ i, y i * (rt (sn (Sum.inr i)) * x (eS (Sum.inr i)))) : Circle) : ℂ) := by
    simp [ψ, eS, sn]
  simp only [FF]
  rw [h1, h2]

private theorem hat_add {a b : V4 F → ℂ} (ha : a ∈ schwartzBruhatPi F (Fin 4))
    (hb : b ∈ schwartzBruhatPi F (Fin 4)) (x : V4 F) : hat (a + b) x = hat a x + hat b x := by
  rw [hat_eq, hat_eq, hat_eq]
  have e : FF (a + b) = FF a + FF b := rfl
  rw [e]
  exact congrFun (adelicFourierPi_add
    (GroundTheory.Heights₂.Theta.integrable_partialFourierPi_slice (FF_mem ha) _)
    (GroundTheory.Heights₂.Theta.integrable_partialFourierPi_slice (FF_mem hb) _)) _

private theorem hat_smul (c : ℂ) (a : V4 F → ℂ) (x : V4 F) : hat (c • a) x = c * hat a x := by
  unfold hat
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp [mul_assoc]

private theorem normOneIntegral_add (M : Meas F) {u u' : G1 F → ℂ} (hu : Integrable (iw u) M.ν)
    (hu' : Integrable (iw u') M.ν) : M.I0 (fun g => u g + u' g) = M.I0 u + M.I0 u' := by
  unfold Meas.I0
  rw [← integral_add hu hu']
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp [iw, mul_add]

private theorem normOneIntegral_const_mul (M : Meas F) (c : ℂ) (u : G1 F → ℂ) :
    M.I0 (fun g => c * u g) = c * M.I0 u := by
  unfold Meas.I0
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [iw]
  ring

end UpperTheory.ConvolutionTheory.R2.I.WL

end

open UpperTheory.ConvolutionTheory.R2.I.WL in
theorem UpperTheory.ConvolutionTheory.R2.I.thetaIntegral_exists_bilinear :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (h : GL (Fin 2) (A E)),
      ∃ B : π.V →ₗ[ℂ] Fock (F := F) D.δ →ₗ[ℂ] ℂ, ∀ f φ, B f φ = W1 W M f.1.1 φ.1 h := by
  intro F E _ _ _ _ _ _ _ D W M π h
  have hint : ∀ (f : π.V) (φ : Fock (F := F) D.δ), Integrable (iw (w1 W f.1.1 φ.1 h)) M.ν :=
    fun f φ => (UpperTheory.ConvolutionTheory.R2.conv F E D W M π f.1 f.2 φ.1 φ.2 h).2.2.2.2
  have hL : ∀ f : π.V, Pp.Lf f.1.1 := fun f => (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f.1 f.2).1
  have hwf := UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F
  refine ⟨LinearMap.mk₂ ℂ (fun f φ => W1 W M f.1.1 φ.1 h) ?_ ?_ ?_ ?_, fun f φ => rfl⟩
  · intro f f' φ
    have e : w1 W (f + f').1.1 φ.1 h = fun g => w1 W f.1.1 φ.1 h g + w1 W f'.1.1 φ.1 h g := by
      funext g
      have := (hwf f.1.1 (hL f)).2.2.2.2 f'.1.1 (hL f') (gl g * dM (nu F h))
      simp only [w1]
      rw [← add_mul, ← this]
      rfl
    simp only [W1]
    rw [e]
    exact normOneIntegral_add M (hint f φ) (hint f' φ)
  · intro c f φ
    have e : w1 W (c • f).1.1 φ.1 h = fun g => c * w1 W f.1.1 φ.1 h g := by
      funext g
      have := (hwf f.1.1 (hL f)).2.2.2.1 c (gl g * dM (nu F h))
      simp only [w1]
      rw [← mul_assoc, ← this]
      rfl
    simp only [W1]
    rw [e]
    exact normOneIntegral_const_mul M c _
  · intro f φ φ'
    have e : w1 W f.1.1 (φ + φ').1 h = fun g => w1 W f.1.1 φ.1 h g + w1 W f.1.1 φ'.1 h g := by
      funext g
      simp only [w1]
      rw [← mul_add, ← hat_add (W.Om g (W.L h φ.1)).2 (W.Om g (W.L h φ'.1)).2]
      congr 2
      simp [map_add]
    simp only [W1]
    rw [e]
    exact normOneIntegral_add M (hint f φ) (hint f φ')
  · intro c f φ
    have e : w1 W f.1.1 (c • φ).1 h = fun g => c * w1 W f.1.1 φ.1 h g := by
      funext g
      simp only [w1]
      have e' : (W.Om g (W.L h (c • φ).1)).1 = c • (W.Om g (W.L h φ.1)).1 := by
        simp [map_smul]
      rw [e', hat_smul]
      ring
    simp only [W1]
    rw [e]
    exact normOneIntegral_const_mul M c _
