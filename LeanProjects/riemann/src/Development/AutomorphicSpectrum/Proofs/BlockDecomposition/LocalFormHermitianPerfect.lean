import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.HermForm

section Ring

variable {A : Type} [CommRing A] (c : A →+* A) {n : ℕ} (M : Matrix (Fin n) (Fin n) A)

theorem isHerm_hform (hc : ∀ a, c (c a) = a) (hM : ∀ i j, c (M j i) = M i j) :
    IsHerm c (Formalism.UG.hform c M) := by
  refine ⟨fun x y z => ?_, fun a x y => ?_, fun x y => ?_⟩
  · simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [Formalism.UG.hform, map_sum, map_mul, hc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hM]
    ring

theorem hform_eq_dotProduct (x y : Fin n → A) :
    Formalism.UG.hform c M x y = ((fun i => c (x i)) ᵥ* M) ⬝ᵥ y := by
  simp only [Formalism.UG.hform, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem isPerfect_hform (hc : ∀ a, c (c a) = a) (hM : IsUnit M.det) :
    IsPerfect (Formalism.UG.hform c M) := by
  refine ⟨fun x hx => ?_, fun f => ?_⟩
  · have hv : (fun i => c (x i)) ᵥ* M = 0 := by
      funext j
      have h1 := hx (Pi.single j 1)
      rw [hform_eq_dotProduct] at h1
      simpa using h1
    have h0 : (fun i => c (x i)) = 0 := by
      have h2 := congrArg (fun v => v ᵥ* M⁻¹) hv
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hM] using h2
    funext i
    have h3 : c (x i) = 0 := by simpa using congrFun h0 i
    have h4 := hc (x i)
    rw [h3, map_zero] at h4
    simpa using h4.symm
  · refine ⟨fun i => c (((fun k => f (fun j => if k = j then 1 else 0)) ᵥ* M⁻¹) i), fun y => ?_⟩
    rw [hform_eq_dotProduct]
    simp only [hc]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hM, Matrix.vecMul_one]
    conv_rhs => rw [pi_eq_sum_univ y]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Ring

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem sigR_inclR (a : E) : sigR R σ (inclR (F := F) R a) = inclR (F := F) R (σ a) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem sigR_sigR_of_invol (hσ : ∀ x, σ (σ x) = x) (t : R ⊗[F] E) : sigR R σ (sigR R σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isUnit_det_JR (h : J.det ≠ 0) : IsUnit (JR (F := F) R J).det := by
  have h1 : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det]
    rfl
  rw [h1]
  exact (isUnit_iff_ne_zero.mpr h).map _

end Tensor

end GlobalTheory.CompanionTheory.KFin.HermForm

namespace GlobalTheory.CompanionTheory.KFin

theorem isHerm_isPerfect_hR : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsCMExt F E σ → IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsHerm (sigR (Fv F v) σ) (hR (Fv F v) σ J) ∧ IsPerfect (hR (Fv F v) σ J) := by
  intro F E _ _ _ _ _ σ n J hCM hJ v
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hinv : ∀ x : E, σ (σ x) = x := by
    intro x
    apply (w.embedding).injective
    rw [hCM.2.2.2, hCM.2.2.2]
    exact star_star _
  have hc : ∀ a, sigR (Fv F v) σ (sigR (Fv F v) σ a) = a :=
    HermForm.sigR_sigR_of_invol (Fv F v) σ hinv
  have hM : ∀ i j, sigR (Fv F v) σ (JR (F := F) (Fv F v) J j i) = JR (F := F) (Fv F v) J i j := by
    intro i j
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply]
    rw [HermForm.sigR_inclR, hJ.1]
  exact ⟨HermForm.isHerm_hform _ _ hc hM,
    HermForm.isPerfect_hform _ _ hc (HermForm.isUnit_det_JR (F := F) (Fv F v) J hJ.2)⟩

end GlobalTheory.CompanionTheory.KFin

end
