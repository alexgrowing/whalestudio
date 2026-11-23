import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfA
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfAs
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfK
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.HasFDerivAtIntegralPIter

noncomputable section

open Formalism.IndefR.Datum MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexOrder

namespace Formalism.IndefR.Tow.SobPf.Avg

variable {n : ℕ}

theorem mem_UH_iff {G g : Matrix (Fin n) (Fin n) ℂ} : g ∈ Formalism.QuantumDeterminants.UH G ↔ gᴴ * G * g = G := by
  exact Iff.rfl

theorem isUnit_det_of_cartan {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsUnit G.det := by
  unfold Formalism.IndefR.Datum.IsCartanInv at hs
  obtain ⟨_, _, hp⟩ := hs
  have h : (G * s).det ≠ 0 := hp.det_pos.ne'
  rw [Matrix.det_mul] at h
  exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul h)

theorem isUnit_det_of_UH {G u : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hu : u ∈ Formalism.QuantumDeterminants.UH G) :
    IsUnit u.det := by
  have hu' : uᴴ * G * u = G := hu
  have h := congrArg Matrix.det hu'
  rw [Matrix.det_mul, Matrix.det_mul] at h
  rw [← h] at hG
  exact isUnit_of_mul_isUnit_right hG

theorem UH_inv_left {G u : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hu : u ∈ Formalism.QuantumDeterminants.UH G) :
    (u⁻¹)ᴴ * G = G * u := by
  have hu' : uᴴ * G * u = G := hu
  have hdu := isUnit_det_of_UH hG hu
  have hdh : IsUnit uᴴ.det := by rw [Matrix.det_conjTranspose]; exact hdu.star
  rw [Matrix.conjTranspose_nonsing_inv]
  calc (uᴴ)⁻¹ * G = (uᴴ)⁻¹ * (uᴴ * G * u) := by rw [hu']
    _ = G * u := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (uᴴ)⁻¹, Matrix.nonsing_inv_mul _ hdh, Matrix.one_mul]

theorem UH_inv_right {G u : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hu : u ∈ Formalism.QuantumDeterminants.UH G) :
    G * u⁻¹ = uᴴ * G := by
  have hu' : uᴴ * G * u = G := hu
  have hdu := isUnit_det_of_UH hG hu
  calc G * u⁻¹ = uᴴ * G * u * u⁻¹ := by rw [hu']
    _ = uᴴ * G := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdu, Matrix.mul_one]

theorem inv_mem_UH {G u : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hu : u ∈ Formalism.QuantumDeterminants.UH G) :
    u⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  show (u⁻¹)ᴴ * G * u⁻¹ = G
  rw [UH_inv_left hG hu, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det_of_UH hG hu),
    Matrix.mul_one]

theorem conj_mem_lieG {G u X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hu : u ∈ Formalism.QuantumDeterminants.UH G)
    (hX : X ∈ lieG G) : u⁻¹ * X * u ∈ lieG G := by
  have hX' : Xᴴ * G + G * X = 0 := hX
  have h1 := UH_inv_left hG hu
  have h2 := UH_inv_right hG hu
  show (u⁻¹ * X * u)ᴴ * G + G * (u⁻¹ * X * u) = 0
  have e : (u⁻¹ * X * u)ᴴ * G + G * (u⁻¹ * X * u) = uᴴ * (Xᴴ * G + G * X) * u := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul]
    congr 1
    · simp only [Matrix.mul_assoc]
      rw [h1]
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc G u⁻¹, h2, Matrix.mul_assoc]
  rw [e, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem exp_conj_inv {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit u.det) (Y : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    u⁻¹ * NormedSpace.exp (r • Y) * u = NormedSpace.exp (r • (u⁻¹ * Y * u)) := by
  rw [← Matrix.exp_conj' u (r • Y) ((Matrix.isUnit_iff_isUnit_det u).2 hu)]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem oneProd_succ {d : ℕ} (Y : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (t : Fin (d + 1) → ℝ) :
    oneProd Y t = NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) := by
  simp only [oneProd, List.ofFn_succ, List.prod_cons]

theorem oneProd_conj {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit u.det) :
    ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ),
      u⁻¹ * oneProd Y t * u = oneProd (fun i => u⁻¹ * Y i * u) t := by
  intro d
  induction d with
  | zero =>
    intro Y t
    simp [oneProd, Matrix.nonsing_inv_mul _ hu]
  | succ d ih =>
    intro Y t
    have e := ih (fun i => Y i.succ) (fun i => t i.succ)
    rw [oneProd_succ, oneProd_succ, ← e, ← exp_conj_inv hu]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]

theorem oneProd_mul {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit u.det) {d : ℕ}
    (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ) :
    oneProd Y t * u = u * oneProd (fun i => u⁻¹ * Y i * u) t := by
  rw [← oneProd_conj hu Y t, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mul]

theorem oneProd_append {d d' : ℕ} (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (Y : Fin d' → Matrix (Fin n) (Fin n) ℂ)
    (t : Fin d → ℝ) (s : Fin d' → ℝ) :
    oneProd (Fin.append X Y) (Fin.append t s) = oneProd X t * oneProd Y s := by
  have e : (fun i => NormedSpace.exp (Fin.append t s i • Fin.append X Y i)) =
      Fin.append (fun i => NormedSpace.exp (t i • X i)) (fun j => NormedSpace.exp (s j • Y j)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]
  simp only [oneProd]
  rw [e, List.ofFn_fin_append, List.prod_append]

def appL (d d' : ℕ) : (Fin d → ℝ) →L[ℝ] (Fin (d + d') → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun t => Fin.append t 0
      map_add' := fun a b => by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      map_smul' := fun c a => by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp }

theorem append_eq_appL {d d' : ℕ} (t : Fin d → ℝ) (s : Fin d' → ℝ) :
    Fin.append t s = appL d d' t + Fin.append (0 : Fin d → ℝ) s := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [appL]
  · simp [appL]

end Formalism.IndefR.Tow.SobPf.Avg

end
