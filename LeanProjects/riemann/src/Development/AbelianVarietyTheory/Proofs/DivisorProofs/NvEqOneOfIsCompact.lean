import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

noncomputable section

namespace GlobalTheory.LKLoc.GLOneUnit

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

def nv : GL (Fin 1) (Kn p K r) →* ℝ where
  toFun g := ‖((((GeneralLinearGroup.det g : (Kn p K r)ˣ) : Kn p K r) : PadicAlgCl p))‖
  map_one' := by simp
  map_mul' a b := by simp [norm_mul]

theorem nv_apply (g : GL (Fin 1) (Kn p K r)) :
    nv p K r g = ‖(((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p)‖ := by
  show ‖((((GeneralLinearGroup.det g : (Kn p K r)ˣ) : Kn p K r) : PadicAlgCl p))‖ = _
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

theorem nv_pos (g : GL (Fin 1) (Kn p K r)) : 0 < nv p K r g := by
  show 0 < ‖((((GeneralLinearGroup.det g : (Kn p K r)ˣ) : Kn p K r) : PadicAlgCl p))‖
  refine norm_pos_iff.2 fun h => (GeneralLinearGroup.det g).ne_zero ?_
  exact Subtype.ext h

theorem nv_inv (g : GL (Fin 1) (Kn p K r)) : nv p K r g⁻¹ = (nv p K r g)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])

theorem comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem mem_intR {x : Kn p K r} : x ∈ intR p K r ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 :=
  mem_Obar_iff

theorem mem_Kint_of_nv (g : GL (Fin 1) (Kn p K r)) (h : nv p K r g = 1) : g ∈ Kint p K 1 r := by
  rw [nv_apply] at h
  have hinv : (((g⁻¹ : GL (Fin 1) (Kn p K r)) : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0) *
      ((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0) = 1 := by
    have := congrArg (fun M : Matrix (Fin 1) (Fin 1) (Kn p K r) => M 0 0) (Units.inv_mul g)
    simpa [Matrix.mul_apply] using this
  have hi : ‖((((g⁻¹ : GL (Fin 1) (Kn p K r)) : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) :
      PadicAlgCl p)‖ = 1 := by
    have := congrArg (fun x : Kn p K r => ‖(x : PadicAlgCl p)‖) hinv
    simpa [norm_mul, h] using this
  have h0 : (((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
  refine ⟨⟨Matrix.of fun _ _ => ⟨_, (mem_intR p K r).2 h.le⟩,
    Matrix.of fun _ _ => ⟨_, (mem_intR p K r).2 hi.le⟩, ?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i; fin_cases j
    simp [Matrix.mul_apply, h0]
  · ext i j; fin_cases i; fin_cases j
    simp [Matrix.mul_apply, h0]
  · apply GeneralLinearGroup.ext
    intro i j
    fin_cases i; fin_cases j
    rfl

theorem sig_eq_of_mem (g : GL (Fin 1) (Kn p K r))
    (hg : (((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) ∈ K) :
    sig p K 1 r g = g := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i; fin_cases j
  apply Subtype.ext
  exact (frobK p K).commutes ⟨_, hg⟩

theorem mem_twCent_of_mem (δ g : GL (Fin 1) (Kn p K r))
    (hg : (((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) ∈ K) :
    g ∈ GlobalTheory.BCT.twCent (sig p K 1 r) δ := by
  show g * δ = δ * sig p K 1 r g
  rw [sig_eq_of_mem p K r g hg, comm]

theorem exists_decomp (hK : FiniteDimensional ℚ_[p] K) (hr : 0 < r) (δ x : GL (Fin 1) (Kn p K r)) :
    ∃ t ∈ GlobalTheory.BCT.twCent (sig p K 1 r) δ, ∃ k ∈ Kint p K 1 r, x = t * k := by
  obtain ⟨y, hy, hxy⟩ := norm_Kn p K hK hr ((x : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0).2
  have hxy' : nv p K r x = ‖y‖ := by rw [nv_apply]; exact hxy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hxy'
    exact (nv_pos p K r x).ne' hxy'
  let u : (Kn p K r)ˣ := Units.mk0 ⟨y, le_Kn p K r hy⟩ (fun h => hy0 (congrArg Subtype.val h))
  let t : GL (Fin 1) (Kn p K r) :=
    Units.map (Matrix.scalar (Fin 1) : Kn p K r →+* Matrix (Fin 1) (Fin 1) (Kn p K r)).toMonoidHom u
  have ht00 : (((t : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) = y := by
    simp [t, u]
  refine ⟨t, mem_twCent_of_mem p K r δ t (by rw [ht00]; exact hy), t⁻¹ * x,
    mem_Kint_of_nv p K r _ ?_, (mul_inv_cancel_left t x).symm⟩
  rw [map_mul, nv_inv, hxy', nv_apply, ht00]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hy0)

end GlobalTheory.LKLoc.GLOneUnit

namespace GlobalTheory.LKLoc.GLOneUnit

end GlobalTheory.LKLoc.GLOneUnit
