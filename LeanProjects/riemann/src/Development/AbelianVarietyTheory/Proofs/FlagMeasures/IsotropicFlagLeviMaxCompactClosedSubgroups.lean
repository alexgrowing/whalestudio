import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagLeviGroup

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inv_mul (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem inv_keeps {A B : Matrix (Fin n) (Fin n) ℂ} (hBA : B * A = 1) (V : Submodule ℂ (Fin n → ℂ))
    (hA : ∀ y ∈ V, A *ᵥ y ∈ V) : ∀ y ∈ V, B *ᵥ y ∈ V := by
  have hA' : ∀ y ∈ V, Matrix.toLin' A y ∈ V := fun y hy => by simpa using hA y hy
  have hinj : Function.Injective ((Matrix.toLin' A).restrict hA') := by
    intro x y hxy
    have h1 : A *ᵥ (x : Fin n → ℂ) = A *ᵥ (y : Fin n → ℂ) := by
      simpa using congrArg Subtype.val hxy
    have h2 := congrArg (fun z => B *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] at h2
    exact Subtype.ext h2
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  have h1 : A *ᵥ (x : Fin n → ℂ) = y := by
    simpa using congrArg Subtype.val hx
  rw [← h1, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  exact x.2

variable (ε) in

def leviSub {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := flagM ε W
  one_mem' := by
    intro i y hy
    simpa [uMat_one] using hy
  mul_mem' := by
    intro g h hg hh i y hy
    rw [uMat_mul, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg i _ (hh i y hy).1).1, (hh i _ (hg i y hy).2).2⟩
  inv_mem' := by
    intro g hg i y hy
    refine ⟨inv_keeps (uMat_inv_mul g) (W i) (fun z hz => (hg i z hz).1) y hy,
      inv_keeps (A := (uMat g)ᴴ) ?_ (W i) (fun z hz => (hg i z hz).2) y hy⟩
    rw [← Matrix.conjTranspose_mul, uMat_mul_inv, Matrix.conjTranspose_one]

variable (ε) in

def compactSub : Subgroup (Formalism.REAL.UJ ε) where
  carrier := maxK ε
  one_mem' := by
    show (uMat (1 : Formalism.REAL.UJ ε))ᴴ * uMat (1 : Formalism.REAL.UJ ε) = 1
    simp [uMat_one]
  mul_mem' := by
    intro g h hg hh
    have hg' : (uMat g)ᴴ * uMat g = 1 := hg
    have hh' : (uMat h)ᴴ * uMat h = 1 := hh
    show (uMat (g * h))ᴴ * uMat (g * h) = 1
    rw [uMat_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hg',
      Matrix.one_mul, hh']
  inv_mem' := by
    intro g hg
    have hg' : (uMat g)ᴴ * uMat g = 1 := hg
    have h1 : uMat g⁻¹ = (uMat g)ᴴ := by
      calc uMat g⁻¹ = ((uMat g)ᴴ * uMat g) * uMat g⁻¹ := by rw [hg', Matrix.one_mul]
        _ = (uMat g)ᴴ := by rw [Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]
    show (uMat g⁻¹)ᴴ * uMat g⁻¹ = 1
    conv_lhs => enter [1]; rw [h1, Matrix.conjTranspose_conjTranspose]
    exact uMat_mul_inv g

theorem isClosed_flagM {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : IsClosed (flagM ε W) := by
  have h : flagM ε W = ⋂ i, ⋂ y ∈ W i,
      ((fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) ∩
        (fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ))) := by
    ext g
    simp only [flagM, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    rfl
  rw [h]
  refine isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ => ?_
  exact ((W i).closed_of_finiteDimensional.preimage
      (continuous_uMat.matrix_mulVec continuous_const)).inter
    ((W i).closed_of_finiteDimensional.preimage
      (continuous_uMat.matrix_conjTranspose.matrix_mulVec continuous_const))

theorem isClosed_maxK : IsClosed (maxK ε) :=
  isClosed_eq (continuous_uMat.matrix_conjTranspose.matrix_mul continuous_uMat) continuous_const

theorem conj_sub (m u : Formalism.REAL.UJ ε) (y : Fin n → ℂ) :
    uMat (m * u * m⁻¹) *ᵥ y - y = uMat m *ᵥ (uMat u *ᵥ (uMat m⁻¹ *ᵥ y) - uMat m⁻¹ *ᵥ y) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec y (uMat m) (uMat m⁻¹), uMat_mul_inv, Matrix.one_mulVec,
    uMat_mul, uMat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem form_inv (m : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat m⁻¹ *ᵥ y)) = star (uMat m *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * uMat m⁻¹ = ((uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m) * uMat m⁻¹ := by rw [hm]
      _ = _ := by rw [Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem conj_mem_flagN {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) {m u : Formalism.REAL.UJ ε}
    (hm : m ∈ flagM ε W) (hu : u ∈ flagN ε W) : m * u * m⁻¹ ∈ flagN ε W := by
  have hm' : m⁻¹ ∈ flagM ε W := (leviSub ε W).inv_mem hm
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · rw [conj_sub]
    exact (hm _ _ (hu.1 i _ (hm' _ y hy).1)).1
  · rw [conj_sub]
    refine (hm _ _ (hu.2 _ fun x hx => ?_)).1
    rw [form_inv]
    exact hy _ (hm _ x hx).1

theorem levi_compact_subgroups : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)),
    (∃ M : Subgroup (Formalism.REAL.UJ ε), (M : Set (Formalism.REAL.UJ ε)) = flagM ε W) ∧ IsClosed (flagM ε W) ∧
    (∃ K : Subgroup (Formalism.REAL.UJ ε), (K : Set (Formalism.REAL.UJ ε)) = maxK ε) ∧ IsClosed (maxK ε) ∧
    ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W :=
  fun _ ε _ W => ⟨⟨leviSub ε W, rfl⟩, isClosed_flagM W, ⟨compactSub ε, rfl⟩, isClosed_maxK,
    fun _ hm _ hu => conj_mem_flagN W hm hu⟩

end GlobalTheory.FlagLeviGroup
