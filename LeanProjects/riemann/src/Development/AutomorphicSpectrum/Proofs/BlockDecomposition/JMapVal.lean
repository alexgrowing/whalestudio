import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

noncomputable section

open Matrix PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.RgEis.Cover

variable {R S : Type} [CommRing R] [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι]

def sc (a : Rˣ) : GL (ι ⊕ ι) R := Units.map (Matrix.scalar (ι ⊕ ι) : R →+* _).toMonoidHom a

theorem sc_val (a : Rˣ) (G : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    ((sc a : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * G = (a : R) • G := by
  show Matrix.scalar (ι ⊕ ι) (a : R) * G = (a : R) • G
  rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]

theorem sc_comm (a : Rˣ) (g : GL (ι ⊕ ι) R) : sc a * g = g * sc a := by
  apply Units.ext
  show Matrix.scalar (ι ⊕ ι) (a : R) * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
    (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * Matrix.scalar (ι ⊕ ι) (a : R)
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, ← Matrix.smul_eq_mul_diagonal]

def jMap (D : GL (ι ⊕ ι) R) (ν : S →+* R) : Rˣ × GL (ι ⊕ ι) S →* GL (ι ⊕ ι) R where
  toFun x := sc x.1 * (D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D)
  map_one' := by
    have : (sc (1 : Rˣ) : GL (ι ⊕ ι) R) = 1 := by simp [sc]
    simp [this]
  map_mul' x y := by
    have h : (sc (x.1 * y.1) : GL (ι ⊕ ι) R) = sc x.1 * sc y.1 := by simp [sc]
    simp only [Prod.fst_mul, Prod.snd_mul, h, map_mul]
    rw [mul_assoc (sc x.1) _ (sc y.1 * _), ← mul_assoc _ (sc y.1), ← sc_comm y.1 (D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D)]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem J_apply (e : ℤˣ) (i : ι) (hi : ∀ x : ι, x = i) (G G' : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (x y : ι ⊕ ι) :
    (Gᵀ * Ad.J R e ι * G') x y =
      G (Sum.inl i) x * G' (Sum.inr i) y + ((e : ℤ) : R) * G (Sum.inr i) x * G' (Sum.inl i) y := by
  have hs : ∀ f : ι → R, ∑ z, f z = f i := fun f =>
    Fintype.sum_eq_single i (fun z hz => (hz (hi z)).elim)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, hs, Matrix.transpose_apply,
    PositivityTheory.RgEis.Ad.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq, Matrix.smul_apply,
    Matrix.zero_apply, smul_eq_mul]
  ring

theorem det_two (i : ι) (hi : ∀ x : ι, x = i) (N : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    N.det = N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
      N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i) := by
  let e : Fin 2 ≃ ι ⊕ ι :=
    { toFun := ![Sum.inl i, Sum.inr i]
      invFun := Sum.elim (fun _ => 0) (fun _ => 1)
      left_inv := fun x => by fin_cases x <;> rfl
      right_inv := fun x => by
        rcases x with x | x <;> (have h := hi x; subst h; rfl) }
  rw [← Matrix.det_submatrix_equiv_self e N, Matrix.det_fin_two]
  rfl

theorem mem_aux (σ : R →+* R) (e : ℤˣ) (i : ι) (hi : ∀ x : ι, x = i) (a d d' : R)
    (N : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (hN : ∀ x y, σ (N x y) = N x y) (hd : d * d' = 1)
    (hσ : σ d = -(((e : ℤ) : R) * d)) (ha : a * σ a * N.det = 1) :
    (a • (Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d') * N *
        Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d)))ᵀ * Ad.J R e ι *
      (a • (Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d') * N *
        Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d))).map σ = Ad.J R e ι := by
  have he2 : ((e : ℤ) : R) * ((e : ℤ) : R) = 1 := by
    rcases Int.units_eq_one_or e with h | h <;> simp [h]
  have h1 : σ d * σ d' = 1 := by rw [← map_mul, hd, map_one]
  rw [hσ] at h1
  have hσd' : σ d' = -(((e : ℤ) : R) * d') := by
    linear_combination (-(((e : ℤ) : R) * d')) * h1 - (σ d' * ((e : ℤ) : R) ^ 2) * hd - σ d' * he2
  have hdet := GlobalTheory.CompanionTheory.RgEis.Cover.det_two i hi N
  ext x y
  rw [GlobalTheory.CompanionTheory.RgEis.Cover.J_apply e i hi]
  rcases x with x | x <;> rcases y with y | y <;> rw [hi x, hi y] <;>
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
      Sum.elim_inl, Sum.elim_inr, smul_eq_mul, map_mul, map_one, hN, hσ, hσd', one_mul, mul_one,
      PositivityTheory.RgEis.Ad.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply_eq]
  · ring
  · linear_combination (((e : ℤ) : R) ^ 2 * a * σ a * (N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
        N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i))) * hd +
      (a * σ a * (N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
        N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i))) * he2 + ha - (a * σ a) * hdet
  · linear_combination (((e : ℤ) : R) * a * σ a * (N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
        N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i))) * hd +
      ((e : ℤ) : R) * ha - (((e : ℤ) : R) * a * σ a) * hdet
  · ring

theorem jMap_val (D : GL (ι ⊕ ι) R) (ν : S →+* R) (x : Rˣ × GL (ι ⊕ ι) S) :
    ((jMap D ν x : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
      (x.1 : R) • ((D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
  show ((GlobalTheory.CompanionTheory.RgEis.Cover.sc x.1 * (D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D) : GL (ι ⊕ ι) R) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) R) = _
  rw [Units.val_mul, GlobalTheory.CompanionTheory.RgEis.Cover.sc_val]

theorem jEx : JEx := by
  intro F E R _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i hD hi
  obtain ⟨-, -, hfix, -, -, -, -, -, -, -, -, -, hδ, -, -⟩ := hD
  refine ⟨((GlobalTheory.CompanionTheory.RgEis.Cover.jMap (PositivityTheory.RgEis.So.dg ι (Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)) ν).comp
    (PositivityTheory.RgEis.So.cover A ν ι).subtype).codRestrict (PositivityTheory.RgEis.Ad.uSub A ε ι) ?_, ?_⟩
  · rintro ⟨⟨a, g⟩, hx⟩
    have h1 : (a : R) * PositivityTheory.RgEis.Ad.σ A (a : R) * ν (g : Matrix (ι ⊕ ι) (ι ⊕ ι) _).det = 1 :=
      congrArg Units.val ((MonoidHom.mem_ker).1 hx)
    have e1 : ((Matrix.GeneralLinearGroup.map ν g : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).det =
        ν (g : Matrix (ι ⊕ ι) (ι ⊕ ι) _).det := (RingHom.map_det ν _).symm
    have key := GlobalTheory.CompanionTheory.RgEis.Cover.mem_aux (PositivityTheory.RgEis.Ad.σ A) ε i hi (a : R)
      ((Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ : Rˣ) : R)
      (((Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)⁻¹ : Rˣ) : R)
      ((Matrix.GeneralLinearGroup.map ν g : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)
      (fun x y => hfix ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) _) x y)) (Units.mul_inv _) hδ (by rw [e1]; exact h1)
    show ((GlobalTheory.CompanionTheory.RgEis.Cover.jMap (PositivityTheory.RgEis.So.dg ι (Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)) ν (a, g) :
        GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * PositivityTheory.RgEis.Ad.J R ε ι *
      ((GlobalTheory.CompanionTheory.RgEis.Cover.jMap (PositivityTheory.RgEis.So.dg ι (Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)) ν (a, g) :
        GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map (PositivityTheory.RgEis.Ad.σ A) =
      PositivityTheory.RgEis.Ad.J R ε ι
    rw [GlobalTheory.CompanionTheory.RgEis.Cover.jMap_val]
    exact key
  · intro x
    exact GlobalTheory.CompanionTheory.RgEis.Cover.jMap_val _ _ _

end GlobalTheory.CompanionTheory.RgEis.Cover
