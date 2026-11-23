import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

namespace UpperTheory.V.T.UnipCard

private def upMat (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0

private theorem upMat_lower (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) (i j : Fin n) (h : j < i) :
    upMat R n f i j = 0 := by
  simp [upMat, not_lt.2 h.le, h.ne']

private theorem upMat_diag (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) (i : Fin n) :
    upMat R n f i i = 1 := by
  simp [upMat]

private theorem upMat_det (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) : (upMat R n f).det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => upMat_lower R n f i j h)]
  simp [upMat_diag]

private noncomputable def upGL (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) : GL (Fin n) R :=
  Matrix.nonsingInvUnit (upMat R n f) (by rw [upMat_det]; exact isUnit_one)

private theorem upGL_val (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) :
    (upGL R n f : Matrix (Fin n) (Fin n) R) = upMat R n f := rfl

private noncomputable def unipEquiv (R : Type) [CommRing R] (n : ℕ) :
    unipB R (Fin n) ≃ ({p : Fin n × Fin n // p.1 < p.2} → R) where
  toFun g := fun p => ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2
  invFun f := ⟨upGL R n f, (mem_unipB R).2 ⟨fun i j h => by
      rw [upGL_val]; exact upMat_lower R n f i j h, fun i => by
      rw [upGL_val]; exact upMat_diag R n f i⟩⟩
  left_inv g := by
    obtain ⟨hl, hd⟩ := (mem_unipB R).1 g.2
    apply Subtype.ext
    apply Units.ext
    funext i j
    show ((upGL R n (fun p => ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2) : GL (Fin n) R) :
      Matrix (Fin n) (Fin n) R) i j = _
    rw [upGL_val]
    rcases lt_trichotomy i j with h | h | h
    · simp [upMat, h]
    · subst h
      simp [upMat, hd]
    · have h1 : ¬ i < j := not_lt.2 h.le
      have h2 : i ≠ j := h.ne'
      simp [upMat, h1, h2, hl i j h]
  right_inv f := by
    funext p
    show upMat R n f p.1.1 p.1.2 = f p
    have h : p.1.1 < p.1.2 := p.2
    simp [upMat, h]

end UpperTheory.V.T.UnipCard

theorem UpperTheory.card_unipotent_upper_eq_pow :
    ∀ (R : Type) [CommRing R] [Finite R] (n : ℕ), ∃ j : ℕ, Nat.card (unipB R (Fin n)) = Nat.card R ^ j := by
  intro R _ _ n
  refine ⟨Nat.card {p : Fin n × Fin n // p.1 < p.2}, ?_⟩
  rw [Nat.card_congr (UpperTheory.V.T.UnipCard.unipEquiv R n), Nat.card_fun]
