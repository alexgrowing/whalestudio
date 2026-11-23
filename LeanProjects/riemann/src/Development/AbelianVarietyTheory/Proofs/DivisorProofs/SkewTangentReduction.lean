import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix GlobalTheory.SUCong

namespace GlobalTheory.SUCongRed

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem red_coe (S : Subring A) (ϖ : A) (s : S) :
    red S ϖ (s : A) = Ideal.Quotient.mk (piIdeal S ϖ) s := by
  unfold red; rw [dif_pos s.2]

theorem inPow_one_iff (S : Subring A) (ϖ : A) (hϖ : ϖ ∈ S) (s : S) :
    InPow S ϖ 1 (s : A) ↔ Ideal.Quotient.mk (piIdeal S ϖ) s = 0 := by
  have hI : piIdeal S ϖ = Ideal.span {(⟨ϖ, hϖ⟩ : S)} := by
    unfold piIdeal; congr 1; ext x; simp [Subtype.ext_iff]
  rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨t, ht, he⟩
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    show t * ϖ = (s : A)
    rw [he, pow_one, mul_comm]
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    have h2 := congrArg Subtype.val hc
    rw [← h2, pow_one, mul_comm]; rfl

end GlobalTheory.SUCongRed

open GlobalTheory.SUCongRed in
theorem GlobalTheory.SUCong.skewTr_eq_reduced {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (τ : Res S ϖ →+* Res S ϖ) :
    ϖ ∈ S → (∀ s ∈ S, σ s ∈ S) → (∀ i j, H i j ∈ S) →
    (∀ a ∈ S, τ (red S ϖ a) = red S ϖ (σ a)) →
    skewTr S σ H ϖ = {Y : Matrix n n (Res S ϖ) | Formalism.UG.cT τ Y * H.map (red S ϖ) +
      H.map (red S ϖ) * Y = 0 ∧ Y.trace = 0} := by
  intro hϖ hσ hH hτ
  set π := Ideal.Quotient.mk (piIdeal S ϖ) with hπ
  let σS : S →+* S := (σ.comp S.subtype).codRestrict S (fun x => hσ x x.2)
  let Hs : Matrix n n S := fun i j => ⟨H i j, hH i j⟩
  have hHs : H = Hs.map S.subtype := by ext i j; rfl
  have hHr : H.map (red S ϖ) = Hs.map π := by
    ext i j; exact red_coe S ϖ (Hs i j)
  have hτS : ∀ s : S, τ (π s) = π (σS s) := by
    intro s
    have := hτ s s.2
    rw [red_coe] at this
    rw [this, ← red_coe]; rfl

  have core : ∀ Xs : Matrix n n S,
      ((∀ i j, InPow S ϖ 1 ((Formalism.UG.cT σ (Xs.map S.subtype) * H + H * Xs.map S.subtype) i j)) ∧
        InPow S ϖ 1 (Xs.map S.subtype).trace) ↔
      (Formalism.UG.cT τ (Xs.map π) * H.map (red S ϖ) + H.map (red S ϖ) * Xs.map π = 0 ∧
        (Xs.map π).trace = 0) := by
    intro Xs
    set Z : Matrix n n S := Formalism.UG.cT σS Xs * Hs + Hs * Xs with hZ
    have e1 : Formalism.UG.cT σ (Xs.map S.subtype) * H + H * Xs.map S.subtype = Z.map S.subtype := by
      have : Z.map S.subtype = S.subtype.mapMatrix Z := rfl
      rw [this, hZ, map_add, map_mul, map_mul, hHs]
      rfl
    have e2 : Formalism.UG.cT τ (Xs.map π) * H.map (red S ϖ) + H.map (red S ϖ) * Xs.map π = Z.map π := by
      have : Z.map π = π.mapMatrix Z := rfl
      rw [this, hZ, map_add, map_mul, map_mul, hHr]
      congr 2
      ext i j
      simp only [Formalism.UG.cT, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply]
      exact hτS (Xs j i)
    have t1 : (Xs.map S.subtype).trace = ((Xs.trace : S) : A) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
      exact (map_sum S.subtype _ _).symm
    have t2 : (Xs.map π).trace = π Xs.trace := by
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
      exact (map_sum π _ _).symm
    rw [e1, e2, t1, t2, inPow_one_iff S ϖ hϖ]
    refine and_congr ?_ Iff.rfl
    constructor
    · intro h; ext i j; exact (inPow_one_iff S ϖ hϖ _).1 (h i j)
    · intro h i j; exact (inPow_one_iff S ϖ hϖ _).2 (congrFun (congrFun h i) j)
  ext Y
  constructor
  · rintro ⟨X, hX, hY, hsk, htr⟩
    let Xs : Matrix n n S := fun i j => ⟨X i j, hX i j⟩
    have hXs : X = Xs.map S.subtype := by ext i j; rfl
    have hYX : Y = Xs.map π := by
      ext i j; rw [hY i j]; exact red_coe S ϖ (Xs i j)
    rw [hXs] at hsk htr
    rw [hYX]
    exact (core Xs).1 ⟨hsk, htr⟩
  · rintro ⟨h1, h2⟩
    choose Xs hXs using fun i j => Ideal.Quotient.mk_surjective (I := piIdeal S ϖ) (Y i j)
    have hYX : Y = (Matrix.of Xs).map π := by ext i j; exact (hXs i j).symm
    rw [hYX] at h1 h2
    obtain ⟨c1, c2⟩ := (core (Matrix.of Xs)).2 ⟨h1, h2⟩
    refine ⟨(Matrix.of Xs).map S.subtype, fun i j => (Xs i j).2, fun i j => ?_, c1, c2⟩
    rw [← hXs i j]; exact (red_coe S ϖ (Xs i j)).symm
