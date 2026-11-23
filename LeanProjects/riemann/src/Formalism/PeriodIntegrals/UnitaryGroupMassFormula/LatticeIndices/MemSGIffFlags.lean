import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CardNuGZmod

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni isUpUni_inv isUpUni_det)

variable {A : Type} [CommRing A] {r k : ℕ}

def zI : Idx r k := Sum.inr (Sum.inl (Sum.inr ()))

def wI (i : Fin k) : Idx r k := Sum.inr (Sum.inl (Sum.inl i))

def ColC (m : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsUpUni (b11 m) ∧ b21 m = 0 ∧ b31 m = 0 ∧ (∀ i, m (wI i) zI = 0) ∧ m zI zI = 1 ∧
    ∀ j, m (Sum.inr (Sum.inr j)) zI = 0

def RowC (m : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsUpUni (b33 m) ∧ b31 m = 0 ∧ b32 m = 0 ∧ (∀ i, m zI (wI i) = 0) ∧ m zI zI = 1 ∧
    ∀ j, m zI (Sum.inl j) = 0

theorem det_shape {x : Matrix (Idx r k) (Idx r k) A} (h11 : IsUpUni (b11 x)) (h33 : IsUpUni (b33 x))
    (h21 : b21 x = 0) (h31 : b31 x = 0) (h32 : b32 x = 0) (h : Matrix (Fin k) (Fin k) A)
    (h22 : b22 x = midEmb h) : x.det = h.det := by
  have e1 : x.toBlocks₂₁ = 0 := by
    ext (i | i) j
    · exact congrFun (congrFun h21 i) j
    · exact congrFun (congrFun h31 i) j
  have e2 : x.toBlocks₂₂.toBlocks₂₁ = 0 := by
    ext i j
    exact congrFun (congrFun h32 i) j
  have d1 : x.toBlocks₁₁.det = 1 := isUpUni_det _ h11
  have d3 : x.toBlocks₂₂.toBlocks₂₂.det = 1 := isUpUni_det _ h33
  have d2 : x.toBlocks₂₂.toBlocks₁₁ = midEmb h := h22
  rw [← Matrix.fromBlocks_toBlocks x, e1, Matrix.det_fromBlocks_zero₂₁, d1, one_mul,
    ← Matrix.fromBlocks_toBlocks x.toBlocks₂₂, e2, Matrix.det_fromBlocks_zero₂₁, d3, mul_one, d2,
    midEmb, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem par_iff_flags (x y : Matrix (Idx r k) (Idx r k) A) (hxy : x * y = 1) (hyx : y * x = 1) :
    Par (fun h => IsUnit h.det) x ↔ ColC x ∧ RowC y := by
  constructor
  · intro hx
    have hy : Par (fun h : Matrix (Fin k) (Fin k) A => IsUnit h.det) y := par_rinv gpUnit hx hxy
    obtain ⟨h11, -, h21, h31, h32, h, -, h22⟩ := hx
    obtain ⟨-, g33, g21, g31, g32, g, -, g22⟩ := hy
    refine ⟨⟨h11, h21, h31, fun i => ?_, ?_, fun j => ?_⟩, ⟨g33, g31, g32, fun i => ?_, ?_, fun j => ?_⟩⟩
    · simpa [b22, midEmb, wI, zI] using congrFun (congrFun h22 (Sum.inl i)) (Sum.inr ())
    · simpa [b22, midEmb, zI] using congrFun (congrFun h22 (Sum.inr ())) (Sum.inr ())
    · simpa [b32, zI] using congrFun (congrFun h32 j) (Sum.inr ())
    · simpa [b22, midEmb, wI, zI] using congrFun (congrFun g22 (Sum.inr ())) (Sum.inl i)
    · simpa [b22, midEmb, zI] using congrFun (congrFun g22 (Sum.inr ())) (Sum.inr ())
    · simpa [b21, zI] using congrFun (congrFun g21 (Sum.inr ())) j
  · rintro ⟨⟨h11, h21, h31, hwz, hzz, hfz⟩, ⟨g33, g31, g32, gzw, gzz, gze⟩⟩

    set B := b33 y with hB
    have hBu : IsUnit B.det := by rw [isUpUni_det _ g33]; exact isUnit_one
    let R : Matrix (Fin r) (Idx r k) A := Matrix.of fun j c => x (Sum.inr (Sum.inr j)) c
    let E : Matrix (Fin r) (Idx r k) A :=
      Matrix.of fun j c => (1 : Matrix (Idx r k) (Idx r k) A) (Sum.inr (Sum.inr j)) c
    have z1 : ∀ j a, y (Sum.inr (Sum.inr j)) (Sum.inl a) = 0 := fun j a => congrFun (congrFun g31 j) a
    have z2 : ∀ j m, y (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inl m)) = 0 :=
      fun j m => congrFun (congrFun g32 j) m
    have key : B * R = E := by
      ext j c
      rw [show E j c = (y * x) (Sum.inr (Sum.inr j)) c by rw [hyx]; rfl, Matrix.mul_apply (M := y) (N := x),
        Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp [z1, z2, B, R, b33, Matrix.mul_apply]
    have hRE : R = B⁻¹ * E := by rw [← key, Matrix.nonsing_inv_mul_cancel_left _ _ hBu]
    have fw : ∀ j i, x (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inl (Sum.inl i))) = 0 := by
      intro j i
      have := congrFun (congrFun hRE j) (Sum.inr (Sum.inl (Sum.inl i)))
      simpa [R, E, Matrix.mul_apply, Matrix.one_apply] using this
    have hb33 : b33 x = B⁻¹ := by
      ext j j'
      have := congrFun (congrFun hRE j) (Sum.inr (Sum.inr j'))
      simpa [R, E, b33, Matrix.mul_apply, Matrix.one_apply] using this
    have hb32 : b32 x = 0 := by
      ext j (i | u)
      · exact fw j i
      · exact hfz j

    have gze' : ∀ a, y (Sum.inr (Sum.inl (Sum.inr ()))) (Sum.inl a) = 0 := gze
    have gzw' : ∀ i, y (Sum.inr (Sum.inl (Sum.inr ()))) (Sum.inr (Sum.inl (Sum.inl i))) = 0 := gzw
    have gzz' : y (Sum.inr (Sum.inl (Sum.inr ()))) (Sum.inr (Sum.inl (Sum.inr ()))) = 1 := gzz
    have zw : ∀ i, x (Sum.inr (Sum.inl (Sum.inr ()))) (Sum.inr (Sum.inl (Sum.inl i))) = 0 := by
      intro i
      have := congrFun (congrFun hyx (Sum.inr (Sum.inl (Sum.inr ())))) (Sum.inr (Sum.inl (Sum.inl i)))
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at this
      simpa [gze', gzw', gzz', fw, Matrix.one_apply] using this
    let h : Matrix (Fin k) (Fin k) A := Matrix.of fun i j => x (wI i) (wI j)
    have hb22 : b22 x = midEmb h := by
      ext (i | u) (i' | u')
      · simp [b22, midEmb, h, wI]
      · simpa [b22, midEmb, wI, zI] using hwz i
      · simpa [b22, midEmb] using zw i'
      · simpa [b22, midEmb, zI] using hzz
    have hb33' : IsUpUni (b33 x) := by rw [hb33]; exact isUpUni_inv _ g33
    refine ⟨h11, hb33', h21, h31, hb32, h, ?_, hb22⟩
    show IsUnit h.det
    rw [← det_shape h11 hb33' h21 h31 hb32 h hb22]
    exact Matrix.isUnit_det_of_right_inverse hxy

theorem mem_sG_iff_flags (g : GL (Idx r k) A) :
    g ∈ sG A r k ↔ ColC (g : Matrix (Idx r k) (Idx r k) A) ∧ RowC ((g⁻¹ : GL (Idx r k) A) : Matrix (Idx r k) (Idx r k) A) :=
  par_iff_flags _ _ (Units.mul_inv g) (Units.inv_mul g)

end MassDataIdxStIm
