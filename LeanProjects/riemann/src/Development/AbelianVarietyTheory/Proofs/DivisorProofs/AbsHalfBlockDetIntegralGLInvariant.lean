import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.AbsHalfInv

theorem v_det_KGL {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w n) : Valued.v (k.val.det) = 1 := by
  obtain ⟨y, rfl⟩ := hk
  have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  obtain ⟨u, hu⟩ := hu
  have hdet : (Formalism.UG.bc (Ov E w).subtype y).val.det = ((u : Ov E w) : w.adicCompletion E) := by
    rw [hu]
    change (y.val.map (Ov E w).subtype).det = _
    exact (RingHom.map_det (Ov E w).subtype y.val).symm
  rw [hdet]
  have h1 : Valued.v ((u : Ov E w) : w.adicCompletion E) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (u : Ov E w).2
  have h2 : Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2
  have h3 : Valued.v ((u : Ov E w) : w.adicCompletion E) *
      Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]
  by_contra hne
  have hlt := lt_of_le_of_ne h1 hne
  have : Valued.v ((u : Ov E w) : w.adicCompletion E) *
      Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

theorem v_det_mul_left {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k m : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w n) : Valued.v ((k * m).val.det) = Valued.v m.val.det := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_det_KGL hk, one_mul]

theorem v_det_mul_right {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k m : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w n) : Valued.v ((m * k).val.det) = Valued.v m.val.det := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_det_KGL hk, mul_one]

theorem absHalf_congr {E : Type} [Field E] [NumberField E] {w : Pl E} {x y : w.adicCompletion E}
    (h : Valued.v x = Valued.v y) : absHalf w x = absHalf w y := by
  have : ordL x = ordL y := by unfold ordL; simp only [h]
  unfold absHalf
  rw [this]

end GlobalTheory.BCT.AbsHalfInv

open GlobalTheory.BCT.AbsHalfInv in
theorem GlobalTheory.BCT.absHalf_blockDet_KGL_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m k : GLw a w × GLw b w),
    k.1 ∈ GlobalTheory.LFun.KGL w a → k.2 ∈ GlobalTheory.LFun.KGL w b →
    absHalf w ((k * m).1.val.det ^ b / (k * m).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) ∧
      absHalf w ((m * k).1.val.det ^ b / (m * k).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
  intro E _ _ _ a b w m k h1 h2
  refine ⟨absHalf_congr ?_, absHalf_congr ?_⟩
  · rw [map_div₀, map_div₀, map_pow, map_pow, map_pow, map_pow, Prod.fst_mul, Prod.snd_mul,
      v_det_mul_left h1, v_det_mul_left h2]
  · rw [map_div₀, map_div₀, map_pow, map_pow, map_pow, map_pow, Prod.fst_mul, Prod.snd_mul,
      v_det_mul_right h1, v_det_mul_right h2]
