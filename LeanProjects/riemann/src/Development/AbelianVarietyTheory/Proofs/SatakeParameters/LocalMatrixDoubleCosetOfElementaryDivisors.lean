import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralFiniteAdelesTensorIffLocalOrders

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceDiv

section Abstract

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (O : Subring R)

theorem single_mem (j i : n) : (Pi.single j (1 : R) : n → R) i ∈ O := by
  by_cases h : i = j
  · subst h; simpa using O.one_mem
  · simpa [Pi.single_eq_of_ne h] using O.zero_mem

theorem exists_factor (P Q : Matrix n n R)
    (H : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ P.mulVec y = Q.mulVec z) :
    ∃ M : Matrix n n O, P = Q * M.map O.subtype := by
  choose z hz1 hz2 using fun j => H (Pi.single j 1) (single_mem O j)
  refine ⟨Matrix.of fun i j => ⟨z j i, hz1 j i⟩, ?_⟩
  ext i j
  have := congrFun (hz2 j) i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [this]
  rfl

theorem mem_range_of_mul_eq_one (M N : Matrix n n O) (h : M.map O.subtype * N.map O.subtype = 1) :
    ∃ k ∈ (Formalism.UG.bc (n := n) O.subtype).range, k.1 = M.map O.subtype := by
  have h1 : M * N = 1 := by
    apply Matrix.map_injective O.subtype_injective
    simp only [Matrix.map_mul]
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨_, ⟨⟨M, N, h1, mul_eq_one_comm.1 h1⟩, rfl⟩, rfl⟩

theorem double_coset (B m T T' : Matrix n n R) (hT : T' * T = 1)
    (h1 : ∀ z : n → R, (∀ i, z i ∈ O) → ∀ i, B.mulVec z i ∈ O)
    (h2 : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ y = B.mulVec z)
    (h3 : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ m.mulVec y = (B * T).mulVec z)
    (h4 : ∀ z : n → R, (∀ i, z i ∈ O) → ∃ y : n → R, (∀ i, y i ∈ O) ∧ m.mulVec y = (B * T).mulVec z) :
    ∃ k₁ ∈ (Formalism.UG.bc (n := n) O.subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := n) O.subtype).range,
      m = k₁.1 * T * k₂.1 := by
  obtain ⟨B0, hB0⟩ := exists_factor O B 1 fun y hy => ⟨_, h1 y hy, by rw [Matrix.one_mulVec]⟩
  rw [Matrix.one_mul] at hB0
  obtain ⟨C, hC⟩ := exists_factor O 1 B fun y hy => by rw [Matrix.one_mulVec]; exact h2 y hy
  obtain ⟨M, hM⟩ := exists_factor O m (B * T) h3
  obtain ⟨N, hN⟩ := exists_factor O (B * T) m fun z hz => (h4 z hz).imp fun y hy => ⟨hy.1, hy.2.symm⟩
  have hCB : C.map O.subtype * B = 1 := mul_eq_one_comm.1 hC.symm
  have hinv : T' * C.map O.subtype * (B * T) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ B, hCB, Matrix.one_mul, hT]
  have hMN : M.map O.subtype * N.map O.subtype = 1 := by
    have e : B * T * (M.map O.subtype * N.map O.subtype) = B * T := by
      rw [← Matrix.mul_assoc, ← hM, ← hN]
    calc _ = T' * C.map O.subtype * (B * T) * (M.map O.subtype * N.map O.subtype) := by
          rw [hinv, Matrix.one_mul]
      _ = 1 := by rw [Matrix.mul_assoc, e, hinv]
  obtain ⟨k₁, hk₁, e₁⟩ := mem_range_of_mul_eq_one O B0 C (by rw [← hB0, ← hC])
  obtain ⟨k₂, hk₂, e₂⟩ := mem_range_of_mul_eq_one O M N hMN
  exact ⟨k₁, hk₁, k₂, hk₂, by rw [e₁, e₂, ← hB0, hM]⟩

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sgT_mem_intA (v : HeightOneSpectrum (𝓞 F)) {y : Fv F v ⊗[F] E} (hy : y ∈ ordAt E v) :
    sgT E v y ∈ intA F E := by
  refine (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).2 fun w => ?_
  by_cases h : w = v
  · subst h; rwa [evF_sgT_self]
  · rw [evF_sgT_ne h]; exact zero_mem _

theorem sgT_mem_lamHat [StarRing E] (V : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    {y : Fin V.rank → Fv F v ⊗[F] E} (hy : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v) :
    (fun i => sgT E v (y i)) ∈ lamHat F V := by
  refine (mem_lamHat_iff V _).2 fun w => ?_
  by_cases h : w = v
  · subst h; simpa only [evF_sgT_self] using hy
  · simp only [evF_sgT_ne h]; exact zero_mem _

omit [NumberField E] in
theorem evF_mulVec {n : Type} [Fintype n] (v : HeightOneSpectrum (𝓞 F)) {f : Af F ⊗[F] E} (hf : evF E v f = 1)
    (A : Matrix n n (Af F ⊗[F] E)) (z : n → Af F ⊗[F] E) :
    (fun a => evF E v (f * A.mulVec z a)) = (A.map (evF E v)).mulVec fun i => evF E v (z i) := by
  funext a
  rw [map_mul, hf, one_mul, RingHom.map_mulVec]
  rfl

theorem double_coset_of_divG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) (ϖ : E) (d : Fin V.rank → ℤ) (g : HA (AF F) hc.sig V.gram), IsIdemOf E v e → IsFrameAt V v h → ϖ ≠ 0 → DivG hc V e ϖ d g → ∃ k₁ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, (h⁻¹ * locMat hc V v g * h).1 = k₁.1 * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i)) * k₂.1 := by
  intro F E _ _ _ _ _ _ hc V v e h ϖ d g he hh hϖ ⟨B, h1, h2, h3, h4⟩
  have he1 := he.2.1
  have hfr : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (∀ i, y i ∈ ordAt E v) →
      h.1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := fun y hy => by
    refine (hh _).2 ?_
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]; exact hy
  have hback : ∀ y : Fin V.rank → Fv F v ⊗[F] E, h.1.mulVec ((h⁻¹).1.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hback' : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (h⁻¹).1.mulVec (h.1.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have key : ∀ y z : Fin V.rank → Af F ⊗[F] E,
      ((fun a => finP F E e * (finMat hc.sig V.gram g).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a) →
      (locMat hc V v g).1.mulVec (fun i => evF E v (y i)) =
        (B.map (evF E v) * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i))).mulVec fun i => evF E v (z i) := by
    intro y z hyz
    rw [locMat_val, ← evF_mulVec v he1, ← Matrix.mulVec_mulVec]
    have e2 : (Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i))).mulVec (fun i => evF E v (z i)) =
        fun i => evF E v (finP F E (inclR (AF F) (ϖ ^ d i)) * z i) := by
      funext i
      rw [Matrix.mulVec_diagonal, map_mul, evF_finP_incl]
    rw [e2, ← evF_mulVec v he1]
    funext a
    rw [congrFun hyz a]
  refine double_coset (ordAt E v) ((h⁻¹).1 * B.map (evF E v)) _ _
    (Matrix.diagonal fun i => inclR (Fv F v) (ϖ ^ d i)⁻¹) ?_ ?_ ?_ ?_ ?_
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← map_mul, inv_mul_cancel₀ (zpow_ne_zero _ hϖ), map_one]
  · intro z hz
    have := (mem_lamHat_iff V _).1 (h1 (fun i => sgT E v (z i)) fun i => sgT_mem_intA v (hz i)) v
    rw [evF_mulVec v he1] at this
    simp only [evF_sgT_self] at this
    rw [← Matrix.mulVec_mulVec]
    exact (hh _).1 this
  · intro y hy
    obtain ⟨z, hz, e2⟩ := h2 _ (sgT_mem_lamHat V v (hfr y hy))
    refine ⟨fun i => evF E v (z i), fun i => (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).1 (hz i) v, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← evF_mulVec v he1, ← hback' y]
    congr 1; funext a
    rw [← congrFun e2 a, map_mul, he1, one_mul, evF_sgT_self]
  · intro y hy
    obtain ⟨z, hz, e2⟩ := h3 _ (sgT_mem_lamHat V v (hfr y hy))
    refine ⟨fun i => evF E v (z i), fun i => (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).1 (hz i) v, ?_⟩
    have := key _ _ e2
    simp only [evF_sgT_self] at this
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (h⁻¹).1, ← this, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  · intro z hz
    obtain ⟨y, hy, e2⟩ := h4 (fun i => sgT E v (z i)) fun i => sgT_mem_intA v (hz i)
    refine ⟨(h⁻¹).1.mulVec fun i => evF E v (y i), (hh _).1 ((mem_lamHat_iff V _).1 hy v), ?_⟩
    have := key _ _ e2
    simp only [evF_sgT_self] at this
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (h⁻¹).1, ← this, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hback]

end GlobalTheory.PlaceDiv
