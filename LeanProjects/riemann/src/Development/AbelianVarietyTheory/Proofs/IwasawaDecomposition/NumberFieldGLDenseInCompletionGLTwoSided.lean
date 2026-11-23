import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DenseGL

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem approx (x : P.adicCompletion E) (M : ℤ) :
    ∃ e : E, Valued.v (x - algebraMap E (P.adicCompletion E) e) ≤ WithZero.exp (-M) := by
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := E) P
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := E) P
  set c : P.adicCompletion E := algebraMap E (P.adicCompletion E) (π ^ M.toNat) with hc
  have hvc : Valued.v c = WithZero.exp (-(M.toNat : ℤ)) := by
    have hv : ∀ k : E, Valued.v (algebraMap E (P.adicCompletion E) k) = P.valuation E k :=
      fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k
    rw [hc, hv, map_pow, hπ,
      ← WithZero.exp_nsmul]
    congr 1
    simp
  have hc0 : Valued.v c ≠ 0 := by rw [hvc]; exact WithZero.exp_ne_zero
  have hN : {y : P.adicCompletion E | Valued.v (x - y) < Valued.v c} ∈ nhds x := by
    have ho := (Valued.isOpen_ball (P.adicCompletion E) (Valued.v.restrict c)).preimage
      (continuous_const.sub continuous_id : Continuous fun y : P.adicCompletion E => x - y)
    simp only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (x - x) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hc0
  obtain ⟨e, he⟩ := hd.mem_nhds hN
  refine ⟨e, le_of_lt (lt_of_lt_of_le he ?_)⟩
  rw [hvc, WithZero.exp_le_exp]
  have := Int.self_le_toNat M
  omega

theorem bound {n : ℕ} (B : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    ∃ L : ℕ, ∀ r k, Valued.v (B r k) ≤ WithZero.exp (L : ℤ) := by
  obtain ⟨c, hc⟩ := Finite.bddAbove_range (fun p : Fin n × Fin n => Valued.v (B p.1 p.2))
  refine ⟨(WithZero.log (max c 1)).toNat, fun r k => ?_⟩
  have h1 : Valued.v (B r k) ≤ max c 1 := (hc ⟨(r, k), rfl⟩).trans (le_max_left _ _)
  have h0 : max c 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  refine h1.trans ?_
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp, WithZero.log_exp]
  exact Int.self_le_toNat _

end GlobalTheory.DenseGL

namespace GlobalTheory.DenseGL

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

def smallIdeal : Ideal (P.adicCompletionIntegers E) where
  carrier := {x | Valued.v (x : P.adicCompletion E) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subring.coe_add] at *
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    have hc : Valued.v (c : P.adicCompletion E) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 c.2
    rw [show ((c * x : P.adicCompletionIntegers E) : P.adicCompletion E) = c * x from rfl, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx

theorem one_add_small {n : ℕ} (X : Matrix (Fin n) (Fin n) (P.adicCompletion E))
    (hX : ∀ r s, Valued.v (X r s) < 1) :
    Valued.v (1 + X).det = 1 ∧ ∀ r s, Valued.v ((1 + X)⁻¹ r s) ≤ 1 := by
  set O := P.adicCompletionIntegers E
  have hmem : ∀ r s, X r s ∈ O := fun r s =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hX r s).le
  let X' : Matrix (Fin n) (Fin n) O := fun r s => ⟨X r s, hmem r s⟩
  have hmap : O.subtype.mapMatrix (1 + X') = 1 + X := by
    rw [map_add, map_one]; rfl
  have hq : (Ideal.Quotient.mk (smallIdeal P)).mapMatrix (1 + X') = 1 := by
    rw [map_add, map_one, add_eq_left]
    ext r s
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hX r s)
  have hd : (1 + X').det - 1 ∈ smallIdeal P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, hq, Matrix.det_one, map_one,
      sub_self]
  have hdet : Valued.v (1 + X).det = 1 := by
    rw [← hmap, ← RingHom.map_det]
    have h1 : (O.subtype (1 + X').det) = 1 + (((1 + X').det - 1 : O) : P.adicCompletion E) := by
      simp [O]
    rw [h1]
    exact Valuation.map_one_add_of_lt _ hd
  refine ⟨hdet, fun r s => ?_⟩
  have hdet0 : (1 + X).det ≠ 0 := fun h => by rw [h, map_zero] at hdet; exact zero_ne_one hdet
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hdet,
    inv_one, one_mul, ← hmap, ← RingHom.map_adjugate]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((1 + X').adjugate r s).2

end GlobalTheory.DenseGL

namespace GlobalTheory.DenseGL

theorem entry_le {n : ℕ} {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (B C : Matrix (Fin n) (Fin n) K)
    (a b : WithZero (Multiplicative ℤ)) (hB : ∀ r k, Valued.v (B r k) ≤ a) (hC : ∀ k s, Valued.v (C k s) ≤ b) (r s : Fin n) :
    Valued.v ((B * C) r s) ≤ a * b := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hB r k) (hC k s)

theorem dense_two_sided : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (A : GL (Fin n) (P.adicCompletion E)), ∃ γ : GL (Fin n) E, ∀ r s, Valued.v (((A⁻¹).1 * γ.1.map (algebraMap E (P.adicCompletion E)) - 1) r s) ≤ WithZero.exp (-(N : ℤ)) ∧ Valued.v (((γ⁻¹).1.map (algebraMap E (P.adicCompletion E)) * A.1 - 1) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  intro E _ _ P n N A
  set f := algebraMap E (P.adicCompletion E)
  set B := (A⁻¹).1 with hBdef
  have hBA : B * A.1 = 1 := Units.inv_mul A
  obtain ⟨L, hL⟩ := bound P B
  choose C hC using fun r s => approx P (A.1 r s) ((N : ℤ) + 1 + L)
  let Cm : Matrix (Fin n) (Fin n) E := Matrix.of C
  set C' := Cm.map f with hC'
  set X := B * C' - 1 with hXdef
  have hXe : X = B * (C' - A.1) := by rw [Matrix.mul_sub, hBA]
  have hsmall : ∀ r s, Valued.v (X r s) ≤ WithZero.exp (-((N : ℤ) + 1)) := by
    intro r s
    rw [hXe]
    refine (entry_le B (C' - A.1) _ (WithZero.exp (-((N : ℤ) + 1 + L))) hL (fun k s => ?_) r s).trans (le_of_eq ?_)
    · show Valued.v (f (C k s) - A.1 k s) ≤ _
      rw [Valuation.map_sub_swap]
      exact hC k s
    · rw [← WithZero.exp_add]; congr 1; ring
  have hN1 : WithZero.exp (-((N : ℤ) + 1)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hNN : WithZero.exp (-((N : ℤ) + 1)) ≤ WithZero.exp (-(N : ℤ)) := by
    rw [WithZero.exp_le_exp]; omega
  have hX1 : ∀ r s, Valued.v (X r s) < 1 := fun r s => (hsmall r s).trans_lt hN1
  obtain ⟨hdet, hint⟩ := one_add_small P X hX1
  have hY : 1 + X = B * C' := by rw [hXdef]; abel
  have hCdet : Cm.det ≠ 0 := by
    intro h0
    have : (1 + X).det = 0 := by
      rw [hY, Matrix.det_mul, hC', ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero,
        mul_zero]
    rw [this, map_zero] at hdet
    exact zero_ne_one hdet
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Cm hCdet, fun r s => ⟨?_, ?_⟩⟩
  · exact (hsmall r s).trans hNN
  · set γ := Matrix.GeneralLinearGroup.mkOfDetNeZero Cm hCdet
    have hγ : γ.1 = Cm := rfl
    set D := (γ⁻¹).1.map f
    have hCD : C' * D = 1 := by
      rw [hC', ← hγ, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]
    have hYZ : (1 + X) * (D * A.1) = 1 := by
      rw [hY, Matrix.mul_assoc, ← Matrix.mul_assoc C', hCD, Matrix.one_mul, hBA]
    have hZ : D * A.1 = (1 + X)⁻¹ := (Matrix.inv_eq_right_inv hYZ).symm
    have hZY : (D * A.1) * (1 + X) = 1 := by
      rw [hZ]; exact Matrix.nonsing_inv_mul _ (by
        refine isUnit_iff_ne_zero.2 fun h => ?_; rw [h, map_zero] at hdet; exact zero_ne_one hdet)
    have hdiff : D * A.1 - 1 = -((D * A.1) * X) := by
      rw [Matrix.mul_add, Matrix.mul_one] at hZY
      rw [← hZY]; abel
    rw [hdiff, Matrix.neg_apply, Valuation.map_neg]
    refine (entry_le _ X 1 _ (by rw [hZ]; exact hint) hsmall r s).trans ?_
    rw [one_mul]; exact hNN

end GlobalTheory.DenseGL
