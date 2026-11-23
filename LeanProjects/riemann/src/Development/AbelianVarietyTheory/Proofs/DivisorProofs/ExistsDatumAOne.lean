import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBotOfIsIntegral

noncomputable section
open NumberField
open scoped TensorProduct ComplexConjugate
open GlobalTheory.Published.LandherrModel GlobalTheory.UPel.HT.Gauss

namespace GlobalTheory.UPel.HT.GaussOne

theorem liO : LinearIndependent ℤ ![(1 : 𝓞 Qi), ζO] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h := congrArg (algebraMap (𝓞 Qi) Qi) hst
  simp at h
  rw [show algebraMap (𝓞 Qi) Qi ζO = ii from coe_ζO] at h
  have h2 := coord_zero (a := s) (b := t) (by push_cast; exact h)
  exact ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩

theorem spanO : ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 Qi), ζO]) := by
  intro x _
  obtain ⟨a, b, rfl⟩ := coordO x
  rw [Submodule.mem_span_range_iff_exists_fun]
  exact ⟨![a, b], by simp [Fin.sum_univ_two, zsmul_eq_mul]⟩

def bO : Module.Basis (Fin 2) ℤ (𝓞 Qi) := Module.Basis.mk liO spanO

theorem bO_zero : bO 0 = 1 := by simp [bO]
theorem bO_one : bO 1 = ζO := by simp [bO]

theorem repr_coord (a b : ℤ) : bO.repr ((a : 𝓞 Qi) + b * ζO) = Finsupp.equivFunOnFinite.symm ![a, b] := by
  have : ((a : 𝓞 Qi) + b * ζO) = a • bO 0 + b • bO 1 := by simp [bO_zero, bO_one, zsmul_eq_mul]
  rw [this, map_add, map_zsmul, map_zsmul, bO.repr_self, bO.repr_self]
  ext i; fin_cases i <;> simp

theorem repr0 (a b : ℤ) : bO.repr ((a : 𝓞 Qi) + b * ζO) 0 = a := by simp [repr_coord]
theorem repr1 (a b : ℤ) : bO.repr ((a : 𝓞 Qi) + b * ζO) 1 = b := by simp [repr_coord]

def barO : 𝓞 Qi ≃+* 𝓞 Qi := (IsCMField.ringOfIntegersComplexConj Qi).toRingEquiv

theorem barO_apply (x : 𝓞 Qi) : barO x = IsCMField.ringOfIntegersComplexConj Qi x := rfl

theorem barO_eq (x : 𝓞 Qi) : ((barO x : 𝓞 Qi) : Qi) = IsCMField.complexConj Qi (x : Qi) := by
  rw [barO_apply, IsCMField.coe_ringOfIntegersComplexConj]

theorem barO_barO (x : 𝓞 Qi) : barO (barO x) = x := by
  ext; rw [barO_eq, barO_eq, IsCMField.complexConj_apply_apply]

theorem barO_ζO : barO ζO = -ζO := cO_ζO

end GlobalTheory.UPel.HT.GaussOne

namespace GlobalTheory.UPel.HT.GaussOne

def EF : LinearMap.BilinForm ℤ (𝓞 Qi) :=
  LinearMap.mk₂ ℤ (fun x y => bO.repr x 1 * bO.repr y 0 - bO.repr x 0 * bO.repr y 1)
    (fun x x' y => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun r x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun r x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)

theorem EF_coord (a b c d : ℤ) : EF ((a : 𝓞 Qi) + b * ζO) ((c : 𝓞 Qi) + d * ζO) = b * c - a * d := by
  simp only [EF, LinearMap.mk₂_apply, repr0, repr1]

theorem mul_coord (a b c d : ℤ) : ((a : 𝓞 Qi) + b * ζO) * ((c : 𝓞 Qi) + d * ζO) =
    ((a * c - b * d : ℤ) : 𝓞 Qi) + ((a * d + b * c : ℤ) : 𝓞 Qi) * ζO := by
  push_cast; linear_combination (b * d : 𝓞 Qi) * ζO_sq

theorem bar_coord (a b : ℤ) : barO ((a : 𝓞 Qi) + b * ζO) = ((a : ℤ) : 𝓞 Qi) + ((-b : ℤ) : 𝓞 Qi) * ζO := by
  simp [barO_ζO]

theorem EF_alt (x : 𝓞 Qi) : EF x x = 0 := by
  obtain ⟨a, b, rfl⟩ := coordO x
  rw [EF_coord]; ring

theorem EF_adj (b x y : 𝓞 Qi) : EF (b * x) y = EF x (barO b * y) := by
  obtain ⟨a, a', rfl⟩ := coordO b
  obtain ⟨c, c', rfl⟩ := coordO x
  obtain ⟨d, d', rfl⟩ := coordO y
  rw [bar_coord, mul_coord, mul_coord, EF_coord, EF_coord]; ring

theorem EF_bO (i j : Fin 2) : EF (bO i) (bO j) = ![![0, -1], ![1, 0]] i j := by
  simp only [EF, LinearMap.mk₂_apply]
  fin_cases i <;> fin_cases j <;> simp [Module.Basis.repr_self, Finsupp.single_apply]

theorem EF_bij : Function.Bijective EF :=
  bijective_of_gram bO EF (by rw [EF_bO]; rfl) (by rw [EF_bO]; rfl) (by rw [EF_bO]; rfl) (by rw [EF_bO]; rfl)

end GlobalTheory.UPel.HT.GaussOne

namespace GlobalTheory.UPel.HT.GaussOne

theorem ζ_mul_coord (c d : ℤ) : ζO * ((c : 𝓞 Qi) + d * ζO) = ((-d : ℤ) : 𝓞 Qi) + ((c : ℤ) : 𝓞 Qi) * ζO := by
  push_cast; linear_combination (d : 𝓞 Qi) * ζO_sq

theorem bO_zero' : bO 0 = ((1 : ℤ) : 𝓞 Qi) + ((0 : ℤ) : 𝓞 Qi) * ζO := by simp [bO_zero]
theorem bO_one' : bO 1 = ((0 : ℤ) : 𝓞 Qi) + ((1 : ℤ) : 𝓞 Qi) * ζO := by simp [bO_one]

theorem EF_ζ_bO (i j : Fin 2) : EF (ζO * bO i) (bO j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, bO_zero', bO_one', ζ_mul_coord, EF_coord] <;> norm_num

theorem EF_ζ (x y : 𝓞 Qi) : EF (ζO * x) (ζO * y) = EF x y := by
  rw [EF_adj, ← mul_assoc, barO_ζO, neg_mul, ζO_sq, neg_neg, one_mul]

theorem trace_mulLeft (a b : ℤ) :
    LinearMap.trace ℤ (𝓞 Qi) (LinearMap.mulLeft ℤ ((a : 𝓞 Qi) + b * ζO)) = 2 * a := by
  rw [LinearMap.trace_eq_matrix_trace ℤ bO, Matrix.trace_fin_two, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, bO_zero', bO_one', mul_coord,
    mul_coord, repr0, repr1]
  ring

def bR : Module.Basis (Fin 2) ℝ (ℝ ⊗[ℤ] 𝓞 Qi) := Algebra.TensorProduct.basis ℝ bO

theorem bR_apply (i : Fin 2) : bR i = 1 ⊗ₜ bO i := Algebra.TensorProduct.basis_apply _ _

def J : ℝ ⊗[ℤ] 𝓞 Qi →ₗ[ℝ] ℝ ⊗[ℤ] 𝓞 Qi := (LinearMap.mulLeft ℤ ζO).baseChange ℝ

theorem A_eq (b : 𝓞 Qi) (A : ℝ ⊗[ℤ] 𝓞 Qi →ₗ[ℝ] ℝ ⊗[ℤ] 𝓞 Qi) (h : ∀ x : 𝓞 Qi, A (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) :
    A = (LinearMap.mulLeft ℤ b).baseChange ℝ :=
  bR.ext fun i => by rw [bR_apply, h, LinearMap.baseChange_tmul, LinearMap.mulLeft_apply, smul_eq_mul]

theorem J_J (x : ℝ ⊗[ℤ] 𝓞 Qi) : J (J x) = -x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp [J, ← mul_assoc, ζO_sq, TensorProduct.tmul_neg]
  | add x y hx hy => rw [map_add, map_add, hx, hy, neg_add]

theorem J_EF (x y : ℝ ⊗[ℤ] 𝓞 Qi) : EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y := by
  have key : (EF.baseChange ℝ).compl₁₂ J J = EF.baseChange ℝ :=
    LinearMap.BilinForm.ext_basis bR fun i j => by
      rw [LinearMap.compl₁₂_apply, bR_apply, bR_apply, J, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, EF_ζ]
  exact LinearMap.congr_fun₂ key x y

theorem J_pos (x : ℝ ⊗[ℤ] 𝓞 Qi) (hx : x ≠ 0) : 0 < EF.baseChange ℝ (J x) x := by
  have hG : ∀ i j, EF.baseChange ℝ (J (bR i)) (bR j) = if i = j then 1 else 0 := by
    intro i j
    rw [bR_apply, bR_apply, J, LinearMap.baseChange_tmul, LinearMap.mulLeft_apply,
      LinearMap.BilinForm.baseChange_tmul, EF_ζ_bO]
    split_ifs <;> simp
  have hx' := bR.sum_repr x
  rw [Fin.sum_univ_two] at hx'
  have hne : ¬ (bR.repr x 0 = 0 ∧ bR.repr x 1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hx
    rw [← hx', h0, h1, zero_smul, zero_smul, add_zero]
  rw [← hx']
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hG]
  simp only [Fin.isValue, ite_true, show ((0 : Fin 2) = 1) = False by decide, show ((1 : Fin 2) = 0) = False by decide,
    ite_false, mul_one, mul_zero, add_zero, zero_add]
  by_cases h0 : bR.repr x 0 = 0
  · have h1 : bR.repr x 1 ≠ 0 := fun h1 => hne ⟨h0, h1⟩
    nlinarith [mul_self_pos.2 h1, h0]
  · nlinarith [mul_self_pos.2 h0, mul_self_nonneg (bR.repr x 1)]

end GlobalTheory.UPel.HT.GaussOne

namespace GlobalTheory.UPel.HT.GaussOne

theorem emb_ext (τ σ : Qi →+* ℂ) (h : τ ii = σ ii) : τ = σ :=
  RingHom.ext fun x => by
    obtain ⟨a, b, rfl⟩ := exists_coord x
    simp only [map_add, map_mul, map_ratCast, h]

theorem filt : Finset.univ.filter (fun τ : Qi →+* ℂ => τ ((ζO : 𝓞 Qi) : Qi) = (starRingEnd ℂ) Complex.I) =
    {(starRingEnd ℂ).comp τ₀} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    apply emb_ext
    rw [← coe_ζO, h, RingHom.comp_apply, coe_ζO, τ₀_ii]
  · rintro rfl
    show (starRingEnd ℂ) (τ₀ (ζO : Qi)) = _
    rw [coe_ζO, τ₀_ii]

theorem τ₀_int (a b : ℤ) : τ₀ (((a : 𝓞 Qi) + b * ζO : 𝓞 Qi) : Qi) = (a : ℂ) + b * Complex.I := by
  have : (((a : 𝓞 Qi) + b * ζO : 𝓞 Qi) : Qi) = (a : Qi) + b * ii := by
    rw [← coe_ζO]; push_cast; rfl
  rw [this]; simp [τ₀_ii]

end GlobalTheory.UPel.HT.GaussOne

namespace GlobalTheory.UPel.HT

open GaussOne

instance fact5' : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def gaussOneDatum : Datum 5 where
  F := Qi
  cm := cm
  bar := barO
  bar_eq := barO_eq
  ω := ζO
  tr := 0
  nm := 1
  tr_eq := by rw [barO_ζO]; simp
  nm_eq := by rw [barO_ζO, mul_neg, ζO_sq]; simp
  disc_neg := by norm_num
  disc_p := by norm_num
  split := ⟨2, by norm_num⟩
  O := 𝓞 Qi
  freeO := inferInstance
  finO := inferInstance
  m := 1
  m_pos := one_pos
  rankO := by rw [one_pow, one_mul]; exact RingOfIntegers.rank Qi
  central := fun x _ => ⟨x, 1, one_ne_zero, by simp⟩
  star := barO.trans (RingEquiv.toOpposite (𝓞 Qi))
  star_star := fun x => by simp [barO_barO]
  star_F := fun c => by simp
  splitP := ⟨(m1 _).restrictScalars (𝓞 Qi)⟩
  La := 𝓞 Qi
  freeLa := inferInstance
  finLa := inferInstance
  n := 1
  n_pos := le_rfl
  rankLa := by rw [one_mul, one_mul]; exact RingOfIntegers.rank Qi
  EF := EF
  alt := EF_alt
  nondeg := EF_bij.1
  perfP := ⟨1, Nat.coprime_one_left 5, fun f => by
    obtain ⟨x, hx⟩ := EF_bij.2 f
    exact ⟨x, by rw [hx, one_smul]⟩⟩
  adj := fun b x y => by simpa using EF_adj b x y
  a := 1
  ρc := Complex.I
  ρc_root := by simp
  tau := ⟨fun _ => τ₀, fun i j _ => Subsingleton.elim i j⟩
  tau_ω := fun _ => by
    show τ₀ (ζO : Qi) = Complex.I
    rw [coe_ζO, τ₀_ii]
  dom := by
    refine ⟨J, J_J, J_EF, J_pos, ?_, ?_⟩
    · intro b A hA
      rw [A_eq b A hA, J, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
      congr 1
      exact LinearMap.ext fun y => by simp [mul_left_comm]
    · intro c A hA
      have hA' : ∀ x : 𝓞 Qi, A (1 ⊗ₜ x) = 1 ⊗ₜ (c • x) := by simpa using hA
      rw [A_eq c A hA', J, ← LinearMap.baseChange_comp, ← LinearMap.mulLeft_mul, LinearMap.trace_baseChange,
        LinearMap.trace_baseChange]
      obtain ⟨a, b, rfl⟩ := coordO c
      rw [ζ_mul_coord, trace_mulLeft, trace_mulLeft]
      intro S
      have hS : S = (a : ℂ) + b * Complex.I := by
        simp only [S, Nat.cast_one, one_mul, Finset.univ_unique, Finset.sum_singleton, filt]
        show τ₀ _ + (starRingEnd ℂ) (τ₀ _) - (starRingEnd ℂ) (τ₀ _) = _
        rw [add_sub_cancel_right, τ₀_int]
      rw [hS]
      simp

theorem exists_datum_a_one : ∃ (_ : Fact (Nat.Prime 5)) (D : Datum 5), D.a = 1 ∧ D.n = 1 ∧ D.m = 1 :=
  ⟨fact5', gaussOneDatum, rfl, rfl, rfl⟩

end GlobalTheory.UPel.HT
