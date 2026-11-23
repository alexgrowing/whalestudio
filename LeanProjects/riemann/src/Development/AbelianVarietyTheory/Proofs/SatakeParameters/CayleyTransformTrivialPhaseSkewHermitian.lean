import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvariance

noncomputable section

open Matrix

namespace GlobalTheory.Hk3.CayleyPhase

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def IsIntM {a b : Type} (M : Matrix a b L) : Prop := ∀ i j, M i j ∈ Formalism.UG.intL L

def IsSmallM {a b : Type} (M : Matrix a b L) : Prop := ∀ i j, Valued.v (M i j) < 1

theorem mem_int {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem isIntM_mul {a b c : Type} [Fintype b] {A : Matrix a b L} {B : Matrix b c L} (hA : IsIntM A) (hB : IsIntM B) :
    IsIntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

theorem isIntM_add {a b : Type} {A B : Matrix a b L} (hA : IsIntM A) (hB : IsIntM B) : IsIntM (A + B) :=
  fun i j => add_mem (hA i j) (hB i j)

theorem isIntM_neg {a b : Type} {A : Matrix a b L} (hA : IsIntM A) : IsIntM (-A) := fun i j => neg_mem (hA i j)

theorem isIntM_smul {a b : Type} {c : L} (hc : c ∈ Formalism.UG.intL L) {A : Matrix a b L} (hA : IsIntM A) : IsIntM (c • A) :=
  fun i j => mul_mem hc (hA i j)

theorem isIntM_of_small {a b : Type} {A : Matrix a b L} (hA : IsSmallM A) : IsIntM A := fun i j => le_of_lt (hA i j)

theorem lt_one_mul {x y : L} (hx : Valued.v x < 1) (hy : Valued.v y ≤ 1) : Valued.v (x * y) < 1 := by
  rw [map_mul]
  calc Valued.v x * Valued.v y ≤ Valued.v x * 1 := by gcongr
    _ = Valued.v x := mul_one _
    _ < 1 := hx

theorem int_mul_small {a b c : Type} [Fintype b] {A : Matrix a b L} {B : Matrix b c L} (hA : IsIntM A) (hB : IsSmallM B) :
    IsSmallM (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun k _ => by rw [mul_comm]; exact lt_one_mul (hB k j) (hA i k)

theorem small_smul {a b : Type} {c : L} (hc : Valued.v c ≤ 1) {A : Matrix a b L} (hA : IsSmallM A) : IsSmallM (c • A) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul, mul_comm]; exact lt_one_mul (hA i j) hc

theorem isIntM_cT {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {a b : Type} {A : Matrix a b L} (hA : IsIntM A) :
    IsIntM (Formalism.UG.cT σ A) := fun i j => by
  show Valued.v (σ (A j i)) ≤ 1
  rw [hσ]; exact hA j i

theorem trace_mem {a : Type} [Fintype a] {A : Matrix a a L} (hA : IsIntM A) : A.trace ∈ Formalism.UG.intL L :=
  sum_mem fun i _ => hA i i

theorem inv_one_sub {m : ℕ} {Z : Matrix (Fin m) (Fin m) L} (hZ : IsSmallM Z) :
    IsUnit (1 - Z).det ∧ IsIntM (1 - Z)⁻¹ := by
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  let Z' : Matrix (Fin m) (Fin m) O := fun i j => ⟨Z i j, (Valuation.mem_valuationSubring_iff _ _).2 (le_of_lt (hZ i j))⟩
  let M' : Matrix (Fin m) (Fin m) O := 1 - Z'
  have hmap : O.subtype.mapMatrix M' = 1 - Z := by
    ext i j
    have e : M' i j = (1 : Matrix (Fin m) (Fin m) O) i j - Z' i j := rfl
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, e, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp [Z']
  have hres : (IsLocalRing.residue O).mapMatrix M' = 1 := by
    ext i j
    have h0 : IsLocalRing.residue O (Z' i j) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
      exact hZ i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M', Matrix.sub_apply, map_sub, h0, sub_zero, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit M'.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hres, Matrix.det_one]
    exact one_ne_zero
  have hdetL : IsUnit (1 - Z).det := by
    rw [← hmap, ← RingHom.map_det]; exact hdet.map _
  refine ⟨hdetL, ?_⟩
  have hinv : (1 - Z)⁻¹ = O.subtype.mapMatrix M'⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [← hmap, ← RingHom.map_mul, Matrix.mul_nonsing_inv _ hdet, map_one]
  rw [hinv]
  intro i j
  exact ((M'⁻¹) i j).2

theorem inv_one_add {m : ℕ} {Z : Matrix (Fin m) (Fin m) L} (hZ : IsSmallM Z) :
    IsUnit (1 + Z).det ∧ IsIntM (1 + Z)⁻¹ := by
  have h : IsSmallM (-Z) := fun i j => by rw [Matrix.neg_apply, Valuation.map_neg]; exact hZ i j
  simpa [sub_neg_eq_add] using inv_one_sub h

theorem mem_GLint_of_int {ι : Type} [Fintype ι] [DecidableEq ι] {x : GL ι L}
    (h1 : ∀ i j, x.1 i j ∈ Formalism.UG.intL L) (h2 : ∀ i j, (x⁻¹).1 i j ∈ Formalism.UG.intL L) :
    x ∈ Formalism.UG.GLint ι (Formalism.UG.intL L) := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem cayley_ring {α : Type*} [Ring α] {Z Pi : α} (h1 : Pi * (1 - Z) = 1) (h2 : (1 - Z) * Pi = 1) :
    Pi * (1 + Z) - 1 = (Z + Z) * Pi ∧ Pi - 1 = Pi * Z := by
  have hc : (1 - Z) * (Z + Z) = (Z + Z) * (1 - Z) := by noncomm_ring
  have hcomm : Pi * (Z + Z) = (Z + Z) * Pi := by
    calc Pi * (Z + Z) = Pi * (Z + Z) * ((1 - Z) * Pi) := by rw [h2, mul_one]
      _ = Pi * ((1 - Z) * (Z + Z)) * Pi := by rw [hc]; simp only [mul_assoc]
      _ = (Z + Z) * Pi := by rw [← mul_assoc, h1, one_mul]
  constructor
  · calc Pi * (1 + Z) - 1 = Pi * (1 + Z) - Pi * (1 - Z) := by rw [h1]
      _ = Pi * (Z + Z) := by noncomm_ring
      _ = (Z + Z) * Pi := hcomm
  · calc Pi - 1 = Pi - Pi * (1 - Z) := by rw [h1]
      _ = Pi * Z := by noncomm_ring

theorem cayley_unitary_ring {α : Type*} [Ring α] {J Z Zs Pi Qi Pis : α} (hZ : Zs * J = -(J * Z))
    (hP1 : Pi * (1 - Z) = 1) (hP2 : (1 - Z) * Pi = 1) (hQ1 : Qi * (1 + Z) = 1) (hQ2 : (1 + Z) * Qi = 1)
    (hPs : Pis * (1 - Zs) = 1) : (1 + Zs) * Pis * J * (Pi * (1 + Z)) = J := by
  have ha : (1 - Zs) * J = J * (1 + Z) := by rw [sub_mul, hZ]; noncomm_ring
  have hb : (1 + Zs) * J = J * (1 - Z) := by rw [add_mul, hZ]; noncomm_ring
  have h1 : Pis * J = J * Qi := by
    calc Pis * J = Pis * J * ((1 + Z) * Qi) := by rw [hQ2, mul_one]
      _ = Pis * ((1 - Zs) * J) * Qi := by rw [ha]; simp only [mul_assoc]
      _ = J * Qi := by rw [← mul_assoc, hPs, one_mul]
  have hc : Qi * (1 - Z) = (1 - Z) * Qi := by
    have hpq : (1 - Z) * (1 + Z) = (1 + Z) * (1 - Z) := by noncomm_ring
    calc Qi * (1 - Z) = Qi * (1 - Z) * ((1 + Z) * Qi) := by rw [hQ2, mul_one]
      _ = Qi * ((1 + Z) * (1 - Z)) * Qi := by rw [← hpq]; simp only [mul_assoc]
      _ = (1 - Z) * Qi := by rw [← mul_assoc, hQ1, one_mul]
  calc (1 + Zs) * Pis * J * (Pi * (1 + Z)) = (1 + Zs) * (Pis * J) * (Pi * (1 + Z)) := by simp only [mul_assoc]
    _ = ((1 + Zs) * J) * (Qi * Pi * (1 + Z)) := by rw [h1]; simp only [mul_assoc]
    _ = J * ((1 - Z) * Qi) * Pi * (1 + Z) := by rw [hb]; simp only [mul_assoc]
    _ = J * (Qi * (1 - Z)) * Pi * (1 + Z) := by rw [hc]
    _ = J * Qi * ((1 - Z) * Pi) * (1 + Z) := by simp only [mul_assoc]
    _ = J := by rw [hP2, mul_one, mul_assoc, hQ1, mul_one]

section cT
variable (σ : L →+* L) {a b : Type}

theorem cT_add (A B : Matrix a b L) : Formalism.UG.cT σ (A + B) = Formalism.UG.cT σ A + Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_sub (A B : Matrix a b L) : Formalism.UG.cT σ (A - B) = Formalism.UG.cT σ A - Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_smul (c : L) (A : Matrix a b L) : Formalism.UG.cT σ (c • A) = σ c • Formalism.UG.cT σ A := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_herm {J : Matrix a a L} (h : ∀ i j, σ (J i j) = J j i) : Formalism.UG.cT σ J = J := by
  ext i j; simp [Formalism.UG.cT, h j i]

theorem cT_skew {C : Matrix a a L} (h : ∀ i j, σ (C i j) = - C j i) : Formalism.UG.cT σ C = -C := by
  ext i j; simp [Formalism.UG.cT, h j i]

end cT

theorem cayley_phase : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
      (∀ i j, (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) i j ∈ Formalism.UG.intL L) →
      ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) = 1) →
    ∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
    (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
    ψ ((δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))) + σ (δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))))) / 2) = 1 := by
  intro L _ _ _ ϖ σ q δ n n' JS JT ψ hU hq hJS hJT _hermS hermT hδ hψ x hyp C hskew hsmall hCx
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have hσσ := hU.1
  have hσv := hU.2.1
  have hhalf : Valued.v ((2 : L)⁻¹) ≤ 1 := by rw [map_inv₀, h2, inv_one]
  have hσhalf : σ ((2 : L)⁻¹) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  have hδI : δ ∈ Formalism.UG.intL L := le_of_eq hδ.1
  set Jt : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJt
  set Jti : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJti
  set JSi : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hJSi
  have hJtiI : IsIntM Jti := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint (inv_mem hJT)
  have hJSiI : IsIntM JSi := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint (inv_mem hJS)
  have hJJi : Jt * Jti = 1 := by rw [hJt, hJti, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcJt : Formalism.UG.cT σ Jt = Jt := cT_herm σ hermT
  have hcC : Formalism.UG.cT σ C = -C := cT_skew σ hskew
  have hcJti : Formalism.UG.cT σ Jti * Jt = 1 := by
    calc Formalism.UG.cT σ Jti * Jt = Formalism.UG.cT σ Jti * Formalism.UG.cT σ Jt := by rw [hcJt]
      _ = Formalism.UG.cT σ (Jt * Jti) := (Formalism.UG.cT_mul σ _ _).symm
      _ = 1 := by rw [hJJi, Formalism.UG.cT_one]
  set Y : Matrix (Fin n') (Fin n') L := Jti * C with hYdef
  have hY : Formalism.UG.cT σ Y * Jt = -C := by rw [hYdef, Formalism.UG.cT_mul, hcC, Matrix.mul_assoc, hcJti, Matrix.mul_one]
  have hJY : Jt * Y = C := by rw [hYdef, ← Matrix.mul_assoc, hJJi, Matrix.one_mul]
  set Z : Matrix (Fin n') (Fin n') L := (2⁻¹ : L) • Y with hZdef
  have hZZ : Z + Z = Y := by
    rw [hZdef, ← add_smul]
    have : (2⁻¹ + 2⁻¹ : L) = 1 := by
      have h2ne : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
      field_simp; norm_num
    rw [this, one_smul]
  have hZ : Formalism.UG.cT σ Z * Jt = -(Jt * Z) := by
    rw [hZdef, cT_smul, hσhalf, Matrix.smul_mul, hY, Matrix.mul_smul, hJY, smul_neg]
  have hYsmall : IsSmallM Y := int_mul_small hJtiI hsmall
  have hZsmall : IsSmallM Z := small_smul hhalf hYsmall
  obtain ⟨hPdet, hPiI⟩ := inv_one_sub hZsmall
  obtain ⟨hQdet, hQiI⟩ := inv_one_add hZsmall
  set Pi := (1 - Z)⁻¹ with hPi
  set Qi := (1 + Z)⁻¹ with hQi
  have hP1 : Pi * (1 - Z) = 1 := Matrix.nonsing_inv_mul _ hPdet
  have hP2 : (1 - Z) * Pi = 1 := Matrix.mul_nonsing_inv _ hPdet
  have hQ1 : Qi * (1 + Z) = 1 := Matrix.nonsing_inv_mul _ hQdet
  have hQ2 : (1 + Z) * Qi = 1 := Matrix.mul_nonsing_inv _ hQdet
  have hPs : Formalism.UG.cT σ Pi * (1 - Formalism.UG.cT σ Z) = 1 := by
    rw [← Formalism.UG.cT_one σ, ← cT_sub, ← Formalism.UG.cT_mul, hP2]
  let k : GL (Fin n') L := ⟨Pi * (1 + Z), Qi * (1 - Z), by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + Z), hQ2, Matrix.one_mul, hP1], by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Z), hP2, Matrix.one_mul, hQ1]⟩
  have hkU : k ∈ Formalism.UG.UJ σ Jt := by
    show Formalism.UG.cT σ (Pi * (1 + Z)) * Jt * (Pi * (1 + Z)) = Jt
    rw [Formalism.UG.cT_mul, cT_add, Formalism.UG.cT_one]
    exact cayley_unitary_ring hZ hP1 hP2 hQ1 hQ2 hPs
  have hIZ : IsIntM (1 + Z) := isIntM_add (fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _) (isIntM_of_small hZsmall)
  have hIZ' : IsIntM (1 - Z) := by
    rw [sub_eq_add_neg]
    exact isIntM_add (fun i j => by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _) (isIntM_neg (isIntM_of_small hZsmall))
  have hkI : k ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) :=
    mem_GLint_of_int (isIntM_mul hPiI hIZ) (isIntM_mul hQiI hIZ')
  obtain ⟨hr1, hr2⟩ := cayley_ring hP1 hP2
  set u := Pi * (Z * x) with hudef
  have hYxI : IsIntM (Y * x) := by rw [hYdef, Matrix.mul_assoc]; exact isIntM_mul hJtiI hCx
  have huI : IsIntM u := by
    rw [hudef, hZdef, Matrix.smul_mul]; exact isIntM_mul hPiI (isIntM_smul hhalf hYxI)
  have hkx : Pi * (1 + Z) * x - x = Y * x + Y * u := by
    have e1 : Pi * (1 + Z) * x - x = (Pi * (1 + Z) - 1) * x := by rw [Matrix.sub_mul, Matrix.one_mul]
    have e2 : Pi = 1 + Pi * Z := by rw [← hr2]; abel
    rw [e1, hr1, hZZ]
    calc Y * Pi * x = Y * (1 + Pi * Z) * x := by rw [← e2]
      _ = Y * x + Y * u := by simp only [hudef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hkxI : ∀ i j, (Pi * (1 + Z) * x - x : Matrix (Fin n') (Fin n) L) i j ∈ Formalism.UG.intL L := by
    rw [hkx]; exact isIntM_add hYxI (isIntM_mul (isIntM_of_small hYsmall) huI)
  have h3 := hyp ⟨k, hkU⟩ hkI hkxI
  change ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (Pi * (1 + Z) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (Pi * (1 + Z) * x - x))) / 2) = 1 at h3
  have hY' : ∀ {p : Type} (M : Matrix (Fin n') p L), Formalism.UG.cT σ Y * (Jt * M) = -(C * M) := by
    intro p M; rw [← Matrix.mul_assoc, hY, Matrix.neg_mul]
  have hb : GlobalTheory.Hk3.locH σ δ JS JT x (Y * x + Y * u) =
      -(δ * Matrix.trace (C * (x * JSi * Matrix.transpose (x.map σ)))) +
        δ * Matrix.trace (JSi * Formalism.UG.cT σ u * (-(C * x))) := by
    unfold GlobalTheory.Hk3.locH
    change δ * Matrix.trace (JSi * Formalism.UG.cT σ (Y * x + Y * u) * Jt * x) = _
    rw [cT_add, Formalism.UG.cT_mul σ Y x, Formalism.UG.cT_mul σ Y u]
    have e : JSi * (Formalism.UG.cT σ x * Formalism.UG.cT σ Y + Formalism.UG.cT σ u * Formalism.UG.cT σ Y) * Jt * x =
        -((JSi * Formalism.UG.cT σ x) * (C * x)) + JSi * Formalism.UG.cT σ u * (-(C * x)) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hY', Matrix.mul_neg, Matrix.neg_mul]
    rw [e, Matrix.trace_add, Matrix.trace_neg, Matrix.trace_mul_comm (JSi * Formalism.UG.cT σ x), mul_add, mul_neg]
    simp only [Matrix.mul_assoc, Formalism.UG.cT]
  rw [hkx, hb] at h3
  set a := δ * Matrix.trace (C * (x * JSi * Matrix.transpose (x.map σ))) with ha
  set b' := δ * Matrix.trace (JSi * Formalism.UG.cT σ u * (-(C * x))) with hb'
  have hb'I : b' ∈ Formalism.UG.intL L :=
    mul_mem hδI (trace_mem (isIntM_mul (isIntM_mul hJSiI (isIntM_cT hσv huI)) (isIntM_neg hCx)))
  have hσb'I : σ b' ∈ Formalism.UG.intL L := by rw [mem_int, hσv]; exact hb'I
  have hc : ψ ((b' + σ b') / 2) = 1 := by
    apply hψ
    · rw [div_eq_mul_inv]; exact mul_mem (add_mem hb'I hσb'I) hhalf
    · rw [map_div₀, map_add, hσσ, map_ofNat, add_comm]
  have e3 : (-a + b' + σ (-a + b')) / 2 = -((a + σ a) / 2) + (b' + σ b') / 2 := by
    rw [map_add, map_neg]; ring
  rw [e3, AddChar.map_add_eq_mul, hc, mul_one] at h3
  calc ψ ((a + σ a) / 2) = ψ ((a + σ a) / 2) * ψ (-((a + σ a) / 2)) := by rw [h3, mul_one]
    _ = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.Hk3.CayleyPhase
