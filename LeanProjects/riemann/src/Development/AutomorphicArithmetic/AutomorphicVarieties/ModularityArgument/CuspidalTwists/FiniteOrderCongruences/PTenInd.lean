import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

namespace TenInd

section Mat

variable {k : Type} [Field k]

theorem ti_cp_on (g : Matrix (Fin 2) (Fin 2) k) (a b : k) :
    (tn g !![a, b; b, a]).charpoly = ((a + b) • g).charpoly * ((a - b) • g).charpoly := by
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, Matrix.charpoly, Matrix.det_succ_row_zero]
  simp (config := {decide := true}) [Fin.succAbove, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix_apply, Matrix.charmatrix_apply,
    Matrix.diagonal_apply, tn, Matrix.trace_fin_two]
  ring1

theorem ti_cp_off (g : Matrix (Fin 2) (Fin 2) k) (p q : k) (h : p ^ 2 - q ^ 2 = 1) :
    (tn g !![p, q; -q, -p]).charpoly = (g * g).charpoly.comp (X ^ 2) := by
  have h' : (C p : k[X]) ^ 2 - C q ^ 2 = 1 := by rw [← map_pow, ← map_pow, ← map_sub, h, map_one]
  rw [Matrix.charpoly_fin_two, Matrix.charpoly, Matrix.det_succ_row_zero]
  simp (config := {decide := true}) [Fin.succAbove, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix_apply, Matrix.charmatrix_apply,
    Matrix.diagonal_apply, tn, Matrix.trace_fin_two, Matrix.mul_apply,
    Polynomial.sub_comp, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp]
  linear_combination (-((C (g 0 0) + C (g 1 1)) ^ 2 - 2 * (C (g 0 0) * C (g 1 1) - C (g 0 1) * C (g 1 0))) * X ^ 2 +
    (C p ^ 2 - C q ^ 2 + 1) * (C (g 0 0) * C (g 1 1) - C (g 0 1) * C (g 1 0)) ^ 2) * h'

theorem ti_tn_ker (c a : k) (h : c * a = 1) : tn (c • (1 : Matrix (Fin 2) (Fin 2) k)) !![a, 0; 0, a] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn] <;> first | linear_combination h | linear_combination -h

theorem ti_sq_mat (p q : k) (h : p ^ 2 - q ^ 2 = 1) :
    !![p, q; -q, -p] * !![p, q; -q, -p] = (1 : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination h | ring1

theorem ti_conj_mat (a b p q : k) (h : p ^ 2 - q ^ 2 = 1) :
    (!![p, q; -q, -p] * !![a, b; b, a] * !![p, q; -q, -p]) 0 0 +
      (!![p, q; -q, -p] * !![a, b; b, a] * !![p, q; -q, -p]) 0 1 = a - b := by
  first
  | (simp [Matrix.mul_fin_two]; linear_combination (a - b) * h)
  | (simp [Matrix.mul_apply, Fin.sum_univ_two]; linear_combination (a - b) * h)

theorem ti_cp_conj {n : ℕ} (c : k) (M : GL (Fin n) k) (N : Matrix (Fin n) (Fin n) k) :
    (c • ((M : Matrix (Fin n) (Fin n) k) * N * ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))).charpoly =
      (c • N).charpoly := by
  rw [← Matrix.charpoly_units_conj M (c • N), mul_smul_comm, smul_mul_assoc, Matrix.coe_units_inv]

theorem ti_cp_conj' {n : ℕ} (c : k) (M : GL (Fin n) k) (N : Matrix (Fin n) (Fin n) k) :
    (c • (((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * N * (M : Matrix (Fin n) (Fin n) k))).charpoly =
      (c • N).charpoly := by
  have := ti_cp_conj c M⁻¹ N
  rwa [inv_inv] at this

end Mat

section Gen

variable {k : Type} [Field k] {Γ Δ : Type} [Group Γ] [Group Δ]

structure TIHyp (H : Subgroup Γ) (res : Δ →* Γ) (ρ : Γ →* GL (Fin 2) k) (κ : Δ →* kˣ)
    (Gm T : Γ →* Matrix (Fin 2) (Fin 2) k) (R : Γ →* GL (Fin 4) k) (P : GL (Fin 2) k) : Prop where
  hres : ∀ h, res h ∈ H
  hgm : ∀ x, Gm x = (P : Matrix (Fin 2) (Fin 2) k) * (ρ x : Matrix (Fin 2) (Fin 2) k) *
    ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
  hrr : ∀ x, (R x : Matrix (Fin 4) (Fin 4) k) = tn (Gm x) (T x)
  hon : ∀ x ∈ H, T x 1 1 = T x 0 0 ∧ T x 1 0 = T x 0 1
  hoff : ∀ x ∉ H, T x 1 1 = -T x 0 0 ∧ T x 1 0 = -T x 0 1
  hform : ∀ x, T x 0 0 ^ 2 - T x 1 0 ^ 2 = 1
  hkap : ∀ h, (κ h : k) = T (res h) 0 0 + T (res h) 0 1

variable {H : Subgroup Γ} {res : Δ →* Γ} {ρ : Γ →* GL (Fin 2) k} {κ : Δ →* kˣ}
  {Gm T : Γ →* Matrix (Fin 2) (Fin 2) k} {R : Γ →* GL (Fin 4) k} {P : GL (Fin 2) k}

theorem ti_shape_on (hy : TIHyp H res ρ κ Gm T R P) {x : Γ} (hx : x ∈ H) :
    T x = !![T x 0 0, T x 0 1; T x 0 1, T x 0 0] := by
  conv_lhs => rw [Matrix.eta_fin_two (T x)]
  rw [(hy.hon x hx).1, (hy.hon x hx).2]

theorem ti_shape_off (hy : TIHyp H res ρ κ Gm T R P) {x : Γ} (hx : x ∉ H) :
    T x = !![T x 0 0, T x 0 1; -T x 0 1, -T x 0 0] := by
  conv_lhs => rw [Matrix.eta_fin_two (T x)]
  rw [(hy.hoff x hx).1, (hy.hoff x hx).2]

theorem ti_form_off (hy : TIHyp H res ρ κ Gm T R P) {x : Γ} (hx : x ∉ H) :
    T x 0 0 ^ 2 - T x 0 1 ^ 2 = 1 := by
  have h := hy.hform x
  rw [(hy.hoff x hx).2] at h
  linear_combination h

theorem ti_sq (hy : TIHyp H res ρ κ Gm T R P) {t : Γ} (ht : t ∉ H) : T t * T t = 1 := by
  rw [ti_shape_off hy ht]
  exact ti_sq_mat _ _ (ti_form_off hy ht)

theorem ti_inv (hy : TIHyp H res ρ κ Gm T R P) {t : Γ} (ht : t ∉ H) : T t⁻¹ = T t := by
  calc T t⁻¹ = T t⁻¹ * (T t * T t) := by rw [ti_sq hy ht, mul_one]
    _ = T (t⁻¹ * t) * T t := by rw [map_mul, mul_assoc]
    _ = T t := by rw [inv_mul_cancel, map_one, one_mul]

theorem ti_kap_conj (hy : TIHyp H res ρ κ Gm T R P) {t : Γ} (ht : t ∉ H) {g g' : Δ}
    (hg' : res g' = t⁻¹ * res g * t) : (κ g' : k) = T (res g) 0 0 - T (res g) 0 1 := by
  have hx := hy.hres g
  obtain ⟨a, ha⟩ : ∃ a, T (res g) 0 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, T (res g) 0 1 = b := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, T t 0 0 = p := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, T t 0 1 = q := ⟨_, rfl⟩
  have hTx : T (res g) = !![a, b; b, a] := by rw [ti_shape_on hy hx, ha, hb]
  have hTt : T t = !![p, q; -q, -p] := by rw [ti_shape_off hy ht, hp, hq]
  have hpq : p ^ 2 - q ^ 2 = 1 := by rw [← hp, ← hq]; exact ti_form_off hy ht
  rw [hy.hkap g', ha, hb, hg', map_mul, map_mul, ti_inv hy ht, hTt, hTx]
  exact ti_conj_mat a b p q hpq

theorem ti_on (hy : TIHyp H res ρ κ Gm T R P) (t : Γ) (ht : t ∉ H) (g g' : Δ) (hg' : res g' = t⁻¹ * res g * t) :
    (R (res g) : Matrix (Fin 4) (Fin 4) k).charpoly =
      (UpperTheory.V.Af.tw (ρ.comp res) κ g : Matrix (Fin 2) (Fin 2) k).charpoly *
        (UpperTheory.V.Af.tw (ρ.comp res) κ g' : Matrix (Fin 2) (Fin 2) k).charpoly := by
  have hx := hy.hres g
  have hk' := ti_kap_conj hy ht hg'
  obtain ⟨a, ha⟩ : ∃ a, T (res g) 0 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, T (res g) 0 1 = b := ⟨_, rfl⟩
  have hTx : T (res g) = !![a, b; b, a] := by rw [ti_shape_on hy hx, ha, hb]
  have hρ' : (ρ (res g') : Matrix (Fin 2) (Fin 2) k) = (((ρ t)⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
      (ρ (res g) : Matrix (Fin 2) (Fin 2) k) * (ρ t : Matrix (Fin 2) (Fin 2) k) := by
    rw [hg', map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  rw [UpperTheory.V.Af.tw_val, UpperTheory.V.Af.tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, hρ', hk', hy.hkap g,
    ha, hb, hy.hrr, hTx, ti_cp_on, hy.hgm]
  simp only [ti_cp_conj, ti_cp_conj']

theorem ti_off (hy : TIHyp H res ρ κ Gm T R P) (t : Γ) (ht : t ∉ H) (g : Δ) (hg : res g = t * t) :
    (R t : Matrix (Fin 4) (Fin 4) k).charpoly =
      (UpperTheory.V.Af.tw (ρ.comp res) κ g : Matrix (Fin 2) (Fin 2) k).charpoly.comp (X ^ 2) := by
  obtain ⟨p, hp⟩ : ∃ p, T t 0 0 = p := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, T t 0 1 = q := ⟨_, rfl⟩
  have hTt : T t = !![p, q; -q, -p] := by rw [ti_shape_off hy ht, hp, hq]
  have hpq : p ^ 2 - q ^ 2 = 1 := by rw [← hp, ← hq]; exact ti_form_off hy ht
  have hk : (κ g : k) = 1 := by
    rw [hy.hkap g, hg, map_mul, hTt, ti_sq_mat p q hpq]
    simp
  rw [UpperTheory.V.Af.tw_val, MonoidHom.comp_apply, hk, one_smul, hg, hy.hrr, hTt, ti_cp_off _ _ _ hpq,
    ← map_mul Gm, hy.hgm, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem ti_ker [CharZero k] (hy : TIHyp H res ρ κ Gm T R P) (t : Γ) (ht : t ∉ H) (g g' : Δ)
    (hg' : res g' = t⁻¹ * res g * t) (h1 : UpperTheory.V.Af.tw (ρ.comp res) κ g = 1)
    (h1' : UpperTheory.V.Af.tw (ρ.comp res) κ g' = 1) : R (res g) = 1 := by
  have hx := hy.hres g
  have e1 : (κ g : k) • (ρ (res g) : Matrix (Fin 2) (Fin 2) k) = 1 := by
    have e := congrArg Units.val h1
    rwa [UpperTheory.V.Af.tw_val, MonoidHom.comp_apply, Units.val_one] at e
  have e2 : (κ g' : k) • (ρ (res g') : Matrix (Fin 2) (Fin 2) k) = 1 := by
    have e := congrArg Units.val h1'
    rwa [UpperTheory.V.Af.tw_val, MonoidHom.comp_apply, Units.val_one] at e
  have hne : (κ g : k) ≠ 0 := Units.ne_zero _
  have hρx : (ρ (res g) : Matrix (Fin 2) (Fin 2) k) = (κ g : k)⁻¹ • 1 := by
    rw [← e1, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hρx' : (ρ (res g') : Matrix (Fin 2) (Fin 2) k) = (κ g : k)⁻¹ • 1 := by
    rw [hg', map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, hρx, mul_smul_comm, mul_one,
      smul_mul_assoc, Units.inv_mul]
  have e3 : (κ g' : k) * (κ g : k)⁻¹ = 1 := by
    have e := congrFun (congrFun e2 0) 0
    rw [hρx', smul_smul] at e
    simpa using e
  have hkk : (κ g' : k) = κ g := (mul_inv_eq_one₀ hne).1 e3
  rw [ti_kap_conj hy ht hg', hy.hkap g] at hkk
  have hb : T (res g) 0 1 = 0 := by
    have h2 : (2 : k) * T (res g) 0 1 = 0 := by linear_combination -hkk
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have ha0 : T (res g) 0 0 ≠ 0 := by
    have h := hne
    rwa [hy.hkap g, hb, add_zero] at h
  apply Units.ext
  rw [hy.hrr, Units.val_one, hy.hgm, hρx, mul_smul_comm, mul_one, smul_mul_assoc, Units.mul_inv,
    ti_shape_on hy hx, hy.hkap g, hb, add_zero]
  exact ti_tn_ker _ _ (inv_mul_cancel₀ ha0)

end Gen

theorem ti_tenB_val {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (ρ₁ τ : G ℚ Ω →* M2 c.O) (x : G ℚ Ω) :
    ((tenB ρ₁ τ x : GL (Fin 4) (Qbar l)) : Matrix (Fin 4) (Fin 4) (Qbar l)) =
      tn (mapRep (algebraMap c.O (PadicAlgCl l)) ρ₁ x) (mapRep (algebraMap c.O (PadicAlgCl l)) τ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tenB, rep4, tn, MonoidHom.coe_toHomUnits]

end TenInd

theorem tenInd : TenInd := by
  intro Ω _ _ _ l _ ι K' _ _ ρ g0 m c₁ κ ρ₁ τ s hiso hτ
  obtain ⟨P, hP⟩ := hiso
  have hy : TenInd.TIHyp K'.fixingSubgroup (resQ K') ρ κ (mapRep (algebraMap c₁.O (PadicAlgCl l)) ρ₁)
      (mapRep (algebraMap c₁.O (PadicAlgCl l)) τ) (tenB ρ₁ τ) P := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      first
      | exact (mem_fixingSubgroup_iff _).2 fun y hy => h.commutes ⟨y, hy⟩
      | exact fun y => h.commutes y
      | (rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]; intro y hy; exact h.commutes ⟨y, hy⟩)
    · intro x
      have e := congrArg Units.val (hP x)
      rwa [MonoidHom.coe_toHomUnits, Units.val_mul, Units.val_mul] at e
    · exact fun x => TenInd.ti_tenB_val ρ₁ τ x
    · intro x hx
      simp [mapRep_apply, hτ.on x hx]
    · intro x hx
      simp [mapRep_apply, hτ.off x hx]
    · intro x
      have h := congrFun (congrFun (hτ.form x) 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_two] at h
      rw [mapRep_apply, mapRep_apply, ← map_pow, ← map_pow, ← map_sub,
        show τ x 0 0 ^ 2 - τ x 1 0 ^ 2 = 1 by linear_combination h, map_one]
    · intro h
      rw [hτ.val h, mapRep_apply, mapRep_apply, ← map_add]
      first | rfl | simp
  exact ⟨fun t ht g g' hg' => TenInd.ti_on hy t ht g g' hg', fun t ht g hg => TenInd.ti_off hy t ht g hg,
    fun t ht g g' hg' h1 h1' => TenInd.ti_ker hy t ht g g' hg' h1 h1'⟩

end UpperTheory.V.Cu2

end
