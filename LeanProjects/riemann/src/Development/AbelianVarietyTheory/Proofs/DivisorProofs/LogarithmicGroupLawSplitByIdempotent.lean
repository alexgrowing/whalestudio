import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntInv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemImage

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def lin {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) : Fin m → MvPowerSeries (Fin n) C :=
  fun a => ∑ b, N a b • X b

theorem lin_const {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) (a : Fin m) : constantCoeff (lin N a) = 0 := by
  simp [lin]

theorem lin_hs {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) : HasSubst (lin N) :=
  hasSubst_of_constantCoeff_zero (lin_const N)

theorem int_comb {σ ι : Type} [Fintype ι] {c : ι → C} (hc : ∀ i, IsIntV v (c i))
    {f : ι → MvPowerSeries σ C} (hf : ∀ i, MvIsInt v (f i)) : MvIsInt v (∑ i, c i • f i) :=
  (ptIntSer v σ).sum_mem fun i _ => ptIntSer_smul (hc i) (hf i)

theorem lin_int {m n : ℕ} {N : Matrix (Fin m) (Fin n) C} (h : ∀ a b, IsIntV v (N a b)) (a : Fin m) :
    MvIsInt v (lin N a) := int_comb (h a) fun b => ptIntSer_X b

theorem lin_coeff {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) (a : Fin m) (i : Fin n) :
    coeff (Finsupp.single i 1) (lin N a) = N a i := by
  simp [lin, map_sum, pt_coeff_single_X]

theorem const_comb {σ ι : Type} [Fintype ι] (c : ι → C) {f : ι → MvPowerSeries σ C}
    (hf : ∀ i, constantCoeff (f i) = 0) : constantCoeff (∑ i, c i • f i) = 0 := by
  simp [hf]

theorem comb_comb {σ : Type} {l m n : ℕ} (A : Matrix (Fin l) (Fin m) C) (B : Matrix (Fin m) (Fin n) C)
    (f : Fin n → MvPowerSeries σ C) (b : Fin l) :
    ∑ a, A b a • ∑ e, B a e • f e = ∑ e, (A * B) b e • f e := by
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem comb_one {σ : Type} {n : ℕ} (f : Fin n → MvPowerSeries σ C) (b : Fin n) :
    ∑ e, (1 : Matrix (Fin n) (Fin n) C) b e • f e = f b := by
  simp [Matrix.one_apply, ite_smul]

theorem subst_lin {σ : Type} {m n : ℕ} {s : Fin n → MvPowerSeries σ C} (hs : HasSubst s)
    (N : Matrix (Fin m) (Fin n) C) (a : Fin m) : subst s (lin N a) = ∑ b, N a b • s b := by
  rw [lin, subst_sum_smul hs]
  simp only [subst_X hs]

theorem coeff_comb_lg {d m n : ℕ} (G : LogFGL v d) (N : Matrix (Fin m) (Fin d) C)
    (L : Matrix (Fin d) (Fin n) C) (a : Fin m) (i : Fin n) :
    coeff (Finsupp.single i 1) (∑ e, N a e • (subst (lin L) (G.lg e) : MvPowerSeries (Fin n) C)) = (N * L) a i := by
  simp [map_sum, pt_coeff_single_subst (lin_hs L) (lin_const L) (G.lg_const _), G.lg_lin, lin_coeff,
    Matrix.mul_apply]

theorem lg_add {σ : Type} [Finite σ] {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d) :
    subst (fun b => (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C)) (G.lg a) =
      subst x (G.lg a) + subst y (G.lg a) := by
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero (by rintro (b | b) <;> simp [hx, hy])
  have hl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.F_const) hs, G.lg_F, subst_add hs,
    subst_comp_subst_apply hl hs, subst_comp_subst_apply hr hs]
  simp only [subst_X hs, Sum.elim_inl, Sum.elim_inr]

theorem add_const {σ : Type} {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (b : Fin d) :
    constantCoeff (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C) = 0 :=
  have h : ∀ s, constantCoeff (Sum.elim x y s) = 0 := by rintro (b | b) <;> simp [hx, hy]
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (G.F_const b)

theorem add_int {σ : Type} {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0)
    (ix : ∀ a, MvIsInt v (x a)) (iy : ∀ a, MvIsInt v (y a)) (b : Fin d) :
    MvIsInt v (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C) :=
  have h : ∀ s, constantCoeff (Sum.elim x y s) = 0 := by rintro (b | b) <;> simp [hx, hy]
  ptIntSer_subst (hasSubst_of_constantCoeff_zero h) (by rintro (b | b); exacts [ix b, iy b]) (G.F_int b)

theorem lg_hom {σ : Type} {d m : ℕ} {f : MvPowerSeries (Fin d) C} {φ : Fin d → MvPowerSeries (Fin m) C}
    (h0 : ∀ a, constantCoeff (φ a) = 0) {c : Fin m → C} {g : Fin m → MvPowerSeries (Fin m) C}
    (h : subst φ f = ∑ a, c a • g a) {s : Fin m → MvPowerSeries σ C} (hs : HasSubst s) :
    subst (fun b => (subst s (φ b) : MvPowerSeries σ C)) f = ∑ a, c a • (subst s (g a) : MvPowerSeries σ C) := by
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) hs, h, subst_sum_smul hs]

theorem exists_retraction [CharZero C] {d d' : ℕ} (G : LogFGL v d) {I : Matrix (Fin d) (Fin d') C}
    {P : Matrix (Fin d') (Fin d) C} (hI : ∀ a b, IsIntV v (I a b)) (hP : ∀ a b, IsIntV v (P a b))
    (hPI : P * I = 1) {φ ψ : Fin d → MvPowerSeries (Fin d) C} (hφ : IsIntHom G G φ (I * P))
    (hψ : IsIntHom G G ψ (1 - I * P)) :
    ∃ q : Fin d' → MvPowerSeries (Fin d) C, (∀ b, constantCoeff (q b) = 0) ∧ (∀ b, MvIsInt v (q b)) ∧
      ∀ b, subst q (∑ a, P b a • (subst (lin I) (G.lg a) : MvPowerSeries (Fin d') C)) = ∑ a, P b a • G.lg a := by
  have hMi : ∀ a b, IsIntV v ((I * P) a b) := fun a b => by
    rw [Matrix.mul_apply]
    exact (ptIntSub v).sum_mem fun c _ => (ptIntSub v).mul_mem (hI a c) (hP c b)
  have hNi : ∀ a b, IsIntV v ((1 - I * P : Matrix (Fin d) (Fin d) C) a b) := fun a b => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine (ptIntSub v).sub_mem ?_ (hMi a b)
    split_ifs
    exacts [(ptIntSub v).one_mem, (ptIntSub v).zero_mem]
  have hPM : P * (I * P) = P := by rw [← Matrix.mul_assoc, hPI, Matrix.one_mul]
  have hPN : P * (1 - I * P : Matrix (Fin d) (Fin d) C) = 0 := by rw [Matrix.mul_sub, hPM, Matrix.mul_one, sub_self]
  have hMM : I * P * (I * P) = I * P := by rw [Matrix.mul_assoc, hPM]
  have hsq : I * P * (I * P) + (1 - I * P : Matrix (Fin d) (Fin d) C) * (1 - I * P : Matrix (Fin d) (Fin d) C) = 1 := by
    rw [mul_sub, sub_mul, sub_mul, hMM]; simp
  generalize hM : I * P = M at *
  generalize (1 - M : Matrix (Fin d) (Fin d) C) = N at *
  set x : Fin d → MvPowerSeries (Fin d) C := fun a => subst (lin M) (φ a) with hx
  set y : Fin d → MvPowerSeries (Fin d) C := fun a => subst (lin N) (ψ a) with hy
  have x0 : ∀ a, constantCoeff (x a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs M) (lin_const M) (hφ.1 a)
  have y0 : ∀ a, constantCoeff (y a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs N) (lin_const N) (hψ.1 a)
  have xi : ∀ a, MvIsInt v (x a) := fun a => ptIntSer_subst (lin_hs M) (lin_int hMi) (hφ.2.1 a)
  have yi : ∀ a, MvIsInt v (y a) := fun a => ptIntSer_subst (lin_hs N) (lin_int hNi) (hψ.2.1 a)
  set Θ : Fin d → MvPowerSeries (Fin d) C := fun b => subst (Sum.elim x y) (G.F b) with hΘ
  have Θ0 : ∀ a, constantCoeff (Θ a) = 0 := add_const G x0 y0
  have Θs : HasSubst Θ := hasSubst_of_constantCoeff_zero Θ0
  have hlg : ∀ a, subst Θ (G.lg a) = ∑ e, M a e • (subst (lin M) (G.lg e) : MvPowerSeries (Fin d) C) +
      ∑ e, N a e • (subst (lin N) (G.lg e) : MvPowerSeries (Fin d) C) := fun a => by
    rw [hΘ, lg_add G x0 y0, hx, hy, lg_hom hφ.1 (hφ.2.2 a) (lin_hs M), lg_hom hψ.1 (hψ.2.2 a) (lin_hs N)]
  have Θ1 : ∀ a b, coeff (Finsupp.single b 1) (Θ a) = if a = b then 1 else 0 := fun a b => by
    have h := congrArg (coeff (Finsupp.single b 1)) (hlg a)
    rw [map_add, coeff_comb_lg, coeff_comb_lg, ← Matrix.add_apply, hsq, Matrix.one_apply,
      pt_coeff_single_subst Θs Θ0 (G.lg_const a)] at h
    simpa [G.lg_lin] using h
  obtain ⟨Ψ, Ψi, Ψ0, hΨ, -⟩ := GlobalTheory.IntInv.exists_int_inv C v d Θ (add_int G x0 y0 xi yi) Θ0 Θ1
  have Ψs : HasSubst Ψ := hasSubst_of_constantCoeff_zero Ψ0
  refine ⟨fun b => ∑ a, P b a • Ψ a, fun b => const_comb _ Ψ0, fun b => int_comb (hP b) Ψi, fun b => ?_⟩
  have key : subst (lin P) (∑ a, P b a • (subst (lin I) (G.lg a) : MvPowerSeries (Fin d') C)) =
      subst Θ (∑ a, P b a • G.lg a) := by
    have hl : (fun a => (subst (lin P) (lin I a) : MvPowerSeries (Fin d) C)) = lin M := by
      funext a
      rw [subst_lin (lin_hs P), ← hM]
      exact comb_comb I P _ a
    rw [subst_sum_smul (lin_hs P), subst_sum_smul Θs]
    simp only [hlg, smul_add, Finset.sum_add_distrib, comb_comb, hPM, hPN,
      subst_comp_subst_apply (lin_hs I) (lin_hs P), hl]
    simp
  have h := congrArg (subst Ψ) key
  rw [subst_comp_subst_apply (lin_hs P) Ψs, subst_comp_subst_apply Θs Ψs] at h
  simp only [subst_lin Ψs, hΨ] at h
  rw [h, show (fun a => (X a : MvPowerSeries (Fin d) C)) = X from rfl, subst_self]
  rfl

theorem exists_image (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d d' : ℕ) (G : LogFGL v d)
    (I : Matrix (Fin d) (Fin d') C) (P : Matrix (Fin d') (Fin d) C) (hI : ∀ a b, IsIntV v (I a b))
    (hP : ∀ a b, IsIntV v (P a b)) (hPI : P * I = 1) (hφ : ∃ φ, IsIntHom G G φ (I * P))
    (hψ : ∃ ψ, IsIntHom G G ψ (1 - I * P)) :
    ∃ G' : LogFGL v d', (∃ j, IsIntHom G' G j I) ∧ ∃ q, IsIntHom G G' q P := by
  obtain ⟨φ, hφ⟩ := hφ
  obtain ⟨ψ, hψ⟩ := hψ
  obtain ⟨q, q0, qi, hq⟩ := exists_retraction G hI hP hPI hφ hψ
  set lg' : Fin d' → MvPowerSeries (Fin d') C := fun b => ∑ a, P b a • subst (lin I) (G.lg a) with hlg'
  set j : Fin d → MvPowerSeries (Fin d') C := fun a => subst (lin I) (φ a) with hjdef
  have j0 : ∀ a, constantCoeff (j a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs I) (lin_const I) (hφ.1 a)
  have ji : ∀ a, MvIsInt v (j a) := fun a => ptIntSer_subst (lin_hs I) (lin_int hI) (hφ.2.1 a)
  have hj : ∀ a, subst j (G.lg a) = ∑ e, I a e • lg' e := fun a => by
    rw [hjdef, lg_hom hφ.1 (hφ.2.2 a) (lin_hs I), hlg']
    exact (comb_comb I P _ a).symm
  have hl0 : ∀ b : Fin d', constantCoeff (X (Sum.inl b) : MvPowerSeries (Fin d' ⊕ Fin d') C) = 0 := fun _ => by simp
  have hr0 : ∀ b : Fin d', constantCoeff (X (Sum.inr b) : MvPowerSeries (Fin d' ⊕ Fin d') C) = 0 := fun _ => by simp
  have hl := hasSubst_of_constantCoeff_zero hl0
  have hr := hasSubst_of_constantCoeff_zero hr0
  set x : Fin d → MvPowerSeries (Fin d' ⊕ Fin d') C := fun a => subst (fun b => X (Sum.inl b)) (j a) with hx
  set y : Fin d → MvPowerSeries (Fin d' ⊕ Fin d') C := fun a => subst (fun b => X (Sum.inr b)) (j a) with hy
  have x0 : ∀ a, constantCoeff (x a) = 0 := fun a => constantCoeff_subst_eq_zero hl hl0 (j0 a)
  have y0 : ∀ a, constantCoeff (y a) = 0 := fun a => constantCoeff_subst_eq_zero hr hr0 (j0 a)
  have xi : ∀ a, MvIsInt v (x a) := fun a => ptIntSer_subst hl (fun _ => ptIntSer_X _) (ji a)
  have yi : ∀ a, MvIsInt v (y a) := fun a => ptIntSer_subst hr (fun _ => ptIntSer_X _) (ji a)
  have s0 := add_const G x0 y0
  have ss := hasSubst_of_constantCoeff_zero s0
  refine ⟨{ lg := lg'
            lg_const := fun b => const_comb _ fun a =>
              constantCoeff_subst_eq_zero (lin_hs I) (lin_const I) (G.lg_const a)
            lg_lin := fun a b => by rw [hlg', coeff_comb_lg, hPI, Matrix.one_apply]
            F := fun b => subst (fun a => (subst (Sum.elim x y) (G.F a) : MvPowerSeries (Fin d' ⊕ Fin d') C)) (q b)
            F_int := fun b => ptIntSer_subst ss (add_int G x0 y0 xi yi) (qi b)
            F_const := fun b => constantCoeff_subst_eq_zero ss s0 (q0 b)
            lg_F := fun b => ?_ }, ⟨j, j0, ji, hj⟩, q, q0, qi, hq⟩
  rw [lg_hom q0 (hq b) ss]
  simp only [lg_add G x0 y0, smul_add, Finset.sum_add_distrib]
  simp only [hx, hy, lg_hom j0 (hj _) hl, lg_hom j0 (hj _) hr, comb_comb, hPI, comb_one]

end GlobalTheory.IdemImage
