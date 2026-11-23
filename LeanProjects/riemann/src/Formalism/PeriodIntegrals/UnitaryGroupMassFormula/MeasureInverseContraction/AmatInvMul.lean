import Mathlib
import Formalism.PeriodIntegrals.NMeasInv

noncomputable section

open Matrix

namespace PI.NMeasInv.UnitaryGroupMassFormula

section Loc

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_add (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ; rw [Matrix.mulVec_add, dotProduct_add]

theorem hJ_smul (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  unfold hJ; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_sub (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  unfold hJ; rw [Matrix.mulVec_sub, dotProduct_sub]

theorem hJ_zero (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp [hJ]

theorem hJ_sum {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, y i) = ∑ i ∈ s, hJ ε x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hJ]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add, ih]

theorem hJ_conj (u w : Fin n → ℂ) : hJ ε w u = star (hJ ε u w) := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_comm]

def lf (x : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun := hJ ε x
  map_add' := hJ_add ε x
  map_smul' y c := by simp [hJ_smul]

structure Gram (e f : Fin r → Fin n → ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0

variable {ε} {e f : Fin r → Fin n → ℂ}

def Pw (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (v : Fin n → ℂ) : Fin n → ℂ :=
  v - ∑ b, hJ ε (f b) v • e b - ∑ b, hJ ε (e b) v • f b

def Afun (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (s : Fin r → ℝ) (v : Fin n → ℂ) : Fin n → ℂ :=
  ∑ b, ((s b : ℂ) * hJ ε (f b) v) • e b + ∑ b, ((s b : ℂ)⁻¹ * hJ ε (e b) v) • f b + Pw ε e f v

def Alin (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (s : Fin r → ℝ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  ∑ b, ((s b : ℂ) • lf ε (f b)).smulRight (e b) + ∑ b, ((s b : ℂ)⁻¹ • lf ε (e b)).smulRight (f b) +
    (LinearMap.id - ∑ b, (lf ε (f b)).smulRight (e b) - ∑ b, (lf ε (e b)).smulRight (f b))

theorem Alin_apply (s : Fin r → ℝ) (v : Fin n → ℂ) : Alin ε e f s v = Afun ε e f s v := by
  simp [Alin, Afun, Pw, lf, LinearMap.sum_apply, smul_eq_mul]
  try abel

def Amat (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (s : Fin r → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (Alin ε e f s)

theorem Amat_mulVec (s : Fin r → ℝ) (v : Fin n → ℂ) : Amat ε e f s *ᵥ v = Afun ε e f s v := by
  unfold Amat
  rw [LinearMap.toMatrix'_mulVec, Alin_apply]

variable (hG : Gram ε e f)
include hG

theorem fe (a b : Fin r) : hJ ε (f b) (e a) = if a = b then 1 else 0 := by
  rw [hJ_conj, hG.ef]
  split_ifs <;> simp

theorem f_sum_e (b : Fin r) (k : Fin r → ℂ) : hJ ε (f b) (∑ c, k c • e c) = k b := by
  rw [hJ_sum]
  simp [hJ_smul, fe hG]

theorem f_sum_f (b : Fin r) (k : Fin r → ℂ) : hJ ε (f b) (∑ c, k c • f c) = 0 := by
  rw [hJ_sum]
  simp [hJ_smul, hG.ff]

theorem e_sum_e (b : Fin r) (k : Fin r → ℂ) : hJ ε (e b) (∑ c, k c • e c) = 0 := by
  rw [hJ_sum]
  simp [hJ_smul, hG.ee]

theorem e_sum_f (b : Fin r) (k : Fin r → ℂ) : hJ ε (e b) (∑ c, k c • f c) = k b := by
  rw [hJ_sum]
  simp [hJ_smul, hG.ef]

theorem f_Pw (b : Fin r) (v : Fin n → ℂ) : hJ ε (f b) (Pw ε e f v) = 0 := by
  unfold Pw
  simp only [hJ_sub, f_sum_e hG, f_sum_f hG, sub_self, sub_zero]

theorem e_Pw (b : Fin r) (v : Fin n → ℂ) : hJ ε (e b) (Pw ε e f v) = 0 := by
  unfold Pw
  simp only [hJ_sub, e_sum_e hG, e_sum_f hG, sub_self, sub_zero]

theorem f_A (s : Fin r → ℝ) (b : Fin r) (v : Fin n → ℂ) :
    hJ ε (f b) (Afun ε e f s v) = (s b : ℂ) * hJ ε (f b) v := by
  unfold Afun
  simp only [hJ_add, f_sum_e hG, f_sum_f hG, f_Pw hG, add_zero]

theorem e_A (s : Fin r → ℝ) (b : Fin r) (v : Fin n → ℂ) :
    hJ ε (e b) (Afun ε e f s v) = (s b : ℂ)⁻¹ * hJ ε (e b) v := by
  unfold Afun
  simp only [hJ_add, e_sum_e hG, e_sum_f hG, e_Pw hG, add_zero, zero_add]

theorem Pw_A (s : Fin r → ℝ) (v : Fin n → ℂ) : Pw ε e f (Afun ε e f s v) = Pw ε e f v := by
  unfold Pw
  simp only [f_A hG, e_A hG]
  unfold Afun Pw
  abel

theorem A_A (s u : Fin r → ℝ) (v : Fin n → ℂ) :
    Afun ε e f s (Afun ε e f u v) = Afun ε e f (s * u) v := by
  show ∑ b, ((s b : ℂ) * hJ ε (f b) (Afun ε e f u v)) • e b +
      ∑ b, ((s b : ℂ)⁻¹ * hJ ε (e b) (Afun ε e f u v)) • f b + Pw ε e f (Afun ε e f u v) =
      Afun ε e f (s * u) v
  rw [Pw_A hG]
  simp only [f_A hG, e_A hG]
  simp only [Afun, Pi.mul_apply, Complex.ofReal_mul, mul_inv, mul_assoc]

theorem A_one (v : Fin n → ℂ) : Afun ε e f 1 v = v := by
  simp only [Afun, Pw, Pi.one_apply, Complex.ofReal_one, one_mul, inv_one]
  abel

theorem A_inv (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) (v : Fin n → ℂ) :
    Afun ε e f s (Afun ε e f s⁻¹ v) = v := by
  rw [A_A hG, show s * s⁻¹ = 1 from funext fun b => by simp [hs b], A_one hG]

theorem A_e (s : Fin r → ℝ) (d : Fin r) : Afun ε e f s (e d) = (s d : ℂ) • e d := by
  unfold Afun Pw
  simp [fe hG, hG.ee]

theorem A_orth (s : Fin r → ℝ) (z : Fin n → ℂ) (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) :
    Afun ε e f s z = z := by
  unfold Afun Pw
  simp [hez, hfz]

theorem A_spanLt (s : Fin r → ℝ) (k : ℕ) {v : Fin n → ℂ} (hv : v ∈ spanLt e k) :
    Afun ε e f s v ∈ spanLt e k := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    rw [A_e hG]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hd, rfl⟩)
  | zero => rw [← Alin_apply, map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [← Alin_apply, map_add, Alin_apply, Alin_apply]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← Alin_apply, map_smul, Alin_apply]
    exact Submodule.smul_mem _ _ hx

theorem hJ_A (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) (x y : Fin n → ℂ) :
    hJ ε (Afun ε e f s x) (Afun ε e f s y) = hJ ε x y := by
  have addl : ∀ x x' y, hJ ε (x + x') y = hJ ε x y + hJ ε x' y := fun x x' y => by
    rw [hJ_conj ε y (x + x'), hJ_add, star_add, ← hJ_conj ε y x, ← hJ_conj ε y x']
  have smull : ∀ (c : ℂ) x y, hJ ε (c • x) y = star c * hJ ε x y := fun c x y => by
    rw [hJ_conj ε y (c • x), hJ_smul, star_mul', ← hJ_conj ε y x]
  have suml : ∀ (g : Fin r → Fin n → ℂ) y, hJ ε (∑ b, g b) y = ∑ b, hJ ε (g b) y := fun g y => by
    rw [hJ_conj ε y, hJ_sum, star_sum]
    exact Finset.sum_congr rfl fun b _ => (hJ_conj ε y (g b)).symm
  have ePw : ∀ b v, hJ ε (e b) (Pw ε e f v) = 0 := e_Pw hG
  have fPw : ∀ b v, hJ ε (f b) (Pw ε e f v) = 0 := f_Pw hG
  have Pwe : ∀ b v, hJ ε (Pw ε e f v) (e b) = 0 := fun b v => by rw [hJ_conj, ePw, star_zero]
  have Pwf : ∀ b v, hJ ε (Pw ε e f v) (f b) = 0 := fun b v => by rw [hJ_conj, fPw, star_zero]
  have key : ∀ (α β α' β' : Fin r → ℂ) (v v' : Fin n → ℂ),
      hJ ε (∑ b, α b • e b + ∑ b, β b • f b + Pw ε e f v)
        (∑ b, α' b • e b + ∑ b, β' b • f b + Pw ε e f v') =
        ∑ b, (star (α b) * β' b + star (β b) * α' b) + hJ ε (Pw ε e f v) (Pw ε e f v') := by
    intro α β α' β' v v'
    simp only [addl, hJ_add, suml, hJ_sum, smull, hJ_smul, hG.ee, hG.ff, hG.ef, fe hG, ePw, fPw,
      Pwe, Pwf, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_add_distrib]
    try ring
  have dec : ∀ v, v = ∑ b, hJ ε (f b) v • e b + ∑ b, hJ ε (e b) v • f b + Pw ε e f v := fun v => by
    unfold Pw
    abel
  have hA : ∀ v, Afun ε e f s v = ∑ b, ((s b : ℂ) * hJ ε (f b) v) • e b +
      ∑ b, ((s b : ℂ)⁻¹ * hJ ε (e b) v) • f b + Pw ε e f v := fun v => rfl
  rw [hA, hA, key]
  conv_rhs => rw [dec x, dec y, key]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  have hsb : (s b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hs b)
  have hst : star (s b : ℂ) = s b := by
    first
      | simp
      | exact Complex.conj_ofReal _
  rw [star_mul', star_mul', star_inv₀, hst]
  field_simp
  try ring

omit hG in
theorem hJ_mulVec_eq (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    hJ ε (M *ᵥ x) (M *ᵥ y) = star x ⬝ᵥ ((Mᴴ * Formalism.REAL.Jm ε * M) *ᵥ y) := by
  unfold hJ
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

omit hG in
theorem inUJ_of_hJ (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ x y, hJ ε (M *ᵥ x) (M *ᵥ y) = hJ ε x y) :
    Formalism.REAL.inUJ ε M := by
  unfold Formalism.REAL.inUJ
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hJ_mulVec_eq] at this
  unfold hJ at this
  simpa [Matrix.mulVec_single_one, Pi.star_single] using this

theorem inUJ_A (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) : Formalism.REAL.inUJ ε (Amat ε e f s) := inUJ_of_hJ _ (fun x y => by rw [Amat_mulVec, Amat_mulVec]; exact hJ_A hG s hs x y)

theorem Amat_mul_inv (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) : Amat ε e f s * Amat ε e f s⁻¹ = 1 := by
  unfold Amat
  rw [← LinearMap.toMatrix'_comp]
  have hid : Alin ε e f s ∘ₗ Alin ε e f s⁻¹ = LinearMap.id := LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, Alin_apply, Alin_apply, A_inv hG s hs, LinearMap.id_apply]
  rw [hid, LinearMap.toMatrix'_id]

theorem Amat_inv_mul (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) : Amat ε e f s⁻¹ * Amat ε e f s = 1 := by
  unfold Amat
  rw [← LinearMap.toMatrix'_comp]
  have hid : Alin ε e f s⁻¹ ∘ₗ Alin ε e f s = LinearMap.id := LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, Alin_apply, Alin_apply, LinearMap.id_apply]
    have h1 := A_inv hG s⁻¹ (fun b => by simp [hs b]) v
    rwa [inv_inv] at h1
  rw [hid, LinearMap.toMatrix'_id]

theorem inN_A_conj (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) {z : Fin n → ℂ} (hez : ∀ a, hJ ε (e a) z = 0)
    (hfz : ∀ a, hJ ε (f a) z = 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : InN ε e z g) :
    InN ε e z (Amat ε e f s * g * Amat ε e f s⁻¹) := by
  have hconj : ∀ v, (Amat ε e f s * g * Amat ε e f s⁻¹ - 1) *ᵥ v =
      Afun ε e f s ((g - 1) *ᵥ Afun ε e f s⁻¹ v) := fun v => by
    have e1 : Afun ε e f s ((g - 1) *ᵥ Afun ε e f s⁻¹ v) =
        Afun ε e f s (g *ᵥ Afun ε e f s⁻¹ v) - v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Alin_apply (s := s), map_sub, Alin_apply,
        Alin_apply, A_inv hG s hs]
    rw [e1, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Amat_mulVec, Amat_mulVec]
  obtain ⟨⟨hSe, hSz⟩, hN⟩ := hg
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hconj, A_e hG s⁻¹ a, Matrix.mulVec_smul]
    exact A_spanLt hG s _ (Submodule.smul_mem _ _ (hSe a))
  · rw [hconj, A_orth hG s⁻¹ z hez hfz]
    exact A_spanLt hG s _ hSz
  · rw [hconj]
    apply A_spanLt hG s
    apply hN
    intro b
    rw [e_A hG, hy b, mul_zero]

end Loc

end PI.NMeasInv.UnitaryGroupMassFormula
