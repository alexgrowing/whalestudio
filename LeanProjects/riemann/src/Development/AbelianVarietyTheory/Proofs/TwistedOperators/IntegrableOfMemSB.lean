import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.Exchange

section Algebra
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem rowE_mul_inl (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : n) (s) :
    ((rowE c p u).val * M) (Sum.inl r) s = M (Sum.inl r) s := by
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem rowE_mul_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : Fin c) (s) :
    ((rowE c p u).val * M) (Sum.inr r) s =
      M (Sum.inr r) s + if r.val + 1 = p then ∑ t, u t * M (Sum.inl t) s else 0 := by
  by_cases h : r.val + 1 = p <;>
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h, add_comm]

theorem mul_rowE_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : Fin c) :
    (M * (rowE c p u).val) r (Sum.inr s) = M r (Sum.inr s) := by
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_rowE_inl (P : Fin c) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : n) :
    (M * (rowE c (P.val + 1) u).val) r (Sum.inl s) = M r (Sum.inl s) + M r (Sum.inr P) * u s := by
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.val_inj]

theorem colE_mul_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : Fin c) (s) :
    ((colE c p u).val * M) (Sum.inr r) s = M (Sum.inr r) s := by
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem colE_mul_inl (P : Fin c) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : n) (s) :
    ((colE c (P.val + 1) u).val * M) (Sum.inl r) s = M (Sum.inl r) s + u r * M (Sum.inr P) s := by
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.val_inj]

theorem mul_colE_inl (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : n) :
    (M * (colE c p u).val) r (Sum.inl s) = M r (Sum.inl s) := by
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_colE_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : Fin c) :
    (M * (colE c p u).val) r (Sum.inr s) =
      M r (Sum.inr s) + if s.val + 1 = p then ∑ t, M r (Sum.inl t) * u t else 0 := by
  by_cases h : s.val + 1 = p <;>
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h, add_comm]

theorem rowE_neg_mul (p : ℕ) (u : n → k) : rowE c p (-u) * rowE c p u = 1 := by
  ext1
  simp only [rowE, lowU, Units.val_mul, fromBlocks_multiply, Units.val_one]
  rw [← fromBlocks_one]
  congr 1 <;> simp
  ext l s; by_cases h : l.val + 1 = p <;> simp [h]

theorem colE_neg_mul (p : ℕ) (u : n → k) : colE c p (-u) * colE c p u = 1 := by
  ext1
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply, Units.val_one]
  rw [← fromBlocks_one]
  congr 1 <;> simp
  ext l s; by_cases h : s.val + 1 = p <;> simp [h]

theorem rowE_mul_embX (p : ℕ) (u : n → k) (g : GL n k) :
    rowE c p u * embX c g = embX c g * rowE c p (g.valᵀ.mulVec u) := by
  ext1
  simp only [rowE, lowU, embX, Units.val_mul, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
    fromBlocks_multiply]
  congr 1 <;> simp
  ext l s; by_cases h : l.val + 1 = p <;> simp [h, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.mulVec, mul_comm]

theorem colE_mul_embX (p : ℕ) (u : n → k) (g : GL n k) :
    colE c p u * embX c g = embX c g * colE c p ((g⁻¹).val.mulVec u) := by
  have : colE c p (g.val.mulVec ((g⁻¹).val.mulVec u)) * embX c g = embX c g * colE c p ((g⁻¹).val.mulVec u) := by
    generalize (g⁻¹).val.mulVec u = w
    ext1
    simp only [colE, upU, embX, Units.val_mul, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
      fromBlocks_multiply]
    congr 1 <;> simp
    ext l s; by_cases h : s.val + 1 = p <;> simp [h, Matrix.mul_apply, dotProduct, Matrix.mulVec]
  rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this

theorem rowE_mul_mem (P : Fin c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c (P.val + 1 + 1)) :
    ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c (P.val + 1), simpleSum h = simpleSum g ∧
      rowE c (P.val + 1) u * g = h * rowE c (P.val + 1) (u + w) := by
  rw [Model.mem_N_iff] at hg
  have h11 : ∀ r s, g.val (Sum.inl r) (Sum.inl s) = if r = s then 1 else 0 := fun r s => by
    simpa [Matrix.one_apply] using hg (Sum.inl r) (Sum.inl s) le_rfl
  have h12 : ∀ r (s : Fin c), s.val ≤ P.val + 1 → g.val (Sum.inl r) (Sum.inr s) = 0 := fun r s h => by
    simpa using hg (Sum.inl r) (Sum.inr s) (by simpa [lev] using h)
  have h21 : ∀ (r : Fin c) s, P.val < r.val → g.val (Sum.inr r) (Sum.inl s) = 0 := fun r s h => by
    simpa using hg (Sum.inr r) (Sum.inl s) (by simp [lev]; omega)
  have h22 : ∀ (r s : Fin c), s.val ≤ r.val → g.val (Sum.inr r) (Sum.inr s) = if r = s then 1 else 0 :=
    fun r s h => by simpa [Matrix.one_apply] using hg (Sum.inr r) (Sum.inr s) (by simpa [lev] using h)
  refine ⟨fun s => g.val (Sum.inr P) (Sum.inl s), fun u => ⟨rowE c (P.val + 1) u * g *
    rowE c (P.val + 1) (-(u + fun s => g.val (Sum.inr P) (Sum.inl s))), ?_, ?_, ?_⟩⟩
  · rw [Model.mem_N_iff]
    rintro (r | r) (s | s) h <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h <;>
      simp only [Units.val_mul, mul_rowE_inl, mul_rowE_inr, rowE_mul_inl, rowE_mul_inr]
    · simp [h11, h12 r P (by omega), Matrix.one_apply]
    · simp [h12 r s (by omega)]
    · by_cases hr : r = P
      · subst hr; simp [h11, h12, h22]; ring
      · have : P.val < r.val := by have := Fin.val_ne_of_ne hr; omega
        simp [h21 r s this, h22 r P this.le, hr, this.ne']
    · by_cases hr : r = P
      · subst hr; simp [h22 r s (by omega), fun t => h12 t s (by omega), Matrix.one_apply]
      · simp [h22 r s (by omega), Fin.val_ne_of_ne hr, Matrix.one_apply]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · simp only [Units.val_mul, mul_rowE_inr, rowE_mul_inr]
      split_ifs with hi
      · simp [fun t => h12 t j (by omega)]
      · simp
    · rfl
  · rw [mul_assoc, rowE_neg_mul, mul_one]

theorem colE_mul_mem (P : Fin c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c P.val) :
    ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c (P.val + 1), simpleSum h = simpleSum g ∧
      colE c (P.val + 1) u * g = h * colE c (P.val + 1) (u + w) := by
  rw [Model.mem_N_iff] at hg
  have h11 : ∀ r s, g.val (Sum.inl r) (Sum.inl s) = if r = s then 1 else 0 := fun r s => by
    simpa [Matrix.one_apply] using hg (Sum.inl r) (Sum.inl s) le_rfl
  have h12 : ∀ r (s : Fin c), s.val < P.val → g.val (Sum.inl r) (Sum.inr s) = 0 := fun r s h => by
    simpa using hg (Sum.inl r) (Sum.inr s) (by simp [lev]; omega)
  have h21 : ∀ (r : Fin c) s, P.val ≤ r.val + 1 → g.val (Sum.inr r) (Sum.inl s) = 0 := fun r s h => by
    simpa using hg (Sum.inr r) (Sum.inl s) (by simpa [lev] using h)
  have h22 : ∀ (r s : Fin c), s.val ≤ r.val → g.val (Sum.inr r) (Sum.inr s) = if r = s then 1 else 0 :=
    fun r s h => by simpa [Matrix.one_apply] using hg (Sum.inr r) (Sum.inr s) (by simpa [lev] using h)
  refine ⟨fun s => g.val (Sum.inl s) (Sum.inr P), fun u => ⟨colE c (P.val + 1) u * g *
    colE c (P.val + 1) (-(u + fun s => g.val (Sum.inl s) (Sum.inr P))), ?_, ?_, ?_⟩⟩
  · rw [Model.mem_N_iff]
    rintro (r | r) (s | s) h <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h <;>
      simp only [Units.val_mul, mul_colE_inl, mul_colE_inr, colE_mul_inl, colE_mul_inr]
    · simp [h11, h21 P s (by omega), Matrix.one_apply]
    · by_cases hr : s = P
      · subst hr; simp [h11, h21, h22]; ring
      · have : s.val < P.val := by have := Fin.val_ne_of_ne hr; omega
        simp [h12 r s this, h22 P s this.le, Ne.symm hr, this.ne]
    · simp [h21 r s (by omega)]
    · by_cases hr : s = P
      · subst hr; simp [h22 r s (by omega), fun t => h21 r t (by omega), Matrix.one_apply]
      · simp [h22 r s (by omega), Fin.val_ne_of_ne hr, Matrix.one_apply]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · simp only [Units.val_mul, mul_colE_inr, colE_mul_inr]
      split_ifs with hi
      · simp [fun t => h21 i t (by omega)]
      · simp
    · rfl
  · rw [mul_assoc, colE_neg_mul, mul_one]

end Algebra

section Analysis
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  (ν : Measure k) [ν.IsAddHaarMeasure] {A : Type} [AddCommGroup A] [Module ℂ A]

theorem integrable_of_mem_SB {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    Integrable f (Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  exact hf.1.continuous.integrable_of_hasCompactSupport hf.2

def avg (T : (n → k) → A →ₗ[ℂ] A) (l : A →ₗ[ℂ] ℂ) (h : ∀ v, (fun u => l (T u v)) ∈ SB (n → k)) :
    A →ₗ[ℂ] ℂ where
  toFun v := ∫ u, l (T u v) ∂(Measure.pi fun _ => ν)
  map_add' v w := by
    simp only [map_add]
    exact integral_add (integrable_of_mem_SB ν (h v)) (integrable_of_mem_SB ν (h w))
  map_smul' a v := by
    simp only [map_smul, RingHom.id_apply]
    exact integral_smul a _

def avg₂ {P : Type} [AddCommGroup P] [Module ℂ P] (T : (n → k) → A →ₗ[ℂ] A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ)
    (h : ∀ φ v, (fun u => b φ (T u v)) ∈ SB (n → k)) : P →ₗ[ℂ] A →ₗ[ℂ] ℂ where
  toFun φ := avg ν T (b φ) (h φ)
  map_add' φ φ' := by
    ext v
    simp only [avg, map_add, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    exact integral_add (integrable_of_mem_SB ν (h φ v)) (integrable_of_mem_SB ν (h φ' v))
  map_smul' a φ := by
    ext v
    simp only [avg, map_smul, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
    exact integral_smul a _

theorem isNEquiv_integral {ψ : AddChar k Circle} {p q : ℕ} {σ : Representation ℂ (GL (n ⊕ Fin c) k) A}
    {l : A → ℂ} (hl : IsNEquiv ψ p σ l) (E : (n → k) → GL (n ⊕ Fin c) k)
    (hE : ∀ g ∈ N k n c q, ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c p, simpleSum h = simpleSum g ∧
      E u * g = h * E (u + w)) :
    IsNEquiv ψ q σ fun v => ∫ u, l (σ (E u) v) ∂(Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  intro g hg v
  obtain ⟨w, hw⟩ := hE g hg
  have : ∀ u, l (σ (E u) (σ g v)) = (ψ (simpleSum g) : ℂ) * l (σ (E (u + w)) v) := fun u => by
    obtain ⟨h, hN, hs, he⟩ := hw u
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hl h hN, hs]
  simp only [this]
  rw [integral_const_mul, integral_add_right_eq_self (fun u => l (σ (E u) v)) w]

theorem integral_embX {P : Type} [AddCommGroup P] [Module ℂ P] {π : Representation ℂ (GL n k) P}
    {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} {b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ} (E : (n → k) → GL (n ⊕ Fin c) k)
    (g m : GL n k) (z : ℝ) (φ : P) (hb : ∀ v, b (π g φ) (σ (embX c g) v) = (z : ℂ) * b φ v)
    (hE : ∀ u, E u * embX c g = embX c g * E (m.val.mulVec u)) (v : A) :
    ∫ u, b (π g φ) (σ (E u) (σ (embX c g) v)) ∂(Measure.pi fun _ => ν) =
      ((z * (nabs k (Matrix.GeneralLinearGroup.det m))⁻¹ : ℝ) : ℂ) *
        ∫ u, b φ (σ (E u) v) ∂(Measure.pi fun _ => ν) := by
  have : ∀ u, b (π g φ) (σ (E u) (σ (embX c g) v)) = (z : ℂ) * b φ (σ (E (m.val.mulVec u)) v) := fun u => by
    rw [← Module.End.mul_apply, ← map_mul, hE, map_mul, Module.End.mul_apply, hb]
  simp only [this]
  rw [integral_const_mul, (GlobalTheory.SplitWeil.linear_change_of_variables k n n ν).1 m (fun u => b φ (σ (E u) v))]
  simp [mul_assoc]

end Analysis

theorem exchange_isPos : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ), (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ p σ l → ∃ l' : A →ₗ[ℂ] ℂ, (∀ v, l' v = exUp ν p σ l v) ∧ IsNEquiv ψ (p + 1) σ l') ∧ (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ (p + 1) σ l → ∃ l' : A →ₗ[ℂ] ℂ, (∀ v, l' v = exDown ν p σ l v) ∧ IsNEquiv ψ p σ l') ∧ ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (π : Representation ℂ (GL n k) P) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ), (IsPos ψ p π σ b → ∃ b' : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b' φ v = exUp ν p σ (b φ) v) ∧ IsPos ψ (p + 1) π σ b') ∧ (IsPos ψ (p + 1) π σ b → ∃ b' : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b' φ v = exDown ν p σ (b φ) v) ∧ IsPos ψ p π σ b') := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ
  have H := GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have up : ∀ l : A → ℂ, IsNEquiv ψ p σ l → IsNEquiv ψ (p + 1) σ (exUp ν p σ l) := fun l hl => by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    exact isNEquiv_integral ν hl _ fun g hg => rowE_mul_mem ⟨q, by omega⟩ hg
  have down : ∀ l : A → ℂ, IsNEquiv ψ (p + 1) σ l → IsNEquiv ψ p σ (exDown ν p σ l) := fun l hl =>
    isNEquiv_integral ν hl _ fun g hg => colE_mul_mem ⟨p, hpc⟩ hg
  refine ⟨fun l hl => ⟨avg ν (fun u => σ (rowE c p u)) l fun v => ((H l v).1 hl).1, fun v => rfl, up l hl⟩,
    fun l hl => ⟨avg ν (fun u => σ (colE c (p + 1) u)) l fun v => ((H l v).2 hl).1, fun v => rfl, down l hl⟩,
    fun P _ _ π b => ⟨fun hb => ⟨avg₂ ν (fun u => σ (rowE c p u)) b fun φ v => ((H (b φ) v).1 (hb.1 φ)).1,
      fun φ v => rfl, fun φ => up _ (hb.1 φ), fun g φ v => ?_⟩,
    fun hb => ⟨avg₂ ν (fun u => σ (colE c (p + 1) u)) b fun φ v => ((H (b φ) v).2 (hb.1 φ)).1,
      fun φ v => rfl, fun φ => down _ (hb.1 φ), fun g φ v => ?_⟩⟩⟩
  · let m : GL n k := ⟨g.valᵀ, (g⁻¹).valᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    have hm : Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det g := by
      ext; simp [m]
    refine (integral_embX ν (rowE c p) g m _ φ (hb.2 g φ) (fun u => rowE_mul_embX p u g) v).trans ?_
    rw [hm, ← Real.rpow_neg_one, ← Real.rpow_add (nabs_pos k _)]
    congr 3
    push_cast; ring
  · refine (integral_embX ν (colE c (p + 1)) g g⁻¹ _ φ (hb.2 g φ) (fun u => colE_mul_embX (p + 1) u g) v).trans ?_
    have hm : (nabs k (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ = nabs k (Matrix.GeneralLinearGroup.det g) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← nabs_mul, ← map_mul, inv_mul_cancel, map_one, nabs_one]
    rw [hm, ← Real.rpow_add_one (nabs_pos k _).ne']
    congr 3
    push_cast; ring

end GlobalTheory.RootEx.Exchange
