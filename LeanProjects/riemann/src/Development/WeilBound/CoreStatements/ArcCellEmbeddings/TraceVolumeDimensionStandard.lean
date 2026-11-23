import Development.WeilBound.CoreStatements.ArcCellEmbeddings.Imports
open MeasureTheory Filter Topology Matrix Metric Set GlobalTheory.SUVol GlobalTheory.CompanionTheory.Ar.abelian₂
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace UnitaryFrameBall.Iso

variable {ι : Type} {r : ℕ}

def ww (p q : ℂ) : ℂ := by classical exact if p = q then 1 else Complex.I

theorem ww_self (p : ℂ) : ww p p = 1 := if_pos rfl
theorem ww_pm : ww 1 (-1) = Complex.I := if_neg (by norm_num)
theorem ww_mp : ww (-1) 1 = Complex.I := if_neg (by norm_num)

theorem norm_ww (p q : ℂ) : ‖ww p q‖ = 1 := by
  unfold ww; split_ifs <;> simp

theorem ww_ne (p q : ℂ) : ww p q ≠ 0 := fun h => by
  have := norm_ww p q
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem ww_mul {p q : ℂ} (hp : p = 1 ∨ p = -1) (hq : q = 1 ∨ q = -1) : ww p q * ww q p = q * p := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [ww_self, ww_pm, ww_mp]

theorem ww_eq {p q : ℂ} (hp : p = 1 ∨ p = -1) (hq : q = 1 ∨ q = -1) (x y : ℂ) :
    ww q p * x + starRingEnd ℂ (ww p q * y) = (ww q p * q) * (x * q + p * starRingEnd ℂ y) := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    simp only [ww_self, ww_pm, ww_mp, map_mul, map_one, Complex.conj_I] <;> ring

def sc (v : ι → Fin r → Fin r → ℂ) :
    (ι → Matrix (Fin r) (Fin r) ℂ) →ₗ[ℝ] (ι → Matrix (Fin r) (Fin r) ℂ) where
  toFun X := fun i => Matrix.of fun a c => v i a c * X i a c
  map_add' X Y := by ext i a c; simp [mul_add]
  map_smul' t X := by ext i a c; simp [mul_left_comm]

theorem sc_apply (v : ι → Fin r → Fin r → ℂ) (X : ι → Matrix (Fin r) (Fin r) ℂ) (i : ι) (a c : Fin r) :
    sc v X i a c = v i a c * X i a c := rfl

theorem mem_diag (e : ι → Fin r → ℂ) (X : ι → Matrix (Fin r) (Fin r) ℂ) :
    X ∈ suLie (fun i => Matrix.diagonal (e i)) ↔
      ∀ i, (∀ a c, X i c a * e i c + e i a * starRingEnd ℂ (X i a c) = 0) ∧ ∑ a, X i a a = 0 := by
  refine forall_congr' fun i => and_congr ?_ Iff.rfl
  rw [← Matrix.ext_iff]
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.zero_apply]

theorem mem_one (X : ι → Matrix (Fin r) (Fin r) ℂ) :
    X ∈ suLie (fun _ : ι => (1 : Matrix (Fin r) (Fin r) ℂ)) ↔
      ∀ i, (∀ a c, X i c a + starRingEnd ℂ (X i a c) = 0) ∧ ∑ a, X i a a = 0 := by
  refine forall_congr' fun i => and_congr ?_ Iff.rfl
  rw [← Matrix.ext_iff]
  simp only [Matrix.add_apply, Matrix.mul_one, Matrix.one_mul, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.zero_apply]

variable {e : ι → Fin r → ℂ}

theorem mem_iff (he : ∀ i a, e i a = 1 ∨ e i a = -1) (X : ι → Matrix (Fin r) (Fin r) ℂ) :
    X ∈ suLie (fun i => Matrix.diagonal (e i)) ↔
      sc (fun i a c => ww (e i a) (e i c)) X ∈ suLie (fun _ : ι => (1 : Matrix (Fin r) (Fin r) ℂ)) := by
  rw [mem_diag, mem_one]
  refine forall_congr' fun i => and_congr (forall_congr' fun a => forall_congr' fun c => ?_) ?_
  · rw [sc_apply, sc_apply, ww_eq (he i a) (he i c), mul_eq_zero, or_iff_right]
    exact mul_ne_zero (ww_ne _ _) (by rcases he i c with h | h <;> simp [h])
  · simp only [sc_apply, ww_self, one_mul]

theorem mem_theta (he : ∀ i a, e i a = 1 ∨ e i a = -1) (X : ι → Matrix (Fin r) (Fin r) ℂ)
    (hX : X ∈ suLie (fun i => Matrix.diagonal (e i))) :
    sc (fun i a c => e i a * e i c) X ∈ suLie (fun i => Matrix.diagonal (e i)) := by
  rw [mem_diag] at hX ⊢
  intro i
  have hc : ∀ a, starRingEnd ℂ (e i a) = e i a := fun a => by rcases he i a with h | h <;> simp [h]
  have h2 : ∀ a, e i a * e i a = 1 := fun a => by rcases he i a with h | h <;> simp [h]
  refine ⟨fun a c => ?_, ?_⟩
  · rw [sc_apply, sc_apply, map_mul, map_mul, hc, hc]
    linear_combination (e i a * e i c) * (hX i).1 a c
  · simp only [sc_apply, h2, one_mul]
    exact (hX i).2

def TT (he : ∀ i a, e i a = 1 ∨ e i a = -1) :
    suLie (fun i => Matrix.diagonal (e i)) ≃ₗ[ℝ] suLie (fun _ : ι => (1 : Matrix (Fin r) (Fin r) ℂ)) :=
  LinearEquiv.ofBijective ((sc fun i a c => ww (e i a) (e i c)).restrict fun X hX => (mem_iff he X).1 hX) (by
    constructor
    · intro X Y h
      ext i a c
      exact mul_left_cancel₀ (ww_ne (e i a) (e i c)) (congrFun (congrFun (congrFun (congrArg Subtype.val h) i) a) c)
    · intro Y
      have h : sc (fun i a c => ww (e i a) (e i c)) (sc (fun i a c => (ww (e i a) (e i c))⁻¹) Y.1) = Y.1 := by
        ext i a c
        rw [sc_apply, sc_apply, mul_inv_cancel_left₀ (ww_ne _ _)]
      exact ⟨⟨_, (mem_iff he _).2 (h.symm ▸ Y.2)⟩, Subtype.ext h⟩)

theorem TT_apply (he : ∀ i a, e i a = 1 ∨ e i a = -1) (X : suLie (fun i => Matrix.diagonal (e i))) (i : ι)
    (a c : Fin r) : (TT he X).1 i a c = ww (e i a) (e i c) * X.1 i a c := rfl

def theta (he : ∀ i a, e i a = 1 ∨ e i a = -1) :
    suLie (fun i => Matrix.diagonal (e i)) →ₗ[ℝ] suLie (fun i => Matrix.diagonal (e i)) :=
  (sc fun i a c => e i a * e i c).restrict (mem_theta he)

theorem theta_apply (he : ∀ i a, e i a = 1 ∨ e i a = -1) (X : suLie (fun i => Matrix.diagonal (e i))) (i : ι)
    (a c : Fin r) : (theta he X).1 i a c = e i a * e i c * X.1 i a c := rfl

theorem theta_theta (he : ∀ i a, e i a = 1 ∨ e i a = -1) : theta he ∘ₗ theta he = LinearMap.id := by
  ext X i a c
  rw [LinearMap.comp_apply, theta_apply, theta_apply, LinearMap.id_apply]
  rcases he i a with h | h <;> rcases he i c with h' | h' <;> simp [h, h']

theorem trForm_TT [Fintype ι] (he : ∀ i a, e i a = 1 ∨ e i a = -1) (X Y : suLie (fun i => Matrix.diagonal (e i))) :
    trForm (TT he X).1 (TT he Y).1 = trForm X.1 (theta he Y).1 := by
  unfold trForm
  refine Finset.sum_congr rfl fun i _ => congrArg Complex.re ?_
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [TT_apply, TT_apply, theta_apply, ← ww_mul (he i a) (he i c)]
  ring

end UnitaryFrameBall.Iso

open UnitaryFrameBall.Iso UnitaryFrameBall.Tr in
theorem UnitaryFrameBall.trace_volume_dimension_standard : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : ι → Matrix (Fin r) (Fin r) ℂ), (∀ i, IsSignMat (H i)) → ∀ (n : ℕ) (b : Module.Basis (Fin n) ℝ (suLie H)), n ≤ 2 * r ^ 2 * Fintype.card ι ∧ ∃ b₀ : Module.Basis (Fin n) ℝ (suLie (fun _ : ι => (1 : Matrix (Fin r) (Fin r) ℂ))), ∀ ρ : ℝ, trVol b (lieBall H ρ) = trVol b₀ (lieBall (fun _ : ι => (1 : Matrix (Fin r) (Fin r) ℂ)) ρ) := by
  intro ι _ r H hH n b
  constructor
  · have h1 := Module.finrank_eq_card_basis b
    have h2 := Submodule.finrank_le (suLie H)
    rw [h1, Fintype.card_fin, Module.finrank_pi_fintype, Module.finrank_matrix, Complex.finrank_real_complex,
      Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
    exact h2.trans_eq (by ring)
  choose e he hHe using hH
  obtain rfl : H = fun i => Matrix.diagonal (e i) := funext hHe
  refine ⟨b.map (TT he), fun ρ => ?_⟩
  unfold trVol
  congr 1
  · have h1 : (Matrix.of fun k l => trForm ((b.map (TT he)) k).1 ((b.map (TT he)) l).1) =
        LinearMap.BilinForm.toMatrix b ((trB _).compRight (theta he)) := by
      ext k l
      rw [LinearMap.BilinForm.toMatrix_apply, Matrix.of_apply, Module.Basis.map_apply, Module.Basis.map_apply,
        trForm_TT]
      rfl
    have h2 : |LinearMap.det (theta he)| = 1 := by
      have := congrArg LinearMap.det (theta_theta he)
      rw [LinearMap.det_comp, LinearMap.det_id] at this
      rcases mul_self_eq_one_iff.1 this with h | h <;> simp [h]
    rw [h1, gram_eq, LinearMap.BilinForm.toMatrix_compRight, Matrix.det_mul, LinearMap.det_toMatrix, abs_mul, h2,
      mul_one]
  · congr 1
    have hn : ∀ X i a c, ‖(TT he X).1 i a c‖ = ‖X.1 i a c‖ := fun X i a c => by
      rw [TT_apply, norm_mul, norm_ww, one_mul]
    have hm : ∀ X, (b.map (TT he)).equivFun (TT he X) = b.equivFun X := fun X => by
      ext k; simp
    ext t
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact ⟨TT he X, fun i a c => (hn X i a c).trans_le (hX i a c), hm X⟩
    · rintro ⟨Y, hY, rfl⟩
      obtain ⟨X, rfl⟩ := (TT he).surjective Y
      exact ⟨X, fun i a c => (hn X i a c).symm.trans_le (hY i a c), (hm X).symm⟩
