import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulOfDetZero
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.Hk.CommTD

def tri (q : ℕ) : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(q : ℤ), 0; 0, 1]
  | some u => !![1, ((u : ℕ) : ℤ); 0, (q : ℤ)]

theorem tri_det (q : ℕ) (x : Option (Fin q)) : (tri q x).det = q := by
  cases x <;> simp [tri, Matrix.det_fin_two_of]

theorem tri_exists {q : ℕ} (hp : q.Prime) (δ : Matrix (Fin 2) (Fin 2) ℤ) (hδ : δ.det = q) :
    ∃ (γ : SL(2, ℤ)) (y : Option (Fin q)), δ = γ.1 * tri q y := by
  first
  | exact @_root_.GlobalTheory.DetZeroFactorization.main
  | exact _root_.GlobalTheory.DetZeroFactorization.main
  | (apply _root_.GlobalTheory.DetZeroFactorization.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DetZeroFactorization.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DetZeroFactorization.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DetZeroFactorization.main ..)

def rep (q : ℕ) (w : SL(2, ℤ)) : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => w.1 * tri q none
  | some u => tri q (some u)

theorem rep_det (q : ℕ) (w : SL(2, ℤ)) (x : Option (Fin q)) : (rep q w x).det = q := by
  cases x with
  | none => simp [rep, Matrix.det_mul, tri_det]
  | some u => exact tri_det q (some u)

theorem rep_none_entries (q : ℕ) (w : SL(2, ℤ)) :
    rep q w none 0 0 = q * w 0 0 ∧ rep q w none 0 1 = w 0 1 ∧
      rep q w none 1 0 = q * w 1 0 ∧ rep q w none 1 1 = w 1 1 := by
  simp [rep, tri, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem rep_inj {q : ℕ} (hp : q.Prime) (w : SL(2, ℤ)) (γ : SL(2, ℤ)) {x y : Option (Fin q)}
    (h : rep q w x = γ.1 * rep q w y) : x = y := by
  have hnd : ¬ (q : ℤ) ∣ 1 := fun h => hp.not_dvd_one (by exact_mod_cast h)
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  have dγ := γ.det_coe
  have dw := w.det_coe
  rw [Matrix.det_fin_two] at dγ dw
  obtain ⟨e00, e01, e10, e11⟩ := rep_none_entries q w
  rcases x with _ | u <;> rcases y with _ | v
  · rfl
  · simp [rep, tri, Matrix.mul_apply, Fin.sum_univ_two, e00, e10] at h00 h10
    exact absurd ⟨w 0 0 * γ 1 1 - γ 0 1 * w 1 0, by rw [← h00, ← h10] at dγ; linear_combination -dγ⟩ hnd
  · simp [rep, tri, Matrix.mul_apply, Fin.sum_univ_two, e00, e10] at h00 h10
    exact absurd ⟨γ 0 0 * w 0 0 + γ 0 1 * w 1 0, by linear_combination h00⟩ hnd
  · simp [rep, tri, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 ⊢
    rw [← h00] at h01
    have : (u : ℤ) ≡ (v : ℤ) [ZMOD q] := (Int.modEq_iff_dvd.2 ⟨γ 0 1, by linear_combination h01⟩).symm
    have h2 : (u : ℕ) ≡ (v : ℕ) [MOD q] := Int.natCast_modEq_iff.1 this
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h2 u.2 v.2)

end GlobalTheory.Hk.CommTD

namespace GlobalTheory.Hk.CommTD

theorem zmod_of_mul {N l : ℕ} {x : ℤ} (h : ((x : ℤ) : ZMod (N * l)) = 0) :
    ((x : ℤ) : ZMod N) = 0 ∧ ((x : ℤ) : ZMod l) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast at h
  exact ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩

theorem mem_lev {N l : ℕ} (γ : SL(2, ℤ)) (h10 : ((γ 1 0 : ℤ) : ZMod (N * l)) = 0)
    (h00 : ((γ 0 0 : ℤ) : ZMod N) = 1) : γ ∈ lev N l := by
  obtain ⟨hN, hl⟩ := zmod_of_mul h10
  refine ⟨(Gamma1_mem N γ).2 ⟨h00, ?_, hN⟩, Gamma0_mem.2 hl⟩
  have dγ := congrArg (Int.cast : ℤ → ZMod N) γ.det_coe
  rw [Matrix.det_fin_two] at dγ
  push_cast at dγ
  rw [h00, hN] at dγ
  linear_combination dγ

theorem mul_cong {N l : ℕ} (a b : Matrix (Fin 2) (Fin 2) ℤ) (ha : ((a 1 0 : ℤ) : ZMod (N * l)) = 0)
    (hb : ((b 1 0 : ℤ) : ZMod (N * l)) = 0) :
    (((a * b) 1 0 : ℤ) : ZMod (N * l)) = 0 ∧
      (((a * b) 0 0 : ℤ) : ZMod N) = ((a 0 0 : ℤ) : ZMod N) * ((b 0 0 : ℤ) : ZMod N) := by
  have hb' := (zmod_of_mul hb).1
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [ha, hb, hb']
  constructor <;> ring

theorem rep_cong {N l q : ℕ} {w : SL(2, ℤ)} (hw : IsDia N l q w) (x : Option (Fin q)) :
    ((rep q w x 1 0 : ℤ) : ZMod (N * l)) = 0 ∧ ((rep q w x 0 0 : ℤ) : ZMod N) = 1 := by
  obtain ⟨e00, e01, e10, e11⟩ := rep_none_entries q w
  rcases x with _ | u
  · rw [e00, e10]
    have h1 := hw.2
    have h0 := (zmod_of_mul hw.1).1
    have dw := congrArg (Int.cast : ℤ → ZMod N) w.det_coe
    rw [Matrix.det_fin_two] at dw
    push_cast at dw h1 ⊢
    refine ⟨by rw [hw.1, mul_zero], ?_⟩
    rw [h0, h1] at dw
    linear_combination dw
  · simp [rep, tri]

theorem conj_cong {N l : ℕ} (ρ : SL(2, ℤ)) (hρ : ((ρ 1 0 : ℤ) : ZMod (N * l)) = 0)
    (m : Matrix (Fin 2) (Fin 2) ℤ) (h10 : ((m 1 0 : ℤ) : ZMod (N * l)) = 0)
    (h00 : ((m 0 0 : ℤ) : ZMod N) = 1) :
    (((ρ.1 * m * (ρ⁻¹).1) 1 0 : ℤ) : ZMod (N * l)) = 0 ∧
      (((ρ.1 * m * (ρ⁻¹).1) 0 0 : ℤ) : ZMod N) = 1 := by
  have hi : (((ρ⁻¹).1 1 0 : ℤ) : ZMod (N * l)) = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hρ]
  obtain ⟨a1, a2⟩ := mul_cong ρ.1 m hρ h10
  obtain ⟨b1, b2⟩ := mul_cong (ρ.1 * m) (ρ⁻¹).1 a1 hi
  refine ⟨b1, ?_⟩
  rw [b2, a2, h00]
  have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) (congrArg Subtype.val (mul_inv_cancel ρ))
  have e' := (mul_cong ρ.1 (ρ⁻¹).1 hρ hi).2
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at e
  rw [mul_one, ← e', e, Matrix.one_apply_eq, Int.cast_one]

theorem exists_rep {N l q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N * l) {w : SL(2, ℤ)} (hw : IsDia N l q w)
    (m : Matrix (Fin 2) (Fin 2) ℤ) (hdet : m.det = q) (h10 : ((m 1 0 : ℤ) : ZMod (N * l)) = 0)
    (h00 : ((m 0 0 : ℤ) : ZMod N) = 1) :
    ∃ γ : SL(2, ℤ), γ ∈ lev N l ∧ ∃ y, m = γ.1 * rep q w y := by
  obtain ⟨γ, y, hm⟩ := tri_exists hq m hdet
  have g00 := congrFun (congrFun hm 0) 0
  have g10 := congrFun (congrFun hm 1) 0
  rcases y with _ | u
  · simp [tri, Matrix.mul_apply, Fin.sum_univ_two] at g00 g10
    have hcop : Nat.Coprime q (N * l) := (Nat.Prime.coprime_iff_not_dvd hq).2 hqN
    have hu : IsUnit ((q : ℕ) : ZMod (N * l)) := (ZMod.unitOfCoprime q hcop).isUnit
    have c10 : ((γ 1 0 : ℤ) : ZMod (N * l)) = 0 := by
      rw [g10] at h10; push_cast at h10
      exact hu.mul_left_eq_zero.1 h10
    refine ⟨γ * w⁻¹, ?_, none, ?_⟩
    · have hwi : (((w⁻¹ : SL(2, ℤ)).1 1 0 : ℤ) : ZMod (N * l)) = 0 := by
        rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
        simp [hw.1]
      obtain ⟨a1, a2⟩ := mul_cong γ.1 (w⁻¹).1 c10 hwi
      refine mem_lev _ (by rw [Matrix.SpecialLinearGroup.coe_mul]; exact a1) ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, a2]
      rw [g00] at h00
      have h1 := hw.2
      have h0 := (zmod_of_mul hw.1).1
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      push_cast at h00 h1 ⊢
      rw [h1]
      linear_combination h00
    · rw [hm, rep, Matrix.SpecialLinearGroup.coe_mul, mul_assoc, ← mul_assoc (w⁻¹).1,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]
  · simp [tri, Matrix.mul_apply, Fin.sum_univ_two] at g00 g10
    refine ⟨γ, mem_lev γ (by rw [← g10]; exact h10) (by rw [← g00]; exact h00), some u, hm⟩

theorem perm {N l q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N * l) {w : SL(2, ℤ)} (hw : IsDia N l q w)
    (ρ : SL(2, ℤ)) (hρ : ((ρ 1 0 : ℤ) : ZMod (N * l)) = 0) :
    ∃ (s : Option (Fin q) → Option (Fin q)) (δ : Option (Fin q) → SL(2, ℤ)), Function.Bijective s ∧
      ∀ x, δ x ∈ lev N l ∧ ρ.1 * rep q w x = (δ x).1 * rep q w (s x) * ρ.1 := by
  have ei : (ρ⁻¹ : SL(2, ℤ)).1 * ρ.1 = 1 := congrArg Subtype.val (inv_mul_cancel ρ)
  have ex : ∀ x, ∃ γ : SL(2, ℤ), γ ∈ lev N l ∧ ∃ y, ρ.1 * rep q w x = γ.1 * rep q w y * ρ.1 := by
    intro x
    obtain ⟨c1, c2⟩ := rep_cong hw x
    obtain ⟨d1, d2⟩ := conj_cong ρ hρ _ c1 c2
    obtain ⟨γ, hγ, y, hy⟩ := exists_rep hq hqN hw _
      (by rw [Matrix.det_mul, Matrix.det_mul, rep_det, ρ.det_coe, (ρ⁻¹).det_coe]; ring) d1 d2
    refine ⟨γ, hγ, y, ?_⟩
    rw [← hy, mul_assoc _ (ρ⁻¹).1, ei, mul_one]
  choose δ hδ s h using ex
  refine ⟨s, δ, Finite.injective_iff_bijective.1 fun x y e => ?_, fun x => ⟨hδ x, h x⟩⟩
  refine rep_inj hq w (ρ⁻¹ * δ x * (δ y)⁻¹ * ρ) ?_
  have hx := h x
  have hy := h y
  rw [e] at hx
  have e2 : ((δ y)⁻¹ : SL(2, ℤ)).1 * (δ y).1 = 1 := congrArg Subtype.val (inv_mul_cancel (δ y))
  calc rep q w x = (ρ⁻¹ : SL(2, ℤ)).1 * (ρ.1 * rep q w x) := by rw [← mul_assoc, ei, one_mul]
    _ = (ρ⁻¹ : SL(2, ℤ)).1 * (δ x).1 * (((δ y)⁻¹ : SL(2, ℤ)).1 * (δ y).1) * rep q w (s y) * ρ.1 := by
      rw [hx, e2, mul_one]; simp only [mul_assoc]
    _ = (ρ⁻¹ : SL(2, ℤ)).1 * (δ x).1 * ((δ y)⁻¹ : SL(2, ℤ)).1 * ((δ y).1 * rep q w (s y) * ρ.1) := by
      simp only [mul_assoc]
    _ = _ := by rw [← hy]; simp only [Matrix.SpecialLinearGroup.coe_mul, mul_assoc]

end GlobalTheory.Hk.CommTD

namespace GlobalTheory.Hk.CommTD

def repG {q : ℕ} (hq : 0 < q) (w : SL(2, ℤ)) (x : Option (Fin q)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix (rep q w x)) (by
    rw [← RingHom.map_det, rep_det]; simpa using hq.ne')

theorem repG_val {q : ℕ} (hq : 0 < q) (w : SL(2, ℤ)) (x : Option (Fin q)) :
    (repG hq w x).1 = (Int.castRingHom ℝ).mapMatrix (rep q w x) := rfl

theorem repG_det {q : ℕ} (hq : 0 < q) (w : SL(2, ℤ)) (x : Option (Fin q)) :
    (repG hq w x).det.val = q := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, repG_val, ← RingHom.map_det, rep_det]; simp

def diagG {q : ℕ} (hq : 0 < q) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, 1] (by
    simp [Matrix.det_fin_two_of]; exact hq.ne')

theorem repG_none {q : ℕ} (hq : 0 < q) (w : SL(2, ℤ)) :
    repG hq w none = Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) w) * diagG hq := by
  apply Units.ext
  rw [repG_val, rep, map_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tri, diagG]

theorem slash_diag {q : ℕ} (hq : 0 < q) (k : ℤ) (g : ℍ → ℂ) :
    g ∣[k] diagG hq = ((q : ℂ) ^ (k - 1)) • vOp q g := by
  have hpos : 0 < (diagG hq).det.val := by
    simp [diagG, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]; exact hq
  funext z
  rw [slash_apply, UpperHalfPlane.σ, if_pos hpos, ← ofComplex_apply (diagG hq • z), coe_smul_of_det_pos hpos]
  simp [num, denom, diagG, vOp, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]
  ring

theorem slash_tri {q : ℕ} (hq : 0 < q) (k : ℤ) (w : SL(2, ℤ)) (g : ℍ → ℂ) (u : Fin q) (z : ℍ) :
    (g ∣[k] repG hq w (some u)) z = (q : ℂ)⁻¹ * g (ofComplex (((z : ℂ) + (u : ℕ)) / q)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpos : 0 < (repG hq w (some u)).det.val := by rw [repG_det]; exact_mod_cast hq
  rw [slash_apply, UpperHalfPlane.σ, if_pos hpos, repG_det, ← ofComplex_apply (repG hq w (some u) • z),
    coe_smul_of_det_pos hpos]
  simp [num, denom, repG_val, rep, tri, zpow_sub₀ hq0]
  field_simp

theorem heckeT_eq {q : ℕ} (hq : 0 < q) (k : ℤ) (w : SL(2, ℤ)) (g : ℍ → ℂ) :
    heckeT k q w g = ∑ x : Option (Fin q), g ∣[k] repG hq w x := by
  rw [Fintype.sum_option, heckeT, repG_none, SlashAction.slash_mul, ← SL_slash, slash_diag, add_comm]
  congr 1
  funext z
  rw [Finset.sum_apply]
  simp only [slash_tri]
  rw [uOp, ← Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun b : ℕ => g (ofComplex (((z : ℂ) + b) / q)))]

end GlobalTheory.Hk.CommTD

namespace GlobalTheory.Hk.CommTD

theorem slash_conj {q : ℕ} (hq : 0 < q) (k : ℤ) (w ρ δ : SL(2, ℤ)) (g : ℍ → ℂ) {x y : Option (Fin q)}
    (h : ρ.1 * rep q w x = δ.1 * rep q w y * ρ.1) :
    (g ∣[k] ρ) ∣[k] repG hq w x = ((g ∣[k] δ) ∣[k] repG hq w y) ∣[k] ρ := by
  rw [SL_slash, SL_slash, SL_slash, ← SlashAction.slash_mul, ← SlashAction.slash_mul, ← SlashAction.slash_mul]
  congr 1
  apply Units.ext
  have := congrArg (Int.castRingHom ℝ).mapMatrix h
  rw [map_mul, map_mul, map_mul, mul_assoc] at this
  simp only [Units.val_mul]
  exact this

end GlobalTheory.Hk.CommTD

theorem GlobalTheory.Hk.heckeT_dia_comm : ∀ (N l q : ℕ) (k d : ℤ) (σ ρ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l d ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.dia k ρ ⇑f) = GlobalTheory.Hk.dia k ρ (GlobalTheory.Hk.heckeT k q σ ⇑f) := by
  intro N l q k d σ ρ _ hq hqN hσ hρ f
  obtain ⟨s, δ, hs, h⟩ := GlobalTheory.Hk.CommTD.perm hq hqN hσ ρ hρ.1
  rw [GlobalTheory.Hk.CommTD.heckeT_eq hq.pos, GlobalTheory.Hk.CommTD.heckeT_eq hq.pos, GlobalTheory.Hk.dia, GlobalTheory.Hk.dia,
    SlashAction.sum_slash, ← hs.sum_comp (fun y => (⇑f ∣[k] GlobalTheory.Hk.CommTD.repG hq.pos σ y) ∣[k] ρ)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hinv : (⇑f) ∣[k] (δ x) = ⇑f := by
    rw [SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ ⟨δ x, (h x).1, rfl⟩
  rw [GlobalTheory.Hk.CommTD.slash_conj hq.pos k σ ρ (δ x) ⇑f (h x).2, hinv]
