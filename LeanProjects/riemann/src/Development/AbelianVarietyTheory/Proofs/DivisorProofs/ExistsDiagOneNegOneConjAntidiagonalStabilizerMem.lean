import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacFlip

open GlobalTheory.DblVac

open Matrix

section Idem

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι κ : Type} [Fintype ι] [DecidableEq ι]

theorem idem_sandwich {e : R} (he : e * e = e) (N X : Matrix ι ι A) :
    ((1 - e) • (1 : Matrix ι ι A) + e • N) * X * ((1 - e) • (1 : Matrix ι ι A) + e • N) =
      (1 - e) • X + e • (N * X * N) := by
  have h11 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  have h10 : (1 - e) * e = 0 := by linear_combination -he
  have h01 : e * (1 - e) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    h11, h10, h01, he, zero_smul, add_zero, zero_add]

end Idem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mul_idem_eq_zero (v : Pl F) {x : AF F} (hx : evFin F v x = 0) : x * GlobalTheory.LatVac.liftV v 1 = 0 :=
  GlobalTheory.LatVac.at_liftV v 1 x hx

theorem idem_mul_self (v : Pl F) : GlobalTheory.LatVac.liftV v 1 * GlobalTheory.LatVac.liftV v 1 = (GlobalTheory.LatVac.liftV v 1 : AF F) := by
  have h := mul_idem_eq_zero v (x := GlobalTheory.LatVac.liftV v 1 - 1)
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rwa [sub_mul, one_mul, sub_eq_zero] at h

local notation:70 A:70 " ⬝ₘ " B:71 => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

def flipM (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := fromBlocks 1 0 0 (-1)

theorem flipM_mul_self (d : ℕ) : flipM (F := F) (E := E) d * flipM d = 1 := by
  simp [flipM, fromBlocks_multiply, ← fromBlocks_one]

theorem flipM_transpose (d : ℕ) : (flipM (F := F) (E := E) d)ᵀ = flipM d := by
  simp [flipM, fromBlocks_transpose]

theorem flipM_dbl {d : ℕ} (J : Matrix (Fin d) (Fin d) (AE F E)) : flipM d * dbl J * flipM d = dbl J := by
  simp [flipM, dbl, fromBlocks_multiply]

theorem flipM_diagCols (d : ℕ) : flipM (F := F) (E := E) d ⬝ₘ diagCols (Fin d) = antiCols d := by
  ext (i | i) j <;> simp only [flipM, diagCols, antiCols, Matrix.mul_apply, Fintype.sum_sum_type] <;>
    simp [Matrix.one_apply]

theorem flipM_antiCols (d : ℕ) : flipM (F := F) (E := E) d ⬝ₘ antiCols d = diagCols (Fin d) := by
  ext (i | i) j <;> simp only [flipM, diagCols, antiCols, Matrix.mul_apply, Fintype.sum_sum_type] <;>
    simp [Matrix.one_apply]

theorem flipM_map (σ : E →ₐ[F] E) (d : ℕ) : (flipM (F := F) (E := E) d).map (cA σ) = flipM d := by
  ext (i | i) (j | j) <;> simp [flipM, Matrix.one_apply] <;> split_ifs <;> simp

section Idem2

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem idem_conj_cols {e : R} (he : e * e = e) (N Q : Matrix ι ι A) (D Ac : Matrix ι κ A) (T : Matrix κ κ A)
    (hND : N ⬝ₘ D = Ac) (hNA : N ⬝ₘ Ac = D) (hQ : (1 - e) • Q = (1 - e) • (1 : Matrix ι ι A))
    (hQA : Q ⬝ₘ Ac = Ac ⬝ₘ T) :
    (((1 - e) • (1 : Matrix ι ι A) + e • N) * Q * ((1 - e) • (1 : Matrix ι ι A) + e • N)) ⬝ₘ D =
      D ⬝ₘ ((1 - e) • (1 : Matrix κ κ A) + e • T) := by
  have hQD : (1 - e) • (Q ⬝ₘ D) = (1 - e) • D := by
    rw [← Matrix.smul_mul, hQ, Matrix.smul_mul, Matrix.one_mul]
  rw [idem_sandwich he, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hQD,
    Matrix.mul_assoc, Matrix.mul_assoc, hND, hQA, ← Matrix.mul_assoc, hNA, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one]

theorem idem_unit {e : R} (he : e * e = e) (T Ti : Matrix κ κ A) (h : T * Ti = 1) :
    ((1 - e) • (1 : Matrix κ κ A) + e • T) * ((1 - e) • (1 : Matrix κ κ A) + e • Ti) = 1 := by
  have h11 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  have h10 : (1 - e) * e = 0 := by linear_combination -he
  have h01 : e * (1 - e) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    h11, h10, h01, he, zero_smul, add_zero, zero_add, h]
  rw [← add_smul, sub_add_cancel, one_smul]

end Idem2

def flipAt (v : Pl F) (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
  (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) +
    (GlobalTheory.LatVac.liftV v 1 : AF F) • flipM d

theorem flipAt_mul_self (v : Pl F) (d : ℕ) : flipAt (E := E) v d * flipAt v d = 1 := by
  have h := idem_sandwich (idem_mul_self v) (flipM (F := F) (E := E) d) 1
  rw [Matrix.mul_one, Matrix.mul_one, flipM_mul_self, ← add_smul, sub_add_cancel, one_smul] at h
  exact h

theorem flipAt_transpose (v : Pl F) (d : ℕ) : (flipAt (E := E) v d)ᵀ = flipAt v d := by
  simp only [flipAt, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, flipM_transpose]

theorem flipAt_map (σ : E →ₐ[F] E) (v : Pl F) (d : ℕ) : (flipAt (E := E) v d).map (cA σ) = flipAt v d := by
  ext i j
  have h1 : (cA σ) ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) i j) = (1 : Matrix _ _ (AE F E)) i j :=
    congrFun (congrFun (Matrix.map_one (cA σ) (map_zero _) (map_one _)) i) j
  have h2 : (cA σ) (flipM (F := F) (E := E) d i j) = flipM d i j := congrFun (congrFun (flipM_map σ d) i) j
  simp only [flipAt, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_smul, h1, h2]

theorem flipAt_unitary (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) :
    (flipAt (E := E) v d)ᵀ * dbl (incM F W.J) * (flipAt v d).map (cA σ) = dbl (incM F W.J) := by
  rw [flipAt_transpose, flipAt_map, flipAt, idem_sandwich (idem_mul_self v), flipM_dbl, ← add_smul, sub_add_cancel,
    one_smul]

def flipPt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : UD σ W :=
  ⟨⟨flipAt v d, flipAt v d, flipAt_mul_self v d, flipAt_mul_self v d⟩, flipAt_unitary σ W v⟩

theorem matD_flipPt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : matD (flipPt σ W v) = flipAt v d := rfl

theorem matD_flipPt_inv (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) :
    matD (flipPt σ W v)⁻¹ = flipAt v d := rfl

theorem matD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g h : UD σ W) : matD (g * h) = matD g * matD h := rfl

theorem matD_inv_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : matD g⁻¹ * matD g = 1 := by
  exact congrArg Units.val (inv_mul_cancel (g : GL (Fin d ⊕ Fin d) (AE F E)))

theorem mul_mem_KD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {g h : UD σ W} (hg : g ∈ KD σ W v)
    (hh : h ∈ KD σ W v) : g * h ∈ KD σ W v := by
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · have e1 : matD (g * h) - 1 = (matD g - 1) * matD h + (matD h - 1) := by
      rw [matD_mul, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e1, smul_add, ← Matrix.smul_mul, hg.1 x hx, hh.1 x hx, Matrix.zero_mul, add_zero]
  · have e2 : matD (g * h)⁻¹ = matD h⁻¹ * matD g⁻¹ := by rw [_root_.mul_inv_rev, matD_mul]
    rw [matD_mul, ← Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 z hz).1).1, (hh.2 _ (hg.2 z hz).2).2⟩

theorem inv_mem_KD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {g : UD σ W} (hg : g ∈ KD σ W v) :
    g⁻¹ ∈ KD σ W v := by
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · have e1 : matD g⁻¹ - 1 = -(matD g⁻¹ * (matD g - 1)) := by
      rw [Matrix.mul_sub, matD_inv_mul, Matrix.mul_one, neg_sub]
    rw [e1, smul_neg, ← Matrix.mul_smul, hg.1 x hx, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]
    exact ⟨(hg.2 z hz).2, (hg.2 z hz).1⟩

theorem idem_smul_mem_latAt {d : ℕ} (W : Spc F E d) (v : Pl F) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : (GlobalTheory.LatVac.liftV v 1 : AF F) • y ∈ GlobalTheory.InertSph.latAt W v := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1 * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul]
      exact hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem flipAt_mulVec_inl (v : Pl F) {d : ℕ} (z : Fin d ⊕ Fin d → AE F E) (i : Fin d) :
    (flipAt v d *ᵥ z) (Sum.inl i) = z (Sum.inl i) := by
  simp [flipAt, flipM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, smul_mul_assoc, neg_mul, Finset.sum_neg_distrib]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem flipAt_mulVec_inr (v : Pl F) {d : ℕ} (z : Fin d ⊕ Fin d → AE F E) (i : Fin d) :
    (flipAt v d *ᵥ z) (Sum.inr i) =
      z (Sum.inr i) - (GlobalTheory.LatVac.liftV v 1 : AF F) • z (Sum.inr i) - (GlobalTheory.LatVac.liftV v 1 : AF F) • z (Sum.inr i) := by
  simp [flipAt, flipM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, smul_mul_assoc, neg_mul, Finset.sum_neg_distrib]
  rw [sub_smul, one_smul]; abel

theorem flipAt_mulVec_mem_latD (v : Pl F) {d : ℕ} (W : Spc F E d) {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) :
    flipAt v d *ᵥ z ∈ latD W v := by
  have hl : (flipAt v d *ᵥ z) ∘ Sum.inl = z ∘ Sum.inl := funext (flipAt_mulVec_inl v z)
  have hr : (flipAt v d *ᵥ z) ∘ Sum.inr = z ∘ Sum.inr - (GlobalTheory.LatVac.liftV v 1 : AF F) • (z ∘ Sum.inr) -
      (GlobalTheory.LatVac.liftV v 1 : AF F) • (z ∘ Sum.inr) := funext fun i => by
    simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, flipAt_mulVec_inr]
  have h2 := idem_smul_mem_latAt W v hz.2
  refine ⟨?_, ?_⟩
  · rw [hl]; exact hz.1
  · rw [hr]; exact sub_mem (sub_mem hz.2 h2) h2

theorem flipPt_mem_KD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : flipPt σ W v ∈ KD σ W v := by
  refine ⟨fun x hx => ?_, fun z hz => ⟨flipAt_mulVec_mem_latD v W hz, flipAt_mulVec_mem_latD v W hz⟩⟩
  have e1 : matD (flipPt σ W v) - 1 = (GlobalTheory.LatVac.liftV v 1 : AF F) • (flipM d - 1) := by
    rw [matD_flipPt, flipAt, smul_sub, sub_smul, one_smul]; abel
  rw [e1, smul_smul, mul_idem_eq_zero v hx, zero_smul]

theorem flipPt_conj_anti_diag : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d)
    (v : Pl F), ∃ w₀ ∈ GlobalTheory.DblVac.KD σ W v, ∀ q ∈ GlobalTheory.DblVac.KD σ W v, q ∈ GlobalTheory.DblVac.PAnti σ W →
      w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.KD σ W v ∧ w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.PDiag σ W := by
  intro F E _ _ _ _ _ σ d W v
  have hw := flipPt_mem_KD σ W v
  refine ⟨flipPt σ W v, hw, fun q hq hqa => ⟨mul_mem_KD (mul_mem_KD hw hq) (inv_mem_KD hw), ?_⟩⟩
  obtain ⟨T, hT⟩ := hqa
  have he := idem_mul_self (F := F) v
  have hQ : (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • matD q =
      (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
    have h0 := hq.1 (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rwa [smul_sub, sub_eq_zero] at h0
  refine ⟨⟨(1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d) (Fin d) (AE F E)) +
      (GlobalTheory.LatVac.liftV v 1 : AF F) • (T : Matrix (Fin d) (Fin d) (AE F E)),
    (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d) (Fin d) (AE F E)) +
      (GlobalTheory.LatVac.liftV v 1 : AF F) • ((T⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)),
    idem_unit he _ _ (Units.mul_inv T), idem_unit he _ _ (Units.inv_mul T)⟩, ?_⟩
  show (flipAt v d * matD q * flipAt v d) ⬝ₘ diagCols (Fin d) = diagCols (Fin d) ⬝ₘ
    ((1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d) (Fin d) (AE F E)) +
      (GlobalTheory.LatVac.liftV v 1 : AF F) • (T : Matrix (Fin d) (Fin d) (AE F E)))
  exact idem_conj_cols he (flipM d) (matD q) _ _ _ (flipM_diagCols d) (flipM_antiCols d) hQ hT

end GlobalTheory.DblVacFlip
