import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.CayleyOrd

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem intMat_mul' {α β γ : Type} [Fintype β] {x : Matrix α β L} {y : Matrix β γ L}
    (hx : x ∈ intMat L α β) (hy : y ∈ intMat L β γ) : x * y ∈ intMat L α γ := fun i j =>
  Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hx i k) (hy k j)

theorem intMat_one' {α : Type} [DecidableEq α] : (1 : Matrix α α L) ∈ intMat L α α := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem det_mem' {n : ℕ} {x : Matrix (Fin n) (Fin n) L} (hx : x ∈ intMat L (Fin n) (Fin n)) :
    x.det ∈ Formalism.UG.intL L := by
  have : x = (Formalism.UG.intL L).subtype.mapMatrix (Matrix.of fun i j => (⟨x i j, hx i j⟩ : Formalism.UG.intL L)) := by
    ext i j; rfl
  rw [this, ← RingHom.map_det]; exact SetLike.coe_mem _

theorem v_det_eq_one {n : ℕ} {x y : Matrix (Fin n) (Fin n) L} (hx : x ∈ intMat L (Fin n) (Fin n))
    (hy : y ∈ intMat L (Fin n) (Fin n)) (h : x * y = 1) : Valued.v x.det = 1 := by
  have h1 : Valued.v x.det * Valued.v y.det = 1 := by rw [← map_mul, ← Matrix.det_mul, h, Matrix.det_one, map_one]
  have ha : Valued.v x.det ≤ 1 := GlobalTheory.SphTheta.mem_intL.1 (det_mem' hx)
  have hb : Valued.v y.det ≤ 1 := GlobalTheory.SphTheta.mem_intL.1 (det_mem' hy)
  refine le_antisymm ha ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
    _ ≤ Valued.v x.det * 1 := by gcongr
    _ = _ := mul_one _

theorem ku_int {σ : L →+* L} {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) : k.1.1 ∈ intMat L (Fin n) (Fin n) := by
  obtain ⟨m, hm⟩ := (Subgroup.mem_subgroupOf.1 hk).2
  intro i j
  rw [← hm]; exact (m.1 i j).2

theorem zpow_int {ϖ : L} (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (m : ℤ) (hm : 0 ≤ m) : ϖ ^ m ∈ Formalism.UG.intL L := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [zpow_natCast]
  refine Subring.pow_mem _ (GlobalTheory.SphTheta.mem_intL.2 ?_) k
  rw [hv]; exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)

theorem v_zpow {ϖ : L} (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (m : ℤ) : Valued.v (ϖ ^ m) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, hv, ← WithZero.coe_zpow, ← ofAdd_zsmul]; congr 2; simp

end GlobalTheory.ChainOnto.CayleyOrd

namespace GlobalTheory.ChainOnto

open GlobalTheory.ChainOnto.CayleyOrd in

theorem ordL_det_one_add_of_inv_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (g t : GU σ n) (d : Fin n → ℤ), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU σ n, ∀ k₂ ∈ KU σ n, g⁻¹ = k₁ * t * k₂ → (1 + g.1.1).det ≠ 0 → (1 + g.1.1)⁻¹ ∈ intMat L (Fin n) (Fin n) → ordL (1 + g.1.1).det = -∑ i, max (d i) 0 := by
  intro L _ _ _ ϖ σ q hU n g t d ht k₁ hk₁ k₂ hk₂ hg hdet hc
  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := hU.2.2.2.1
  have hϖ : ϖ ≠ 0 := by intro h; rw [h, map_zero] at hv; exact WithZero.zero_ne_coe hv
  have hK1 := ku_int hk₁
  have hK1i := ku_int (inv_mem hk₁)
  have hK2 := ku_int hk₂
  have hK2i := ku_int (inv_mem hk₂)
  have e1 : k₁.1.1 * (k₁⁻¹).1.1 = 1 := by
    rw [show k₁.1.1 * (k₁⁻¹).1.1 = (k₁ * k₁⁻¹).1.1 from rfl, mul_inv_cancel]; rfl
  have e1' : (k₁⁻¹).1.1 * k₁.1.1 = 1 := by
    rw [show (k₁⁻¹).1.1 * k₁.1.1 = (k₁⁻¹ * k₁).1.1 from rfl, inv_mul_cancel]; rfl
  have e2 : k₂.1.1 * (k₂⁻¹).1.1 = 1 := by
    rw [show k₂.1.1 * (k₂⁻¹).1.1 = (k₂ * k₂⁻¹).1.1 from rfl, mul_inv_cancel]; rfl
  have eg : g.1.1 * (g⁻¹).1.1 = 1 := by
    rw [show g.1.1 * (g⁻¹).1.1 = (g * g⁻¹).1.1 from rfl, mul_inv_cancel]; rfl
  have hgi : (g⁻¹).1.1 = k₁.1.1 * t.1.1 * k₂.1.1 := by rw [hg]; rfl
  set Ti : Matrix (Fin n) (Fin n) L := Matrix.diagonal fun i => ϖ ^ (-d i) with hTi
  have eT : t.1.1 * Ti = 1 := by
    rw [ht, hTi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  have hG : g.1.1 = (k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1 := by
    have X : (k₁.1.1 * t.1.1 * k₂.1.1) * ((k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1) = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc k₂.1.1, e2, Matrix.one_mul, ← Matrix.mul_assoc t.1.1, eT, Matrix.one_mul, e1]
    calc g.1.1 = g.1.1 * ((k₁.1.1 * t.1.1 * k₂.1.1) * ((k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1)) := by rw [X, Matrix.mul_one]
      _ = (g.1.1 * (g⁻¹).1.1) * ((k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1) := by rw [hgi]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [eg, Matrix.one_mul]
  have hu : IsUnit (1 + g.1.1).det := Ne.isUnit hdet
  have hCG : (1 + g.1.1)⁻¹ * (1 + g.1.1) = 1 := Matrix.nonsing_inv_mul _ hu
  have hGC : (1 + g.1.1) * (1 + g.1.1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hCG' : (1 + g.1.1)⁻¹ * g.1.1 = 1 - (1 + g.1.1)⁻¹ := by
    rw [Matrix.mul_add, Matrix.mul_one] at hCG; exact eq_sub_of_add_eq' hCG
  set D : Matrix (Fin n) (Fin n) L := Matrix.diagonal fun i => ϖ ^ max (d i) 0 with hD
  set Di : Matrix (Fin n) (Fin n) L := Matrix.diagonal fun i => ϖ ^ (-max (d i) 0) with hDi
  have eD : D * Di = 1 := by
    rw [hD, hDi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  have hyZ : (D * k₂.1.1 * (1 + g.1.1)) * ((1 + g.1.1)⁻¹ * (k₂⁻¹).1.1 * Di) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 + g.1.1), hGC, Matrix.one_mul, ← Matrix.mul_assoc k₂.1.1, e2, Matrix.one_mul, eD]
  have hDint : D ∈ intMat L (Fin n) (Fin n) := fun i j => by
    rw [hD, Matrix.diagonal_apply]; split_ifs
    · exact zpow_int hv _ (le_max_right _ _)
    · exact Subring.zero_mem _
  have hy : D * k₂.1.1 * (1 + g.1.1) ∈ intMat L (Fin n) (Fin n) := by
    have : D * k₂.1.1 * (1 + g.1.1) = D * k₂.1.1 + (D * Ti) * (k₁⁻¹).1.1 := by
      rw [Matrix.mul_add, Matrix.mul_one, hG]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc k₂.1.1, e2, Matrix.one_mul]
    rw [this]
    refine add_mem (intMat_mul' hDint hK2) (intMat_mul' ?_ hK1i)
    intro i j
    rw [hD, hTi, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]; split_ifs
    · rw [← zpow_add₀ hϖ]; exact zpow_int hv _ (by omega)
    · exact Subring.zero_mem _
  have hCK : (1 + g.1.1)⁻¹ * (k₂⁻¹).1.1 * Ti = (1 - (1 + g.1.1)⁻¹) * k₁.1.1 := by
    rw [← hCG', hG]; simp only [Matrix.mul_assoc]; rw [e1', Matrix.mul_one]
  have hZ : (1 + g.1.1)⁻¹ * (k₂⁻¹).1.1 * Di ∈ intMat L (Fin n) (Fin n) := by
    intro i j
    rw [hDi, Matrix.mul_diagonal]
    rcases le_or_gt (d j) 0 with h | h
    · rw [max_eq_right h, neg_zero, zpow_zero, mul_one]; exact intMat_mul' hc hK2i i j
    · rw [max_eq_left h.le]
      have := congrFun (congrFun hCK i) j
      rw [hTi, Matrix.mul_diagonal] at this
      rw [this]
      exact intMat_mul' (sub_mem intMat_one' hc) hK1 i j
  have vy := v_det_eq_one hy hZ hyZ
  have vK := v_det_eq_one hK2 hK2i e2
  rw [Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, vK, mul_one, hD, Matrix.det_diagonal, map_prod] at vy
  simp only [v_zpow hv] at vy
  have hP : ∀ s : Finset (Fin n), ∏ i ∈ s, (((Multiplicative.ofAdd (-max (d i) 0) : Multiplicative ℤ)) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-∑ i ∈ s, max (d i) 0) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← WithZero.coe_mul, ← ofAdd_add, neg_add]
  rw [hP] at vy
  have vX : Valued.v (1 + g.1.1).det = ((Multiplicative.ofAdd (∑ i, max (d i) 0) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [eq_inv_of_mul_eq_one_right vy, ← WithZero.coe_inv, ← ofAdd_neg, neg_neg]
  have h0 : Valued.v (1 + g.1.1).det ≠ 0 := by rw [vX]; exact WithZero.coe_ne_zero
  unfold ordL
  rw [dif_neg h0]
  have hu : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (∑ i, max (d i) 0) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    (WithZero.coe_unzero h0).trans vX
  rw [WithZero.coe_injective hu, toAdd_ofAdd]

end GlobalTheory.ChainOnto
