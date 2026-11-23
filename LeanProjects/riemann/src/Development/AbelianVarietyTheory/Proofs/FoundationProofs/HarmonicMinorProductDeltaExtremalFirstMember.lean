import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FockSingularValues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivationProdPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockMinorExtremal

open MvPolynomial GlobalTheory.JointHarm GlobalTheory.JointHarm.Minor GlobalTheory.Capelli

section General

variable {A : Type} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A) {n l : ℕ}
  (y : Matrix (Fin n) (Fin l) A)

theorem der_minor {a b : Fin l} (hab : a ≤ b) (hD : ∀ c k, D (y c k) = if k = b then y c a else 0)
    {m : ℕ} (row : Fin m → Fin n) (h : m ≤ l) :
    D (y.submatrix row (Fin.castLE h)).det =
      (if a = b then (if a.1 < m then (1 : ℂ) else 0) else 0) • (y.submatrix row (Fin.castLE h)).det := by
  rw [← Matrix.det_transpose, derivation_det]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, hD]
  by_cases hb : b.1 < m
  · rw [Finset.sum_eq_single (⟨b.1, hb⟩ : Fin m)]
    · have e : Fin.castLE h ⟨b.1, hb⟩ = b := rfl
      simp only [e, if_true]
      split_ifs with h1 h2
      · subst h1
        rw [one_smul]
        congr 1
        exact Matrix.updateRow_eq_self _ _
      · exact absurd (h1 ▸ hb) h2
      · have hlt : a.1 < b.1 := lt_of_le_of_ne hab fun e => h1 (Fin.ext e)
        have hne : (⟨a.1, hlt.trans hb⟩ : Fin m) ≠ ⟨b.1, hb⟩ := fun e => by
          rw [Fin.ext_iff] at e; simp at e; omega
        rw [zero_smul]
        refine Matrix.det_zero_of_row_eq hne ?_
        rw [Matrix.updateRow_self, Matrix.updateRow_ne hne]
        rfl
    · intro i _ hi
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      rw [Matrix.updateRow_self, if_neg fun e : Fin.castLE h i = b => hi (Fin.ext (congrArg Fin.val e :))]
    · simp
  · have h0 : (if a = b then (if a.1 < m then (1 : ℂ) else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exact absurd (h1 ▸ h2) hb
      · rfl
      · rfl
    rw [h0, zero_smul]
    refine Finset.sum_eq_zero fun i _ => Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    rw [Matrix.updateRow_self, if_neg fun e : Fin.castLE h i = b => hb (e ▸ i.2)]

theorem sum_rows (α : Fin l → ℕ) (hα : Antitone α) (a : Fin l) :
    ∑ i : Fin l, ((α i - nextRow α i : ℕ) : ℂ) * (if a.1 < i.1 + 1 then 1 else 0) = α a := by
  let f : ℕ → ℕ := fun i => if h : i < l then α ⟨i, h⟩ else 0
  have hf : Antitone f := by
    refine antitone_nat_of_succ_le fun i => ?_
    simp only [f]
    split_ifs with h1 h2 h2
    · exact hα (by simp [Fin.le_def])
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have h := telescope f hf a l
  have hl : f l = 0 := by simp [f]
  rw [if_pos a.2.le, hl, ← Fin.sum_univ_eq_sum_range
    (fun i => ((f i - f (i + 1) : ℕ) : ℂ) * (if a.1 < i + 1 then 1 else 0))] at h
  have e1 : ∀ i : Fin l, f i = α i := fun i => by simp [f, i.2]
  have e2 : ∀ i : Fin l, f (i + 1) = nextRow α i := fun i => rfl
  simpa only [e1, e2, Nat.cast_zero, sub_zero] using h

theorem der_minorProd (α : Fin l → ℕ) (hα : Antitone α) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n)
    {a b : Fin l} (hab : a ≤ b) (hD : ∀ c k, D (y c k) = if k = b then y c a else 0) :
    D (minorProd α y row) = (if a = b then (α a : ℂ) else 0) • minorProd α y row := by
  rw [minorProd, derivation_prod_pow D _ _ _ _ fun i => der_minor D y hab hD (row i) i.2]
  congr 1
  split_ifs with h
  · exact sum_rows α hα a
  · simp

theorem der_minorProd_zero (α : Fin l → ℕ) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n)
    (hD : ∀ i c k, D (y (row i c) k) = 0) : D (minorProd α y row) = 0 := by
  rw [minorProd, derivation_prod_pow D _ _ _ (fun _ => 0) fun i => ?_]
  · simp
  · rw [zero_smul, derivation_det]
    refine Finset.sum_eq_zero fun j _ => Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [Matrix.updateRow_self, Matrix.submatrix_apply, hD]

end General

theorem minorProd_ne_zero {σ : Type} {n l : ℕ} (z : Fin n × Fin l → σ) (hz : Function.Injective z)
    (α : Fin l → ℕ) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n) (hrow : ∀ i, Function.Injective (row i)) :
    minorProd α (Matrix.of fun c k => (X (z (c, k)) : MvPolynomial σ ℂ)) row ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _
    (lead_ne_zero (fun w : Fin (i.1 + 1) × Fin l => z (row i w.1, w.2))
      (hz.comp ((hrow i).prodMap Function.injective_id)) le_rfl i.2)

variable {p q n : ℕ}

def vPlus (p q n : ℕ) : Fin p × Fin n → Ln p q n 0 := fun w => (.inl w.1, .inl w.2)

def vMinus (p q n : ℕ) : Fin q × Fin n → Ln p q n 0 := fun w => (.inr w.1, .inl w.2)

theorem vPlus_inj : Function.Injective (vPlus p q n) := fun u w h => by
  simpa [vPlus, Prod.ext_iff] using h

theorem vMinus_inj : Function.Injective (vMinus p q n) := fun u w h => by
  simpa [vMinus, Prod.ext_iff] using h

theorem act_plus (i j : Fin p) (P : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (.inl i) (.inl j)) P =
      rowDer (vPlus p q n) i j P + (if i = j then (n : ℂ) / 2 else 0) • P := by
  rw [isSide_one.1, mixedOp_apply, ← rowOp_eq_rowDer, rowOp_apply]
  simp [zA, vPlus, cPair]

theorem act_minus (i j : Fin q) (P : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (.inr j) (.inr i)) P =
      -rowDer (vMinus p q n) i j P - (if i = j then (n : ℂ) / 2 else 0) • P := by
  rw [isSide_one.2, mixedOp_apply, ← rowOp_eq_rowDer, rowOp_apply]
  simp [zD, vMinus, cPair, eq_comm]

theorem der_plus (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (hp : Antitone ap) {i j : Fin p}
    (hij : i ≤ j) :
    rowDer (vPlus p q n) i j (delta hn ap am) = (if i = j then (ap i : ℂ) else 0) • delta hn ap am := by
  rw [delta, Derivation.leibniz, der_minorProd _ (zPlus p q n) ap hp _ hij
    fun c k => rowDer_X _ vPlus_inj i j k c, der_minorProd_zero _ (zMinus p q n) am _ fun _ c k => ?_]
  · simp [mul_comm]
  · rw [← rowOp_eq_rowDer, rowOp_apply]
    simp [zMinus, vPlus, pderiv_X, Pi.single_apply]

theorem der_minus (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (hm : Antitone am) {i j : Fin q}
    (hij : i ≤ j) :
    rowDer (vMinus p q n) i j (delta hn ap am) = (if i = j then (am i : ℂ) else 0) • delta hn ap am := by
  rw [delta, Derivation.leibniz, der_minorProd _ (zMinus p q n) am hm _ hij
    fun c k => rowDer_X _ vMinus_inj i j k c, der_minorProd_zero _ (zPlus p q n) ap _ fun _ c k => ?_]
  · simp
  · rw [← rowOp_eq_rowDer, rowOp_apply]
    simp [zPlus, vMinus, pderiv_X, Pi.single_apply]

theorem lower (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) :
    KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  intro a b
  rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero, GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.lowerOp]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h1 : pderiv ((.inr b, .inl c) : Ln p q n 0) (minorProd ap (zPlus p q n) (topRows (by omega))) = 0 :=
    der_minorProd_zero _ _ _ _ fun _ _ _ => pderiv_X_of_ne (by simp)
  have h2 : pderiv ((.inl a, .inl c) : Ln p q n 0) (minorProd am (zMinus p q n) (botRows (by omega))) = 0 :=
    der_minorProd_zero _ _ _ _ fun _ _ _ => pderiv_X_of_ne (by simp)
  rw [delta, Derivation.leibniz, h1, smul_zero, add_zero, smul_eq_mul, Derivation.leibniz, pderiv_swap, h2,
    map_zero, smul_zero, zero_add, smul_eq_mul]
  by_cases hc : c.1 < p
  · rw [der_minorProd_zero (pderiv ((.inr b, .inl c) : Ln p q n 0)) (zMinus p q n) am (botRows (by omega))
      fun i d _ => pderiv_X_of_ne ?_,
      zero_mul]
    have := i.2
    simp only [botRows, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff]
    omega
  · rw [der_minorProd_zero (pderiv ((.inl a, .inl c) : Ln p q n 0)) (zPlus p q n) ap (topRows (by omega))
      fun i d _ => pderiv_X_of_ne ?_,
      mul_zero]
    have := i.2
    have := d.2
    simp only [topRows, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff]
    omega

theorem delta_extremal : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → delta hn ap am ≠ 0 ∧ delta hn ap am ∈ wtSub (fockAct1 p q n 0) (wtExt n ap am) ∧ (∀ i j : Fin p, i < j → fockAct1 p q n 0 (Eab (Sum.inl i) (Sum.inl j)) (delta hn ap am) = 0) ∧ (∀ i j : Fin q, i < j → fockAct1 p q n 0 (Eab (Sum.inr j) (Sum.inr i)) (delta hn ap am) = 0) ∧ KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  intro p q n hn ap am hp hm
  refine ⟨mul_ne_zero ?_ ?_, ?_, fun i j h => ?_, fun i j h => ?_, lower hn ap am⟩
  · exact minorProd_ne_zero (fun w => vPlus p q n w.swap) (vPlus_inj.comp Prod.swap_injective) ap _
      fun i c d h => by simpa [topRows, Fin.ext_iff] using h
  · exact minorProd_ne_zero (fun w => vMinus p q n w.swap) (vMinus_inj.comp Prod.swap_injective) am _
      fun i c d h => by simpa [botRows, Fin.ext_iff] using h
  · simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, Sum.forall, sub_eq_zero]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [act_plus, der_plus hn ap am hp le_rfl]
      simp [wtExt, add_smul]
    · rw [act_minus, der_minus hn ap am hm le_rfl]
      simp [wtExt, sub_smul]
  · rw [act_plus, der_plus hn ap am hp h.le]
    simp [h.ne]
  · rw [act_minus, der_minus hn ap am hm h.le]
    simp [h.ne]

end GlobalTheory.FockMinorExtremal

end
