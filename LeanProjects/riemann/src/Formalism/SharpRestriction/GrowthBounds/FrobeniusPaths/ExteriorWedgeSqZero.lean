import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section LamSec

variable {k : ℕ} {A : Type*} [CommRing A]

def Wop (x : Fin k → A) : Module.End A (Finset (Fin k) → A) := ∑ a, x a • exteriorWedge A a

def Iop (y : Fin k → A) : Module.End A (Finset (Fin k) → A) := ∑ a, y a • exteriorContraction A a

lemma Wop_apply (x : Fin k → A) (K : Finset (Fin k) → A) : Wop x K = wedgeR x K := by
  rw [right_wedge_eq_sum]
  simp [Wop]

lemma Iop_apply (y : Fin k → A) (K : Finset (Fin k) → A) : Iop y K = contrR y K := by
  rw [right_contraction_eq_sum]
  simp [Iop]

lemma exterior_wedge_sq_zero (a : Fin k) : exteriorWedge A a * exteriorWedge A a = 0 := by
  refine LinearMap.ext fun K => funext fun J => ?_
  simp [Module.End.mul_apply, exterior_wedge_apply]

lemma Wop_mul (x y : Fin k → A) : Wop x * Wop y = ∑ a, ∑ b, (x a * y b) • (exteriorWedge A a * exteriorWedge A b) := by
  unfold Wop
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul_comm]

lemma Wop_anti (x y : Fin k → A) : Wop x * Wop y = -(Wop y * Wop x) := by
  rw [Wop_mul, Wop_mul, ← Finset.sum_neg_distrib, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [wedge_anticommute, smul_neg, mul_comm (x b) (y a)]

lemma Wop_sq (x : Fin k → A) : Wop x * Wop x = 0 := by
  rw [Wop_mul, ← Fintype.sum_prod_type']
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ (fun _ _ => Finset.mem_univ _)
    (fun p _ => Prod.swap_swap p)
  · intro p _
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [wedge_anticommute p.2 p.1, smul_neg, mul_comm (x p.2) (x p.1), add_neg_cancel]
  · intro p _ hne heq
    apply hne
    have h12 : p.1 = p.2 := by
      have := congrArg Prod.fst heq
      simpa using this.symm
    rw [h12, exterior_wedge_sq_zero, smul_zero]

lemma WI_rel (x y : Fin k → A) : Wop x * Iop y + Iop y * Wop x = (∑ a, x a * y a) • 1 := by
  have h1 : Wop x * Iop y = ∑ a, ∑ b, (x a * y b) • (exteriorWedge A a * exteriorContraction A b) := by
    unfold Wop Iop
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_smul_comm]
  have h2 : Iop y * Wop x = ∑ a, ∑ b, (x a * y b) • (exteriorContraction A b * exteriorWedge A a) := by
    unfold Wop Iop
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_smul_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm (y b)]
  rw [h1, h2, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← smul_add, wedge_contraction_anticommute]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_smul]

lemma IW_apply (x y : Fin k → A) (v : Finset (Fin k) → A) :
    Iop y (Wop x v) = (∑ a, x a * y a) • v - Wop x (Iop y v) := by
  have h := congrArg (fun f => f v) (WI_rel x y)
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h
  rw [← h]
  abel

lemma Wop_vecMul (x : Fin k → A) (m : Matrix (Fin k) (Fin k) A) :
    Wop (Matrix.vecMul x m) = ∑ a, x a • Wop (m a) := by
  simp only [Wop, Matrix.vecMul, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

lemma w_eq_Wop (b : Fin k) : exteriorWedge A b = Wop (Pi.single b 1) := by
  simp [Wop, Pi.single_apply, ite_smul]

lemma single_vecMul' (b : Fin k) (m : Matrix (Fin k) (Fin k) A) : Matrix.vecMul (Pi.single b 1) m = m b := by
  funext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

def img (m : Matrix (Fin k) (Fin k) A) (I : Finset (Fin k)) : Finset (Fin k) → A :=
  if h : I.Nonempty then wedgeR (m (I.max' h)) (img m (I.erase (I.max' h))) else extOne
termination_by I.card
decreasing_by exact Finset.card_erase_lt_of_mem (Finset.max'_mem _ _)

lemma img_empty (m : Matrix (Fin k) (Fin k) A) : img m ∅ = extOne := by
  rw [img, dif_neg Finset.not_nonempty_empty]

lemma img_insert_max (m : Matrix (Fin k) (Fin k) A) (b : Fin k) (I : Finset (Fin k)) (hb : ∀ x ∈ I, x < b) :
    img m (insert b I) = wedgeR (m b) (img m I) := by
  have hbI : b ∉ I := fun h => lt_irrefl b (hb b h)
  have hmax : (insert b I).max' (Finset.insert_nonempty b I) = b := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact le_rfl
      · exact (hb y hy).le
    · exact Finset.le_max' _ _ (Finset.mem_insert_self b I)
  rw [img, dif_pos (Finset.insert_nonempty b I)]
  simp only [hmax, Finset.erase_insert hbI]

lemma sg_top (a : Fin k) (I : Finset (Fin k)) (hb : ∀ x ∈ I, x < a) : exteriorSign A (insert a I) a = 1 := by
  unfold exteriorSign
  rw [Finset.filter_eq_empty_iff.2]
  · simp
  · intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact lt_irrefl _
    · exact not_lt.2 (hb j hj).le

lemma img_wedge (m : Matrix (Fin k) (Fin k) A) (I : Finset (Fin k)) :
    ∀ a, (a ∈ I → Wop (m a) (img m I) = 0) ∧
      (a ∉ I → Wop (m a) (img m I) = exteriorSign A (insert a I) a • img m (insert a I)) := by
  induction I using Finset.induction_on_max with
  | empty =>
    intro a
    refine ⟨fun h => by simp at h, fun _ => ?_⟩
    rw [sg_top a ∅ (by simp), one_smul, img_insert_max m a ∅ (by simp), Wop_apply]
  | insert b s hb ih =>
    have hbs : b ∉ s := fun h => lt_irrefl b (hb b h)
    have himg : img m (insert b s) = Wop (m b) (img m s) := by
      rw [img_insert_max m b s hb, Wop_apply]
    intro a
    have hanti : ∀ v, Wop (m a) (Wop (m b) v) = -(Wop (m b) (Wop (m a) v)) := fun v => by
      have h := congrArg (fun f => f v) (Wop_anti (m a) (m b))
      simpa only [Module.End.mul_apply, LinearMap.neg_apply] using h
    constructor
    · intro ha
      rcases Finset.mem_insert.1 ha with rfl | ha'
      · rw [himg]
        have h := congrArg (fun f => f (img m s)) (Wop_sq (m a))
        simpa only [Module.End.mul_apply, LinearMap.zero_apply] using h
      · rw [himg, hanti, (ih a).1 ha', map_zero, neg_zero]
    · intro ha
      have hab : a ≠ b := fun h => ha (h ▸ Finset.mem_insert_self b s)
      have has : a ∉ s := fun h => ha (Finset.mem_insert_of_mem h)
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · have hins : ∀ x ∈ insert a s, x < b := by
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hlt
          · exact hb x hx
        have hba : b ∉ insert a s := by simp [Ne.symm hab, hbs]
        rw [himg, hanti, (ih a).2 has, map_smul, Wop_apply, ← img_insert_max m b (insert a s) hins,
          Finset.insert_comm a b s, exterior_sign_insert b a (insert a s), if_pos ⟨hba, hlt⟩, neg_one_mul, neg_smul]
      · have hins : ∀ x ∈ insert b s, x < a := by
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hgt
          · exact (hb x hx).trans hgt
        rw [sg_top a (insert b s) hins, one_smul, img_insert_max m a (insert b s) hins, Wop_apply]

def LamL (m : Matrix (Fin k) (Fin k) A) : Module.End A (Finset (Fin k) → A) :=
  ∑ I, (LinearMap.proj I : (Finset (Fin k) → A) →ₗ[A] A).smulRight (img m I)

lemma LamL_apply (m : Matrix (Fin k) (Fin k) A) (K : Finset (Fin k) → A) : LamL m K = ∑ I, K I • img m I := by
  simp [LamL]

def abelian₂ (m : Matrix (Fin k) (Fin k) A) : Matrix (Finset (Fin k)) (Finset (Fin k)) A := fun I J => img m I J

lemma vecMul_Lam (K : Finset (Fin k) → A) (m : Matrix (Fin k) (Fin k) A) : Matrix.vecMul K (abelian₂ m) = LamL m K := by
  funext J
  rw [LamL_apply]
  simp [Matrix.vecMul, dotProduct, abelian₂, Finset.sum_apply]

lemma LamL_single (m : Matrix (Fin k) (Fin k) A) (I : Finset (Fin k)) (c : A) :
    LamL m (Pi.single I c) = c • img m I := by
  rw [LamL_apply]
  simp [Pi.single_apply, ite_smul]

lemma w_single (a : Fin k) (I : Finset (Fin k)) (c : A) :
    exteriorWedge A a (Pi.single I c) = if a ∈ I then 0 else Pi.single (insert a I) (exteriorSign A (insert a I) a * c) := by
  funext J
  rw [exterior_wedge_apply]
  by_cases haI : a ∈ I
  · rw [if_pos haI, Pi.zero_apply]
    split_ifs with haJ
    · rw [Pi.single_apply, if_neg (fun h => by rw [← h] at haI; simp at haI), mul_zero]
    · rfl
  · rw [if_neg haI]
    by_cases haJ : a ∈ J
    · rw [if_pos haJ]
      by_cases hJ : J = insert a I
      · subst hJ
        rw [Finset.erase_insert haI]
        simp [Pi.single_apply]
      · have hne : J.erase a ≠ I := fun h => hJ (by rw [← h, Finset.insert_erase haJ])
        rw [Pi.single_apply, if_neg hne, Pi.single_apply, if_neg hJ, mul_zero]
    · rw [if_neg haJ, Pi.single_apply, if_neg (fun (h : J = insert a I) => haJ (h ▸ Finset.mem_insert_self a I))]

lemma LamL_w_single (m : Matrix (Fin k) (Fin k) A) (a : Fin k) (I : Finset (Fin k)) (c : A) :
    LamL m (exteriorWedge A a (Pi.single I c)) = c • Wop (m a) (img m I) := by
  rw [w_single]
  split_ifs with ha
  · rw [map_zero, (img_wedge m I a).1 ha, smul_zero]
  · rw [LamL_single, (img_wedge m I a).2 ha, smul_smul, mul_comm]

lemma LamL_Wop (m : Matrix (Fin k) (Fin k) A) (x : Fin k → A) :
    LamL m * Wop x = Wop (Matrix.vecMul x m) * LamL m := by
  apply LinearMap.pi_ext
  intro I c
  simp only [Module.End.mul_apply]
  have e : Wop x (Pi.single I c) = ∑ a, x a • exteriorWedge A a (Pi.single I c) := by simp [Wop]
  rw [e, map_sum]
  simp only [map_smul, LamL_w_single]
  rw [LamL_single, map_smul, Wop_vecMul]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => smul_comm _ _ _

lemma LamL_Wop_apply (m : Matrix (Fin k) (Fin k) A) (x : Fin k → A) (v : Finset (Fin k) → A) :
    LamL m (Wop x v) = Wop (Matrix.vecMul x m) (LamL m v) := by
  have h := congrArg (fun f => f v) (LamL_Wop m x)
  simpa only [Module.End.mul_apply] using h

theorem Lam_wedge (m : Matrix (Fin k) (Fin k) A) (x : Fin k → A) (K : Finset (Fin k) → A) :
    Matrix.vecMul (wedgeR x K) (abelian₂ m) = wedgeR (Matrix.vecMul x m) (Matrix.vecMul K (abelian₂ m)) := by
  rw [vecMul_Lam, vecMul_Lam, ← Wop_apply, ← Wop_apply, LamL_Wop_apply]

lemma extOne_eq : (extOne : Finset (Fin k) → A) = Pi.single ∅ 1 := by
  funext J
  simp [extOne, Pi.single_apply]

lemma single_insert_max (b : Fin k) (I : Finset (Fin k)) (hb : ∀ x ∈ I, x < b) (c : A) :
    (Pi.single (insert b I) c : Finset (Fin k) → A) = Wop (Pi.single b 1) (Pi.single I c) := by
  rw [← w_eq_Wop, w_single, if_neg (fun h => lt_irrefl b (hb b h)), sg_top b I hb, one_mul]

lemma img_one (I : Finset (Fin k)) : img (1 : Matrix (Fin k) (Fin k) A) I = Pi.single I 1 := by
  induction I using Finset.induction_on_max with
  | empty => rw [img_empty, extOne_eq]
  | insert b s hb ih =>
    have hrow : (1 : Matrix (Fin k) (Fin k) A) b = Pi.single b 1 := by
      funext j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [img_insert_max 1 b s hb, ih, ← Wop_apply, hrow, ← single_insert_max b s hb 1]

theorem Lam_one : abelian₂ (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  ext I J
  simp [abelian₂, img_one, Pi.single_apply, Matrix.one_apply, eq_comm]

lemma img_mul (m m' : Matrix (Fin k) (Fin k) A) (I : Finset (Fin k)) : img (m * m') I = LamL m' (img m I) := by
  induction I using Finset.induction_on_max with
  | empty =>
    have hL : LamL m' (extOne : Finset (Fin k) → A) = extOne := by
      rw [extOne_eq, LamL_single, one_smul, img_empty, extOne_eq]
    rw [img_empty, img_empty, hL]
  | insert b s hb ih =>
    have hrow : (m * m') b = Matrix.vecMul (m b) m' := by
      funext j
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [img_insert_max (m * m') b s hb, ih, img_insert_max m b s hb, ← Wop_apply, ← Wop_apply,
      LamL_Wop_apply, hrow]

theorem Lam_mul (m m' : Matrix (Fin k) (Fin k) A) : abelian₂ (m * m') = abelian₂ m * abelian₂ m' := by
  ext I J
  rw [Matrix.mul_apply]
  show img (m * m') I J = _
  rw [img_mul, ← vecMul_Lam]
  simp [Matrix.vecMul, dotProduct, abelian₂]

lemma Iop_extOne (y : Fin k → A) : Iop y (extOne : Finset (Fin k) → A) = 0 := by
  rw [Iop_apply]
  funext J
  simp [contrR, extOne]

lemma LamL_Iop_single (m m' : Matrix (Fin k) (Fin k) A) (h : m * m' = 1) (y : Fin k → A) (I : Finset (Fin k)) :
    ∀ c : A, LamL m (Iop y (Pi.single I c)) = Iop (Matrix.mulVec m' y) (LamL m (Pi.single I c)) := by
  induction I using Finset.induction_on_max with
  | empty =>
    intro c
    have e : (Pi.single ∅ c : Finset (Fin k) → A) = c • extOne := by
      funext J
      simp [Pi.single_apply, extOne]
    have hL : LamL m (extOne : Finset (Fin k) → A) = extOne := by
      rw [extOne_eq, LamL_single, one_smul, img_empty, extOne_eq]
    simp only [e, map_smul, Iop_extOne, smul_zero, map_zero, hL]
  | insert b s hb ih =>
    intro c
    have hrow : Matrix.vecMul (Pi.single b 1) m = m b := single_vecMul' b m
    have hyb : ∑ a, (Pi.single b (1 : A) : Fin k → A) a * y a = y b := by simp [Pi.single_apply]
    have hmy : ∑ a, m b a * Matrix.mulVec m' y a = y b := by
      have h2 : Matrix.mulVec m (Matrix.mulVec m' y) = y := by
        rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
      have := congrFun h2 b
      simpa [Matrix.mulVec, dotProduct] using this
    rw [single_insert_max b s hb c, IW_apply, hyb, map_sub, map_smul, LamL_Wop_apply, hrow, ih c,
      LamL_Wop_apply, hrow, IW_apply, hmy]

theorem Lam_contr (m m' : Matrix (Fin k) (Fin k) A) (h : m * m' = 1) (y : Fin k → A) (K : Finset (Fin k) → A) :
    Matrix.vecMul (contrR y K) (abelian₂ m) = contrR (Matrix.mulVec m' y) (Matrix.vecMul K (abelian₂ m)) := by
  rw [vecMul_Lam, vecMul_Lam, ← Iop_apply, ← Iop_apply]
  have hK : K = ∑ I, Pi.single I (K I) := (Finset.univ_sum_single K).symm
  rw [hK]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun I _ => LamL_Iop_single m m' h y I (K I)

theorem Lam_empty (m : Matrix (Fin k) (Fin k) A) (J : Finset (Fin k)) (hJ : J ≠ ∅) : abelian₂ m ∅ J = 0 := by
  simp [abelian₂, img_empty, extOne, hJ]

theorem Lam_empty_self (m : Matrix (Fin k) (Fin k) A) : abelian₂ m ∅ ∅ = 1 := by
  simp [abelian₂, img_empty, extOne]

theorem Lam_card (m : Matrix (Fin k) (Fin k) A) (I J : Finset (Fin k)) (h : I.card ≠ J.card) : abelian₂ m I J = 0 := by
  have key : ∀ (I J : Finset (Fin k)), J.card ≠ I.card → img m I J = 0 := by
    intro I
    induction I using Finset.induction_on_max with
    | empty =>
      intro J hJ
      rw [img_empty]
      simp only [extOne]
      rw [if_neg]
      intro h
      apply hJ
      simp [h]
    | insert b s hb ih =>
      intro J hJ
      have hbs : b ∉ s := fun h => lt_irrefl b (hb b h)
      rw [img_insert_max m b s hb]
      simp only [wedgeR]
      apply Finset.sum_eq_zero
      intro a ha
      rw [ih (J.erase a) ?_, mul_zero]
      rw [Finset.card_erase_of_mem ha]
      rw [Finset.card_insert_eq_ite, if_neg hbs] at hJ
      have := Finset.card_pos.2 ⟨a, ha⟩
      omega
  exact key I J (Ne.symm h)

theorem Lam_map {A' : Type*} [CommRing A'] (φ : A →+* A') (m : Matrix (Fin k) (Fin k) A) :
    (abelian₂ m).map φ = abelian₂ (m.map φ) := by
  have key : ∀ (I J : Finset (Fin k)), φ (img m I J) = img (m.map φ) I J := by
    intro I
    induction I using Finset.induction_on_max with
    | empty =>
      intro J
      simp only [img_empty, extOne]
      split_ifs <;> simp
    | insert b s hb ih =>
      intro J
      simp only [img_insert_max m b s hb, img_insert_max (m.map φ) b s hb, wedgeR, map_sum, map_mul,
        map_pow, map_neg, map_one, ih, Matrix.map_apply]
  ext I J
  simp [Matrix.map_apply, abelian₂, key]

end LamSec

end Formalism.MainNotions.LemmaBAlt
