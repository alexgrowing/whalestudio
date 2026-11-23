import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionActionOnFixK1
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperMulInc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelUniqueOfIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelOfParabolicVector
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp.ParInd

section Blocks
variable {R : Type} [CommRing R] {a b : ℕ}

theorem entN_tl (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin a) :
    entN M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_br (M : Matrix (Fin (a + b)) (Fin (a + b)) R) (i j : Fin b) :
    entN M (a + i) (a + j) = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [entN, hi, hj, and_self, dif_pos]
  rfl

theorem entN_self {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) : entN M i j = M i j := by
  simp [entN]

theorem det_par (M : Matrix (Fin (a + b)) (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0) :
    M.det = (Matrix.of fun i j : Fin a => entN M i j).det *
      (Matrix.of fun i j : Fin b => entN M (a + i) (a + j)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have h0 : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    apply h <;> simp
  rw [h0, Matrix.det_fromBlocks_zero₂₁]
  congr 2 <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, entN_tl, entN_br]

theorem exists_blocks (p : GL (Fin (a + b)) R)
    (h : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix _ _ R) i j = 0) :
    ∃ (x : GL (Fin a) R) (y : GL (Fin b) R),
      (∀ i j : Fin a, (x : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) i j) ∧
      (∀ i j : Fin b, (y : Matrix _ _ R) i j = entN (p : Matrix (Fin (a + b)) (Fin (a + b)) R) (a + i) (a + j)) := by
  have hu : IsUnit (p : Matrix (Fin (a + b)) (Fin (a + b)) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [det_par _ h] at hu
  have h1 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hu)
  have h2 := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hu)
  exact ⟨h1.unit, h2.unit, fun i j => by simp, fun i j => by simp⟩

def dg (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) : Matrix (Fin (a + b)) (Fin (a + b)) R :=
  fun i j => if (i : ℕ) < a ∧ (j : ℕ) < a then entN x i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then entN y (i - a) (j - a) else 0

theorem dg_par (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin (a + b))
    (hj : (j : ℕ) < a) (hi : a ≤ (i : ℕ)) : dg x y i j = 0 := by
  unfold dg
  rw [if_neg (by omega), if_neg (by omega)]

theorem dg_tl (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin a) :
    entN (dg x y) i j = x i j := by
  rw [entN_tl]
  simp [dg, entN_self]

theorem dg_br (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) (i j : Fin b) :
    entN (dg x y) (a + i) (a + j) = y i j := by
  rw [entN_br]
  simp [dg, entN_self]

theorem dg_det (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) :
    (dg x y).det = x.det * y.det := by
  rw [det_par _ (dg_par x y)]
  congr 2 <;> ext i j <;> simp [dg_tl, dg_br]

theorem dg_unit (x : GL (Fin a) R) (y : GL (Fin b) R) : IsUnit (dg x.val y.val) := by
  rw [Matrix.isUnit_iff_isUnit_det, dg_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit)

theorem dg_one : dg (1 : Matrix (Fin a) (Fin a) R) (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [← entN_tl (dg 1 1), dg_tl]; simp [Matrix.one_apply]
  · rw [Matrix.one_apply_ne (by intro h; have := congrArg Fin.val h; simp at this; omega)]
    simp [dg]
  · rw [Matrix.one_apply_ne (by intro h; have := congrArg Fin.val h; simp at this; omega)]
    simp [dg]
  · rw [← entN_br (dg 1 1), dg_br]; simp [Matrix.one_apply]

theorem entN_map {S : Type} [CommRing S] (f : R →+* S) {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : ℕ) :
    entN (M.map f) i j = f (entN M i j) := by
  unfold entN
  split_ifs <;> simp

theorem dg_map {S : Type} [CommRing S] (f : R →+* S) (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin b) (Fin b) R) :
    (dg x y).map f = dg (x.map f) (y.map f) := by
  ext i j
  simp only [dg, Matrix.map_apply, entN_map]
  split_ifs <;> simp

theorem mul_par (M N : Matrix (Fin (a + b)) (Fin (a + b)) R)
    (hM : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0)
    (hN : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → N i j = 0) (i j : Fin (a + b))
    (hj : (j : ℕ) < a) (hi : a ≤ (i : ℕ)) : (M * N) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < a
  · rw [hM i k hk hi, zero_mul]
  · rw [hN k j hj (by omega), mul_zero]

theorem mul_tl (M N : Matrix (Fin (a + b)) (Fin (a + b)) R)
    (hN : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → N i j = 0) (i j : Fin a) :
    entN (M * N) i j = ∑ k : Fin a, entN M i k * entN N k j := by
  simp only [entN_tl, Matrix.mul_apply, Fin.sum_univ_add]
  rw [Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin b))), add_zero]
  intro k _
  rw [hN _ _ (by simp) (by simp), mul_zero]

end Blocks

variable {g : ℕ} [Fact g.Prime] {a b : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem inc_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (inc g n k).val = k.val.map (algebraMap ℤ_[g] ℚ_[g]) := rfl

theorem red_val (n : ℕ) (k : GL (Fin n) ℤ_[g]) : (red g n k).val = k.val.map (PadicInt.toZMod (p := g)) := rfl

theorem det_inc (n : ℕ) (k : GL (Fin n) ℤ_[g]) : Matrix.GeneralLinearGroup.det (inc g n k) =
    Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, inc_val, Units.coe_map]
  exact ((algebraMap ℤ_[g] ℚ_[g]).map_det k.val).symm

theorem det_red (n : ℕ) (k : GL (Fin n) ℤ_[g]) : Matrix.GeneralLinearGroup.det (red g n k) =
    Units.map (PadicInt.toZMod (p := g)).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, red_val, Units.coe_map]
  exact ((PadicInt.toZMod (p := g)).map_det k.val).symm

theorem mem_principalCongruenceFixedVectors_iff {n : ℕ} (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (v : V) :
    v ∈ fixK1 π ↔ ∀ k, red g n k = 1 → π (inc g n k) v = v := by
  simp [fixK1, Submodule.mem_iInf, sub_eq_zero, MonoidHom.mem_ker]

theorem exists_par_lift {n : ℕ} (a : ℕ) (p : Gn g n) (hp : InPar a (p : Mt g n)) :
    ∃ k : GL (Fin n) ℤ_[g], red g n k = p ∧ ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → k.val i j = 0 := by
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := Matrix.of fun i j => ((p.val i j).val : ℤ_[g])
  have hM : M.map (PadicInt.toZMod (p := g)) = p.val := by
    ext i j
    simp [M]
  have hd : PadicInt.toZMod (p := g) M.det = p.val.det := by
    rw [RingHom.map_det, ← hM]; rfl
  have hu : IsUnit M.det := by
    by_contra hn
    have : M.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]; exact hn
    rw [RingHom.mem_ker, hd] at this
    exact ((Matrix.isUnit_iff_isUnit_det _).1 p.isUnit).ne_zero this
  have hu' := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨hu'.unit, ?_, fun i j hj hi => ?_⟩
  · ext1
    rw [red_val, IsUnit.unit_spec, hM]
  · rw [IsUnit.unit_spec]
    simp [M, hp i j hj hi]

def Eqv (π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V) (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W)
    (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W) : Prop :=
  ∀ (p : GL (Fin (a + b)) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
    (∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → p.val i j = 0) →
    (∀ i j : Fin a, x.val i j = entN p.val i j) →
    (∀ i j : Fin b, y.val i j = entN p.val (a + i) (a + j)) →
    ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
      σ x (Λ v)

variable {π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V} {σ : Representation ℂ (GL (Fin a) ℚ_[g]) W}
  {ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ} {Λ : V →ₗ[ℂ] W} {χ : (ZMod g)ˣ →* ℂˣ}

theorem eqv_int (hΛ : Eqv π σ ν₁ ν₂ Λ)
    (h1 : ∀ u : ℤ_[g]ˣ, ν₁ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1)
    (h2 : ∀ u : ℤ_[g]ˣ, ν₂ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) =
      χ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u))
    (k : GL (Fin (a + b)) ℤ_[g]) (x : GL (Fin a) ℤ_[g]) (y : GL (Fin b) ℤ_[g])
    (hk : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → k.val i j = 0)
    (hx : ∀ i j : Fin a, x.val i j = entN k.val i j)
    (hy : ∀ i j : Fin b, y.val i j = entN k.val (a + i) (a + j)) (v : V) :
    Λ (π (inc g _ k) v) = ((χ (Matrix.GeneralLinearGroup.det (red g b y)) : ℂˣ) : ℂ) • σ (inc g a x) (Λ v) := by
  rw [hΛ (inc g _ k) (inc g a x) (inc g b y), det_inc, det_inc, h1, h2, det_red, one_mul]
  · intro i j hj hi
    rw [inc_val, Matrix.map_apply, hk i j hj hi, map_zero]
  · intro i j
    rw [inc_val, inc_val, entN_map, Matrix.map_apply, hx]
  · intro i j
    rw [inc_val, inc_val, entN_map, Matrix.map_apply, hy]

theorem map_fix (hΛ : Eqv π σ ν₁ ν₂ Λ)
    (h1 : ∀ u : ℤ_[g]ˣ, ν₁ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1)
    (h2 : ∀ u : ℤ_[g]ˣ, ν₂ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) =
      χ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u))
    (v : V) (hv : v ∈ fixK1 π) : Λ v ∈ fixK1 σ := by
  rw [mem_principalCongruenceFixedVectors_iff] at hv ⊢
  intro x hx
  have hu := dg_unit x (1 : GL (Fin b) ℤ_[g])
  have h := eqv_int hΛ h1 h2 hu.unit x 1 (fun i j hj hi => by rw [IsUnit.unit_spec]; exact dg_par _ _ i j hj hi)
    (fun i j => by rw [IsUnit.unit_spec, dg_tl]) (fun i j => by rw [IsUnit.unit_spec, dg_br]) v
  rw [hv] at h
  · simpa using h.symm
  · ext1
    rw [red_val, IsUnit.unit_spec, dg_map, ← red_val, ← red_val, hx, map_one]
    exact dg_one

theorem eqv_fin (hΛ : Eqv π σ ν₁ ν₂ Λ)
    (h1 : ∀ u : ℤ_[g]ˣ, ν₁ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1)
    (h2 : ∀ u : ℤ_[g]ˣ, ν₂ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) =
      χ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u))
    (p : Gn g (a + b)) (x : Gn g a) (y : Gn g b) (hp : InPar a p.val)
    (hx : ∀ i j : Fin a, x.val i j = entN p.val i j)
    (hy : ∀ i j : Fin b, y.val i j = entN p.val (a + i) (a + j)) (v : V) (hv : v ∈ fixK1 π) :
    Λ (π (lift g _ p) v) = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • σ (lift g a x) (Λ v) := by
  obtain ⟨k, rfl, hk⟩ := exists_par_lift a p hp
  obtain ⟨x', y', hx', hy'⟩ := exists_blocks k hk
  have ex : red g a x' = x := by
    ext i j
    rw [hx, red_val, red_val, entN_map, Matrix.map_apply, hx']
  have ey : red g b y' = y := by
    ext i j
    rw [hy, red_val, red_val, entN_map, Matrix.map_apply, hy']
  rw [← ((GlobalTheory.GLp.finite_group_acts_on_fixK1 g _ V π).2 v hv).2.1, eqv_int hΛ h1 h2 k x' y' hk hx' hy', ey,
    ((GlobalTheory.GLp.finite_group_acts_on_fixK1 g _ W σ).2 _ (map_fix hΛ h1 h2 v hv)).2.1, ex]

theorem blk_val (x : Gn g a) (y : Gn g b) : (blk a b (a + b) x y).val = dg x.val y.val := by
  have hu := dg_unit x y
  change (toG (dg x.val y.val)).val = _
  rw [toG, dif_pos hu, IsUnit.unit_spec]

def InQ (a : ℕ) {n : ℕ} (p : Gn g n) : Prop := InPar a p.val ∧ tl a p.val = 1

theorem InQ.ent {p : Gn g (a + b)} (hp : InQ a p) (i j : Fin a) :
    entN p.val i j = (1 : Matrix (Fin a) (Fin a) (ZMod g)) i j := by
  rw [← hp.2]; rfl

theorem InQ.mul {p q : Gn g (a + b)} (hp : InQ a p) (hq : InQ a q) : InQ a (p * q) := by
  refine ⟨fun i j hj hi => mul_par _ _ hp.1 hq.1 i j hj hi, ?_⟩
  ext i j
  change entN (p.val * q.val) i j = _
  rw [mul_tl _ _ hq.1]
  simp only [hp.ent, hq.ent]
  rw [← Matrix.mul_apply, one_mul]

theorem InQ.det {p : Gn g (a + b)} (hp : InQ a p) (y : Gn g b)
    (hy : ∀ i j : Fin b, y.val i j = entN p.val (a + i) (a + j)) :
    Matrix.GeneralLinearGroup.det p = Matrix.GeneralLinearGroup.det y := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  rw [det_par _ hp.1]
  have e1 : (Matrix.of fun i j : Fin a => entN p.val i j) = 1 := by ext i j; exact hp.ent i j
  have e2 : (Matrix.of fun i j : Fin b => entN p.val (a + i) (a + j)) = y.val := by ext i j; exact (hy i j).symm
  rw [e1, e2, Matrix.det_one, one_mul]

theorem lift_one {n : ℕ} (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (v : V) (hv : v ∈ fixK1 π) :
    π (lift g n 1) v = v := by
  have := ((GlobalTheory.GLp.finite_group_acts_on_fixK1 g _ V π).2 v hv).2.1 1
  rw [map_one, map_one, map_one] at this
  exact this.symm

theorem exists_parVec (hΛ : Eqv π σ ν₁ ν₂ Λ)
    (h1 : ∀ u : ℤ_[g]ˣ, ν₁ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1)
    (h2 : ∀ u : ℤ_[g]ˣ, ν₂ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) =
      χ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u))
    (w : V) (hw : w ∈ fixK1 π) (hw0 : Λ w ≠ 0) : ∃ v, IsParVec π a b χ v ∧ Λ v ≠ 0 := by
  have hb := (GlobalTheory.GLp.finite_group_acts_on_fixK1 g _ V π).2 w hw
  let φ : Gn g (a + b) →* ℂ := (Units.coeHom ℂ).comp (χ.comp Matrix.GeneralLinearGroup.det)
  have hφ : ∀ p, φ p = ((χ (Matrix.GeneralLinearGroup.det p) : ℂˣ) : ℂ) := fun p => rfl
  have hφ0 : ∀ p, φ p ≠ 0 := fun p => by rw [hφ]; exact Units.ne_zero _
  let v : V := ∑ p : {p : Gn g (a + b) // InQ a p}, (φ p.1)⁻¹ • π (lift g _ p.1) w
  have hq : ∀ q : Gn g (a + b), InQ a q → π (lift g _ q) v = φ q • v := by
    intro q hq
    let m : {p : Gn g (a + b) // InQ a p} → {p : Gn g (a + b) // InQ a p} := fun p => ⟨q * p.1, hq.mul p.2⟩
    have hm : Function.Bijective m := Finite.injective_iff_bijective.1 fun p p' h =>
      Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
    have e : v = ∑ p : {p : Gn g (a + b) // InQ a p}, (φ (m p).1)⁻¹ • π (lift g _ (m p).1) w :=
      (hm.sum_comp (fun p => (φ p.1)⁻¹ • π (lift g _ p.1) w)).symm
    conv_rhs => rw [e]
    simp only [v, map_sum, map_smul, Finset.smul_sum, m, smul_smul, map_mul, hb.2.2.1]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    have := hφ0 q
    have := hφ0 p.1
    field_simp
  refine ⟨v, ⟨Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hb.1 _), fun u hu ht hr => ?_, fun y => ?_⟩, ?_⟩
  · rw [hq u ⟨hu, ht⟩, hφ, InQ.det ⟨hu, ht⟩ 1 (fun i j => by rw [Units.val_one, ← hr]; rfl)]
    simp
  · have hy : InQ a (blk a b (a + b) 1 y) := by
      refine ⟨fun i j hj hi => by rw [blk_val]; exact dg_par _ _ i j hj hi, ?_⟩
      ext i j
      rw [blk_val]
      exact dg_tl _ _ i j
    rw [hq _ hy, hφ, hy.det y (fun i j => by rw [blk_val, dg_br])]
  · have e : ∀ p : {p : Gn g (a + b) // InQ a p}, Λ ((φ p.1)⁻¹ • π (lift g _ p.1) w) = Λ w := by
      intro p
      obtain ⟨x, y, -, hy⟩ := exists_blocks p.1 p.2.1
      rw [map_smul, eqv_fin hΛ h1 h2 p.1 1 y p.2.1 (fun i j => (p.2.ent i j).symm) hy w hw,
        lift_one σ _ (map_fix hΛ h1 h2 w hw), smul_smul, ← p.2.det y hy, ← hφ, inv_mul_cancel₀ (hφ0 _), one_smul]
    have hne : Nonempty {p : Gn g (a + b) // InQ a p} := by
      refine ⟨⟨1, fun i j hj hi => ?_, ?_⟩⟩
      · rw [Units.val_one, ← dg_one]; exact dg_par _ _ i j hj hi
      · ext i j
        rw [Units.val_one, ← dg_one]; exact dg_tl _ _ i j
    simp only [v, map_sum, e, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
    refine smul_ne_zero ?_ hw0
    exact Nat.cast_ne_zero.2 (Finset.card_pos.2 Finset.univ_nonempty).ne'

end GlobalTheory.GLp.ParInd
