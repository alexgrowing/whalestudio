import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.SdComap

set_option synthInstance.maxHeartbeats 400000

variable {D : D7}

theorem exists_nat_mul_isIntegral' (e : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * e) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := D.host.E) {e}
  have h := hy e (Finset.mem_singleton_self e)
  have hpos : 0 < y.natAbs := Int.natAbs_pos.2 hy0
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos hpos hpos, ?_⟩
  have e1 : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * e = (y : D.host.E) * ((y : D.host.E) * e) := by
    have h2 := Int.natAbs_mul_self' y
    rw [← mul_assoc, ← Int.cast_natCast, Nat.cast_mul, h2, Int.cast_mul]
  rw [e1]
  rw [zsmul_eq_mul] at h
  refine IsIntegral.mul ?_ h
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := y))

theorem mul_mem_intAE' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem natCast_mem_intAE (n : ℕ) : (n : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
  rw [Algebra.TensorProduct.natCast_def]
  refine AddSubgroup.subset_closure ⟨(n : Af D.host.F), fun v => ?_, 1, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ n
  · simp

theorem exists_natCast_mul_mem_intAE (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ n : ℕ, 0 < n ∧ (n : Af D.host.F ⊗[D.host.F] D.host.E) * z ∈ intAE D := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [mul_zero]; exact zero_mem _⟩
  | tmul a e =>
    obtain ⟨n, hn, he⟩ := exists_nat_mul_isIntegral' (D := D) e
    obtain ⟨d, hd, ha⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_adele (F := D.host.F) a
    refine ⟨d * n, Nat.mul_pos hd hn, ?_⟩
    have e1 : ((d * n : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (a ⊗ₜ[D.host.F] e) =
        ((d : Af D.host.F) * a) ⊗ₜ[D.host.F] ((n : D.host.E) * e) := by
      rw [Nat.cast_mul, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.natCast_def',
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e1]
    exact AddSubgroup.subset_closure ⟨_, fun v => Subring.mem_iInf.1 ha v, ⟨_, he⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have e1 : ((n₁ * n₂ : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (x + y) =
        (n₂ : Af D.host.F ⊗[D.host.F] D.host.E) * ((n₁ : Af D.host.F ⊗[D.host.F] D.host.E) * x) +
          (n₁ : Af D.host.F ⊗[D.host.F] D.host.E) * ((n₂ : Af D.host.F ⊗[D.host.F] D.host.E) * y) := by
      push_cast; ring
    rw [e1]
    exact add_mem (mul_mem_intAE' (natCast_mem_intAE n₂) hx) (mul_mem_intAE' (natCast_mem_intAE n₁) hy)

theorem exists_natCast_mul_mem_intAt {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) :
    ∃ n : ℕ, 0 < n ∧ (n : AE D) * a ∈ intAt D P := by
  obtain ⟨n, hn, h⟩ := exists_natCast_mul_mem_intAE (D := D) (finPart D a)
  refine ⟨n, hn, Ideal.mul_mem_left _ _ ha, ?_⟩
  rw [map_mul, map_natCast]; exact h

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a * b ∈ intAt D P :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact mul_mem_intAE' ha.2 hb.2⟩

theorem intAt_natCast_mul {P : Pl D → Prop} {a : AE D} (n : ℕ) (ha : a ∈ intAt D P) : (n : AE D) * a ∈ intAt D P :=
  ⟨Ideal.mul_mem_left _ _ ha.1, by rw [map_mul, map_natCast]; exact mul_mem_intAE' (natCast_mem_intAE n) ha.2⟩

theorem intAt_sum {P : Pl D → Prop} {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, f i ∈ intAt D P) :
    ∑ i ∈ s, f i ∈ intAt D P := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    exact intAt_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cA_mulVec {n : ℕ} (M : Mx D n n) (y : Fin n → AE D) :
    (fun i => cA D ((M *ᵥ y) i)) = Matrix.vecMul (fun i => cA D (y i)) (adj M) := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, adj, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = Matrix.vecMul (fun i => cA D (y i)) (gA S) ⬝ᵥ x := by
  simp only [hermAt, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem hermAt_mt (S : HSp D) (g : GA D S) (x y : Fin S.rank → AE D) :
    hermAt S (mt S g *ᵥ x) (mt S g *ᵥ y) = hermAt S x y := by
  rw [hermAt_eq, hermAt_eq, cA_mulVec (mt S g) y, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
    mt_unitary]

theorem mulVec_eq_add {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (i : Fin n) :
    (M *ᵥ y) i = y i + ∑ j, (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * y j := by
  have h : M *ᵥ y = y + (M - 1) *ᵥ y := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [h]; rfl

theorem eq_mulVec_sub {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (i : Fin n) :
    y i = (M *ᵥ y) i - ∑ j, (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * y j := by
  rw [mulVec_eq_add, add_sub_cancel_right]

theorem smul_mulVec_apply {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (c : R)
    (i : Fin n) : (c • (M *ᵥ y)) i = c * y i + ∑ j, (c * (M i j - (1 : Matrix (Fin n) (Fin n) R) i j)) * y j := by
  rw [Pi.smul_apply, smul_eq_mul, mulVec_eq_add, mul_add, Finset.mul_sum]
  simp only [mul_assoc]

theorem mulVec_natCast_smul {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (m K : ℕ) :
    M *ᵥ (((m * K : ℕ) : R) • y) = (m : R) • ((K : R) • (M *ᵥ y)) := by
  rw [Matrix.mulVec_smul, Nat.cast_mul, mul_smul]

theorem mulVec_mulVec_of_mul_eq_one {R : Type} [CommRing R] {n : ℕ} {M N : Matrix (Fin n) (Fin n) R} (h : M * N = 1)
    (x : Fin n → R) : M *ᵥ (N *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem exists_common_natCast_mul_mem_intAt {P : Pl D → Prop} {ι : Type} [Fintype ι] (a : ι → AE D)
    (ha : ∀ i, a i ∈ idAt D P) : ∃ K : ℕ, 0 < K ∧ ∀ i, (K : AE D) * a i ∈ intAt D P := by
  classical
  choose n hn hx using fun i => exists_natCast_mul_mem_intAt (ha i)
  refine ⟨∏ p, n p, Finset.prod_pos fun p _ => hn p, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact intAt_natCast_mul _ (hx i)

theorem isSDAt_comap_of (S : HSp D) (v : Pl D) (M N : Mx D S.rank S.rank) (hMN : M * N = 1)
    (hM1 : ∀ i j, M i j - (1 : Mx D S.rank S.rank) i j ∈ idAt D (· = v))
    (hherm : ∀ x y, hermAt S (M *ᵥ x) (M *ᵥ y) = hermAt S x y)
    (Λ : AddSubgroup (Fin S.rank → AE D)) (hΛ : IsSDAt S v Λ) :
    IsSDAt S v (Λ.comap (Matrix.mulVecLin M).toAddMonoidHom) := by
  obtain ⟨hsupp, ⟨m, hm, hmint⟩, hsd⟩ := hΛ
  have hmem : ∀ y, y ∈ Λ.comap (Matrix.mulVecLin M).toAddMonoidHom ↔ M *ᵥ y ∈ Λ := fun y => Iff.rfl
  refine ⟨fun y hy i => ?_, ?_, ?_⟩
  · rw [eq_mulVec_sub M y i]
    exact sub_mem (hsupp _ ((hmem y).1 hy) i) (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hM1 i j))
  · obtain ⟨K, hK, hKint⟩ := exists_common_natCast_mul_mem_intAt
      (fun p : Fin S.rank × Fin S.rank => M p.1 p.2 - (1 : Mx D S.rank S.rank) p.1 p.2) fun p => hM1 p.1 p.2
    refine ⟨m * K, Nat.mul_pos hm hK, fun y hy => (hmem _).2 ?_⟩
    rw [mulVec_natCast_smul M y m K]
    refine hmint _ fun i => ?_
    rw [smul_mulVec_apply M y (K : AE D) i]
    exact intAt_add (intAt_natCast_mul K (hy i)) (intAt_sum _ _ fun j _ => intAt_mul (hKint (i, j)) (hy j))
  · intro y hy
    have key := hsd _ (mulVec_mem_idAt M hy)
    refine ⟨fun h x hx => ?_, fun h => (hmem y).2 (key.2 fun x hx => ?_)⟩
    · rw [← hherm y x]; exact key.1 ((hmem y).1 h) _ ((hmem x).1 hx)
    · have hx' : M *ᵥ (N *ᵥ x) = x := mulVec_mulVec_of_mul_eq_one hMN x
      have h3 := h (N *ᵥ x) ((hmem _).2 (by rw [hx']; exact hx))
      rwa [← hherm, hx'] at h3

theorem isSDAt_comap (D : D7) (S : HSp D) (v : Pl D) (g : GA D S) (hg : g ∈ grpAt S (· = v))
    (Λ : AddSubgroup (Fin S.rank → AE D)) (hΛ : IsSDAt S v Λ) :
    IsSDAt S v (Λ.comap (Matrix.mulVecLin (mt S g)).toAddMonoidHom) :=
  isSDAt_comap_of S v (mt S g) (mt S g⁻¹) (mt_mul_inv S g) ((mem_congGrp_iff S (idAt D (· = v)) g).1 hg)
    (hermAt_mt S g) Λ hΛ

end GlobalTheory.IwaPlace.SdComap

end
