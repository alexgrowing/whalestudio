import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsGLMovingUnimodularPairToLastBasis
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SplitStd

variable {R : Type} [CommRing R]

def extLast (m : ℕ) : Matrix (Fin m) (Fin m) R →* Matrix (Fin (m + 1)) (Fin (m + 1)) R where
  toFun A := Matrix.of fun i j =>
    Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i
  map_one' := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  map_mul' A B := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem extLast_mulVec_single_last (m : ℕ) (A : Matrix (Fin m) (Fin m) R) :
    extLast m A *ᵥ Pi.single (Fin.last m) 1 = Pi.single (Fin.last m) 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [extLast, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

theorem single_last_vecMul_extLast (m : ℕ) (A : Matrix (Fin m) (Fin m) R) :
    Pi.single (Fin.last m) 1 ᵥ* extLast m A = Pi.single (Fin.last m) 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [extLast, Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

theorem extLast_mulVec (m : ℕ) (A : Matrix (Fin m) (Fin m) R) (w : Fin (m + 1) → R)
    (hw : w (Fin.last m) = 0) (a : Fin m) (h : A *ᵥ (fun i => w i.castSucc) = Pi.single a 1) :
    extLast m A *ᵥ w = Pi.single a.castSucc 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [extLast, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hw, (Fin.castSucc_ne_last a).symm]
  · have := congrFun h i
    simp only [Matrix.mulVec, dotProduct] at this
    simp [extLast, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hw, this, Pi.single_apply]

theorem vecMul_extLast (m : ℕ) (A : Matrix (Fin m) (Fin m) R) (w : Fin (m + 1) → R)
    (hw : w (Fin.last m) = 0) (a : Fin m) (h : (fun i => w i.castSucc) ᵥ* A = Pi.single a 1) :
    w ᵥ* extLast m A = Pi.single a.castSucc 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [extLast, Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, hw, (Fin.castSucc_ne_last a).symm]
  · have := congrFun h i
    simp only [Matrix.vecMul, dotProduct] at this
    simp [extLast, Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, hw, this, Pi.single_apply]

theorem dot_conj {k : ℕ} (g : GL (Fin k) R) (f v : Fin k → R) :
    (f ᵥ* ((g⁻¹ : GL (Fin k) R) : Matrix (Fin k) (Fin k) R)) ⬝ᵥ ((g : Matrix (Fin k) (Fin k) R) *ᵥ v)
      = f ⬝ᵥ v := by
  rw [← dotProduct_mulVec, mulVec_mulVec, Units.inv_mul, one_mulVec]

theorem core (s : ℕ) (hs : StableRangeLe R s) : ∀ (k m : ℕ) (v f : Fin k → Fin m → R),
    (∀ i j, f i ⬝ᵥ v j = if i = j then 1 else 0) → k + s ≤ m →
    ∃ (g : GL (Fin m) R) (σ : Fin k → Fin m), Function.Injective σ ∧ ∀ j,
      (g : Matrix (Fin m) (Fin m) R) *ᵥ v j = Pi.single (σ j) 1 ∧
      f j ᵥ* ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = Pi.single (σ j) 1 := by
  intro k
  induction k with
  | zero => intro m v f _ _; exact ⟨1, Fin.elim0, fun a => a.elim0, fun j => j.elim0⟩
  | succ k ih =>
    intro m v f hvf hkm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨g₁, hg₁v, hg₁f⟩ := GlobalTheory.T.exists_GL_moving_unimodular_pair_to_last_basis R s hs m (by omega) (v 0) (f 0) (by simpa using hvf 0 0)
    have hvl : ∀ j : Fin k, ((g₁ : Matrix _ _ R) *ᵥ v j.succ) (Fin.last m) = 0 := by
      intro j
      have key := dot_conj g₁ (f 0) (v j.succ)
      rw [hg₁f, single_dotProduct, one_mul, hvf, if_neg (Fin.succ_ne_zero j).symm] at key
      exact key
    have hfl : ∀ j : Fin k, (f j.succ ᵥ* ((g₁⁻¹ : GL _ R) : Matrix _ _ R)) (Fin.last m) = 0 := by
      intro j
      have key := dot_conj g₁ (f j.succ) (v 0)
      rw [hg₁v, dotProduct_single, mul_one, hvf, if_neg (Fin.succ_ne_zero j)] at key
      exact key
    let v' : Fin k → Fin m → R := fun j i => ((g₁ : Matrix _ _ R) *ᵥ v j.succ) i.castSucc
    let f' : Fin k → Fin m → R := fun j i => (f j.succ ᵥ* ((g₁⁻¹ : GL _ R) : Matrix _ _ R)) i.castSucc
    have hdual : ∀ i j, f' i ⬝ᵥ v' j = if i = j then 1 else 0 := by
      intro i j
      have key := dot_conj g₁ (f i.succ) (v j.succ)
      rw [hvf, dotProduct, Fin.sum_univ_castSucc, hvl j, mul_zero, add_zero] at key
      simpa [dotProduct, v', f', Fin.succ_inj] using key
    obtain ⟨g', σ', hσ', hg'⟩ := ih m v' f' hdual (by omega)
    refine ⟨Units.map (extLast m) g' * g₁,
      (Fin.cons (Fin.last m) (fun j => (σ' j).castSucc) : Fin (k + 1) → Fin (m + 1)), ?_, ?_⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, (Fin.castSucc_injective _).comp hσ'⟩
      rintro ⟨j, hj⟩
      exact Fin.castSucc_ne_last _ hj
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero, _root_.mul_inv_rev, Units.val_mul, Units.coe_map, Units.coe_map_inv]
        refine ⟨?_, ?_⟩
        · rw [← mulVec_mulVec, hg₁v, extLast_mulVec_single_last]
        · rw [← vecMul_vecMul, hg₁f, single_last_vecMul_extLast]
      · simp only [Fin.cons_succ, _root_.mul_inv_rev, Units.val_mul, Units.coe_map, Units.coe_map_inv]
        refine ⟨?_, ?_⟩
        · rw [← mulVec_mulVec]
          exact extLast_mulVec m _ _ (hvl j) _ (hg' j).1
        · rw [← vecMul_vecMul]
          exact vecMul_extLast m _ _ (hfl j) _ (hg' j).2

def pmat {n : ℕ} (π : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i = π j then 1 else 0

theorem pmat_mul_symm {n : ℕ} (π : Equiv.Perm (Fin n)) : (pmat π : Matrix (Fin n) (Fin n) R) * pmat π.symm = 1 := by
  ext i j
  simp [pmat, Matrix.mul_apply, Matrix.one_apply, Equiv.apply_eq_iff_eq_symm_apply]

def pGL {n : ℕ} (π : Equiv.Perm (Fin n)) : GL (Fin n) R :=
  ⟨pmat π, pmat π.symm, pmat_mul_symm π, by simpa using pmat_mul_symm (R := R) π.symm⟩

theorem pGL_mulVec {n : ℕ} (π : Equiv.Perm (Fin n)) (a : Fin n) :
    ((pGL π : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ Pi.single a 1 = Pi.single (π a) 1 := by
  funext i
  simp only [pGL, pmat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply]
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem vecMul_pGL_inv {n : ℕ} (π : Equiv.Perm (Fin n)) (a : Fin n) :
    Pi.single a 1 ᵥ* (((pGL π)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Pi.single (π a) 1 := by
  funext i
  simp only [pGL, pmat, Matrix.vecMul, dotProduct, Matrix.of_apply, Units.inv_mk]
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply, Equiv.eq_symm_apply, eq_comm]
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem exists_perm {n k : ℕ} (σ ι : Fin k → Fin n) (hσ : Function.Injective σ) (hι : Function.Injective ι) :
    ∃ π : Equiv.Perm (Fin n), ∀ j, π (σ j) = ι j := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, fun j => j.elim0⟩
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (t := (Finset.univ : Finset (Fin n)))
    (s := Finset.univ.image σ) (f := fun x => ι (Function.invFun σ x)) (by simp)
    (fun _ _ => Finset.mem_univ _) (by
      intro x hx y hy hxy
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      simp only [Function.leftInverse_invFun hσ a, Function.leftInverse_invFun hσ b] at hxy
      rw [hι hxy])
  refine ⟨g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ), fun j => ?_⟩
  have := hg (σ j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  simpa [Function.leftInverse_invFun hσ j] using this

end GlobalTheory.SplitStd

open GlobalTheory.SplitStd in
theorem GlobalTheory.splitSeq_to_standard : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ) (l : List ((Fin n → R) × (Fin n → R))), l ∈ splitSeq R n → l.length + s ≤ n → ∀ ι : Fin l.length → Fin n, Function.Injective ι → ∃ g : GL (Fin n) R, ∀ j : Fin l.length, (g : Matrix (Fin n) (Fin n) R) *ᵥ (l.get j).1 = Pi.single (ι j) 1 ∧ (l.get j).2 ᵥ* ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Pi.single (ι j) 1 := by
  intro R _ s hs n l hl hlen ι hι
  obtain ⟨g, σ, hσ, hg⟩ := core s hs l.length n (fun j => (l.get j).1) (fun j => (l.get j).2) hl hlen
  obtain ⟨π, hπ⟩ := exists_perm σ ι hσ hι
  refine ⟨pGL π * g, fun j => ⟨?_, ?_⟩⟩
  · rw [Units.val_mul, ← mulVec_mulVec, (hg j).1, pGL_mulVec, hπ]
  · rw [_root_.mul_inv_rev, Units.val_mul, ← vecMul_vecMul, (hg j).2, vecMul_pGL_inv, hπ]

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_GL_splitSeq_standard_of_stableRangeLe : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ) (l : List ((Fin n → R) × (Fin n → R))), l ∈ splitSeq R n → l.length + s ≤ n → ∀ ι : Fin l.length → Fin n, Function.Injective ι → ∃ g : GL (Fin n) R, ∀ j : Fin l.length, (g : Matrix (Fin n) (Fin n) R) *ᵥ (l.get j).1 = Pi.single (ι j) 1 ∧ (l.get j).2 ᵥ* ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Pi.single (ι j) 1 := by
  first
  | exact @GlobalTheory.splitSeq_to_standard
  | exact @GlobalTheory.SplitStd.exists_perm
  | exact @GlobalTheory.SplitStd.vecMul_pGL_inv
  | exact @GlobalTheory.SplitStd.pGL_mulVec
  | exact @GlobalTheory.SplitStd.pmat_mul_symm
  | exact @GlobalTheory.SplitStd.core
  | exact @GlobalTheory.SplitStd.dot_conj
  | exact @GlobalTheory.SplitStd.vecMul_extLast
  | exact @GlobalTheory.SplitStd.extLast_mulVec
  | exact @GlobalTheory.SplitStd.single_last_vecMul_extLast
  | exact @GlobalTheory.SplitStd.extLast_mulVec_single_last
end
