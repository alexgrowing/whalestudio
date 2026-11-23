import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnitStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.EtIsom

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem rec_eq {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (q : Fin r → R)
    (u w : ℕ → M) (hu : ∀ m, u (m + r) = -∑ i, q i • u (m + i))
    (hw : ∀ m, w (m + r) = -∑ i, q i • w (m + i)) (h0 : ∀ n < r, u n = w n) : ∀ n, u n = w n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < r
    · exact h0 n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + r := ⟨n - r, by omega⟩
      rw [hu, hw]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ih _ (by have := i.2; omega)]

theorem pow_rec (hG : A.IsGen τ p) (m : ℕ) :
    τ ^ (m + r) = -∑ i, algebraMap F A.K (p i) * τ ^ (m + (i : ℕ)) := by
  have h := congrArg (fun t => τ ^ m * t) hG.2.2
  simp only [mul_add, Finset.mul_sum, mul_zero, Algebra.smul_def] at h
  rw [eq_neg_iff_add_eq_zero, ← h, pow_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]; ring

def bK (hG : A.IsGen τ p) : Module.Basis (Fin r) F A.K :=
  basisOfLinearIndependentOfCardEqFinrank' _ hG.1 (by rw [Fintype.card_fin, hG.2.1])

theorem bK_apply (hG : A.IsGen τ p) (i : Fin r) : bK A hG i = τ ^ (i : ℕ) := by
  simp [bK, coe_basisOfLinearIndependentOfCardEqFinrank']

def bL (hG : A.IsGen τ p) : Module.Basis (Fin r) E A.L := A.push.out.basis (bK A hG)

theorem bL_apply (hG : A.IsGen τ p) (i : Fin r) : bL A hG i = algebraMap A.K A.L (τ ^ (i : ℕ)) := by
  rw [bL, IsBaseChange.basis_apply, bK_apply]; rfl

theorem bL_repr (hG : A.IsGen τ p) (v : A.K) (i : Fin r) :
    (bL A hG).repr (algebraMap A.K A.L v) i = algebraMap F E ((bK A hG).repr v i) :=
  A.push.out.basis_repr_comp_apply (bK A hG) v i

theorem trace_map (hG : A.IsGen τ p) (c : A.K) :
    Algebra.trace E A.L (algebraMap A.K A.L c) = algebraMap F E (Algebra.trace F A.K c) := by
  rw [Algebra.trace_eq_matrix_trace (bL A hG), Algebra.trace_eq_matrix_trace (bK A hG), Matrix.trace,
    Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  rw [bL_apply, ← map_mul, bL_repr, bK_apply]

end GlobalTheory.EtIsom

namespace GlobalTheory.EtIsom

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem cayley (M : Matrix (Fin r) (Fin r) E) : M ^ r + ∑ i : Fin r, M.charpoly.coeff i • M ^ (i : ℕ) = 0 := by
  have h := Matrix.aeval_self_charpoly M
  rw [M.charpoly_monic.as_sum, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h
  simpa [Finset.sum_range, Algebra.smul_def] using h

def mat (j : A.L ≃ₗ[E] (Fin r → E)) : Matrix (Fin r) (Fin r) E :=
  LinearMap.toMatrix' (j.toLinearMap ∘ₗ LinearMap.mulLeft E (algebraMap A.K A.L τ) ∘ₗ j.symm.toLinearMap)

theorem mat_mulVec (j : A.L ≃ₗ[E] (Fin r → E)) (z : A.L) :
    mat A (τ := τ) j *ᵥ j z = j (algebraMap A.K A.L τ * z) := by
  simp [mat, LinearMap.toMatrix'_mulVec]

theorem mat_pow_mulVec (j : A.L ≃ₗ[E] (Fin r → E)) (n : ℕ) (z : A.L) :
    mat A (τ := τ) j ^ n *ᵥ j z = j (algebraMap A.K A.L (τ ^ n) * z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, mat_mulVec, ih, pow_succ, RingHom.map_mul, mul_assoc]

end GlobalTheory.EtIsom

namespace GlobalTheory.EtIsom

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem mat_herm_form {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hj : A.IsIsom x j) (u v : Fin r → E) :
    star (mat A (τ := τ) j *ᵥ u) ⬝ᵥ v = star u ⬝ᵥ (mat A (τ := τ) j *ᵥ v) := by
  obtain ⟨z, rfl⟩ := j.surjective u
  obtain ⟨z', rfl⟩ := j.surjective v
  rw [mat_mulVec, mat_mulVec, hj, hj, star_mul', A.star_K]
  congr 1
  ring

theorem mat_selfAdjoint {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hj : A.IsIsom x j) :
    IsSelfAdjoint (mat A (τ := τ) j) := by
  ext k i
  have h := mat_herm_form A (τ := τ) hj (Pi.single k 1) (Pi.single i 1)
  simp [Matrix.mulVec_single, dotProduct_single, single_dotProduct] at h
  simpa [Matrix.star_apply, Matrix.conjTranspose_apply] using h

theorem mat_charpoly (hG : A.IsGen τ p) {j : A.L ≃ₗ[E] (Fin r → E)} (i : Fin r) :
    (mat A (τ := τ) j).charpoly.coeff i = algebraMap F E (p i) := by
  set M := mat A (τ := τ) j with hM
  have h1 : j (algebraMap A.K A.L (τ ^ r)) + ∑ k : Fin r, M.charpoly.coeff k • j (bL A hG k) = 0 := by
    have := congrArg (fun N => N *ᵥ j 1) (cayley M)
    simp only [Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.zero_mulVec, hM,
      mat_pow_mulVec, mul_one] at this
    simpa only [bL_apply] using this
  have h2 : algebraMap A.K A.L (τ ^ r) = -∑ k : Fin r, algebraMap F E (p k) • bL A hG k := by
    have := congrArg (algebraMap A.K A.L) (pow_rec A hG 0)
    simp only [zero_add, map_neg, map_sum, map_mul] at this
    rw [this]; congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [bL_apply, Algebra.smul_def, ← IsScalarTower.algebraMap_apply F A.K A.L,
      ← IsScalarTower.algebraMap_apply F E A.L]
  rw [h2, map_neg, map_sum] at h1
  have h3 : j (∑ k : Fin r, (M.charpoly.coeff k - algebraMap F E (p k)) • bL A hG k) = 0 := by
    rw [← h1, Finset.sum_congr rfl (fun k _ => sub_smul _ _ _), Finset.sum_sub_distrib, map_sub, map_sum,
      map_sum]
    simp only [map_smul]
    abel
  rw [LinearEquiv.map_eq_zero_iff] at h3
  have h4 := Fintype.linearIndependent_iff.mp (bL A hG).linearIndependent _ h3 i
  exact sub_eq_zero.mp h4

end GlobalTheory.EtIsom

namespace GlobalTheory.EtIsom

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem isom_to_herm (hG : A.IsGen τ p) (lam : F) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hj : A.IsIsom x j) :
    ∃ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) ∧
      ∀ y, HasInv ((Ax, j y, lam) : Hn r F E) (A.invK τ p lam (x * A.NL y)) := by
  refine ⟨⟨mat A (τ := τ) j, mat_selfAdjoint A hj⟩, fun z => (mat_mulVec A j z).symm, fun y => ?_⟩
  unfold HasInv GlobalTheory.JR.inv Hn.toGl Inv.map Et.invK
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) rfl)
  · exact mat_charpoly A hG i
  · show star (j y) ⬝ᵥ (mat A (τ := τ) j ^ (i : ℕ) *ᵥ j y) =
      algebraMap F E (Algebra.trace F A.K (τ ^ (i : ℕ) * (x * A.NL y)))
    rw [mat_pow_mulVec, hj, ← trace_map A hG]
    congr 1
    rw [map_mul, map_mul, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1 y]
    ring

end GlobalTheory.EtIsom

namespace GlobalTheory.EtIsom

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem hasInv_parts {lam : F} {a : A.K} {X : Hn r F E} (hX : HasInv X (A.invK τ p lam a)) :
    (∀ i : Fin r, X.1.1.charpoly.coeff i = algebraMap F E (p i)) ∧
      ∀ i : Fin r, star X.2.1 ⬝ᵥ (X.1.1 ^ (i : ℕ) *ᵥ X.2.1) = algebraMap F E (Algebra.trace F A.K (τ ^ (i : ℕ) * a)) := by
  unfold HasInv GlobalTheory.JR.inv Hn.toGl Inv.map Et.invK at hX
  exact ⟨fun i => congrFun (congrArg Prod.fst hX) i, fun i => congrFun (congrArg (fun t => t.2.1) hX) i⟩

theorem mat_rec (M : Matrix (Fin r) (Fin r) E) (q : Fin r → E) (h : M ^ r + ∑ i : Fin r, q i • M ^ (i : ℕ) = 0)
    (v : Fin r → E) (m : ℕ) : M ^ (m + r) *ᵥ v = -∑ i, q i • (M ^ (m + (i : ℕ)) *ᵥ v) := by
  have h1 := congrArg (fun N => (M ^ m * N) *ᵥ v) h
  simp only [mul_add, Finset.mul_sum, mul_smul_comm, ← pow_add, Matrix.add_mulVec, Matrix.sum_mulVec,
    Matrix.smul_mulVec, mul_zero, Matrix.zero_mulVec] at h1
  exact eq_neg_of_add_eq_zero_left h1

theorem star_smul_vec (c : E) (v : Fin r → E) : star (c • v) = star c • star v := by
  funext i; simp [star_mul']

theorem star_smul_L (c : E) (z : A.L) : star (c • z) = star c • star z := by
  rw [Algebra.smul_def, Algebra.smul_def, star_mul', A.star_E]

theorem herm_gram (M : Matrix (Fin r) (Fin r) E) (hM : M.conjTranspose = M) (b : Fin r → E) (i k : ℕ) :
    star (M ^ i *ᵥ b) ⬝ᵥ (M ^ k *ᵥ b) = star b ⬝ᵥ (M ^ (i + k) *ᵥ b) := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_pow, hM, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, pow_add]

theorem trace_rec (hG : A.IsGen τ p) (a : A.K) (m : ℕ) :
    algebraMap F E (Algebra.trace F A.K (τ ^ (m + r) * a)) =
      -∑ i, algebraMap F E (p i) • algebraMap F E (Algebra.trace F A.K (τ ^ (m + (i : ℕ)) * a)) := by
  rw [pow_rec A hG, neg_mul, Finset.sum_mul, map_neg, map_sum, map_neg, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul, map_mul, smul_eq_mul]

end GlobalTheory.EtIsom

namespace GlobalTheory.EtIsom

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem star_bL (hG : A.IsGen τ p) (i : Fin r) : star (bL A hG i) = bL A hG i := by
  rw [bL_apply, A.star_K]

theorem form_eq (hG : A.IsGen τ p) (a : A.K) (M : Matrix (Fin r) (Fin r) E) (hM : M.conjTranspose = M)
    (b : Fin r → E) (hmom : ∀ n : ℕ, star b ⬝ᵥ (M ^ n *ᵥ b) = algebraMap F E (Algebra.trace F A.K (τ ^ n * a)))
    (φ : A.L →ₗ[E] (Fin r → E)) (hφb : ∀ i, φ (bL A hG i) = M ^ (i : ℕ) *ᵥ b) (w w' : A.L) :
    star (φ w) ⬝ᵥ φ w' = Algebra.trace E A.L (algebraMap A.K A.L a * star w * w') := by
  rw [← (bL A hG).sum_repr w, ← (bL A hG).sum_repr w']
  simp only [map_sum, map_smul, star_sum, star_smul_vec, star_smul_L, hφb, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm, smul_eq_mul,
    herm_gram M hM, hmom, star_bL]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [bL_apply, bL_apply, ← map_mul, ← map_mul, trace_map A hG, pow_add]
  ring_nf

end GlobalTheory.EtIsom

namespace GlobalTheory.EtIsom

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem cayley_hasInv {lam : F} {a : A.K} {X : Hn r F E} (hX : HasInv X (A.invK τ p lam a)) :
    X.1.1 ^ r + ∑ i : Fin r, algebraMap F E (p i) • X.1.1 ^ (i : ℕ) = 0 := by
  have h := cayley X.1.1
  simp only [(hasInv_parts A hX).1] at h
  exact h

theorem mom_all (hG : A.IsGen τ p) {lam : F} {a : A.K} {X : Hn r F E} (hX : HasInv X (A.invK τ p lam a)) (n : ℕ) :
    star X.2.1 ⬝ᵥ (X.1.1 ^ n *ᵥ X.2.1) = algebraMap F E (Algebra.trace F A.K (τ ^ n * a)) := by
  refine rec_eq (fun i => algebraMap F E (p i)) (fun n => star X.2.1 ⬝ᵥ (X.1.1 ^ n *ᵥ X.2.1))
    (fun n => algebraMap F E (Algebra.trace F A.K (τ ^ n * a))) (fun m => ?_) (trace_rec A hG a)
    (fun n hn => (hasInv_parts A hX).2 ⟨n, hn⟩) n
  rw [mat_rec _ _ (cayley_hasInv A hX), dotProduct_neg, dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul]

theorem detH (hG : A.IsGen τ p) {a : A.K} (ha : IsUnit a) :
    (Matrix.of fun i k : Fin r => Algebra.trace F A.K (τ ^ ((i : ℕ) + (k : ℕ)) * a)).det ≠ 0 := by
  have hinj := (GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ p 0 hG).1.1
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ e : Fin r → F, (Matrix.of fun i k : Fin r => Algebra.trace F A.K (τ ^ ((i : ℕ) + (k : ℕ)) * a)) *ᵥ e =
      (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * (a * ∑ k, e k • τ ^ (k : ℕ)))) := by
    intro e
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul, pow_add, mul_comm]
    ring_nf
  intro e e' h
  rw [key, key] at h
  have h1 := ha.mul_left_cancel (hinj h)
  have h2 := Fintype.linearIndependent_iff.mp hG.1 (e - e') (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])
  funext i
  exact sub_eq_zero.mp (h2 i)

theorem vec_li (hG : A.IsGen τ p) {lam : F} {a : A.K} (ha : IsUnit a) {X : Hn r F E}
    (hX : HasInv X (A.invK τ p lam a)) : LinearIndependent E (fun i : Fin r => X.1.1 ^ (i : ℕ) *ᵥ X.2.1) := by
  have hAh : X.1.1.conjTranspose = X.1.1 := by rw [← Matrix.star_eq_conjTranspose]; exact X.1.2
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hdet : ((algebraMap F E).mapMatrix
      (Matrix.of fun i k : Fin r => Algebra.trace F A.K (τ ^ ((i : ℕ) + (k : ℕ)) * a))).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact (map_ne_zero _).mpr (detH A hG ha)
  have h0 : (algebraMap F E).mapMatrix
      (Matrix.of fun i k : Fin r => Algebra.trace F A.K (τ ^ ((i : ℕ) + (k : ℕ)) * a)) *ᵥ g = 0 := by
    funext k
    have := congrArg (fun v => star (X.1.1 ^ (k : ℕ) *ᵥ X.2.1) ⬝ᵥ v) hg
    simp only [dotProduct_sum, dotProduct_smul, herm_gram _ hAh, mom_all A hG hX, dotProduct_zero,
      smul_eq_mul] at this
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet h0)

end GlobalTheory.EtIsom

namespace GlobalTheory.EtIsom

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem herm_to_isom (hG : A.IsGen τ p) {lam : F} {a : A.K} (ha : IsUnit a) {X : Hn r F E}
    (hX : HasInv X (A.invK τ p lam a)) (x : A.K) (y : A.L) (hy : IsUnit y) (hxa : a = x * A.NL y) :
    ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom x j ∧ (∀ z, j (algebraMap A.K A.L τ * z) = X.1.1 *ᵥ j z) ∧
      j y = X.2.1 := by
  have hAh : X.1.1.conjTranspose = X.1.1 := by rw [← Matrix.star_eq_conjTranspose]; exact X.1.2
  let bv : Module.Basis (Fin r) E (Fin r → E) :=
    basisOfLinearIndependentOfCardEqFinrank' _ (vec_li A hG ha hX) (by simp)
  have hbv : ∀ i, bv i = X.1.1 ^ (i : ℕ) *ᵥ X.2.1 := fun i => by
    simp [bv, coe_basisOfLinearIndependentOfCardEqFinrank']
  let φ : A.L ≃ₗ[E] (Fin r → E) := (bL A hG).equiv bv (Equiv.refl _)
  have hφb : ∀ i, φ (bL A hG i) = X.1.1 ^ (i : ℕ) *ᵥ X.2.1 := fun i => by
    simp [φ, Module.Basis.equiv_apply, hbv]
  have hφ : ∀ n : ℕ, φ (algebraMap A.K A.L (τ ^ n)) = X.1.1 ^ n *ᵥ X.2.1 := by
    refine rec_eq (fun i => algebraMap F E (p i)) (fun n => φ (algebraMap A.K A.L (τ ^ n)))
      (fun n => X.1.1 ^ n *ᵥ X.2.1) (fun m => ?_) (mat_rec _ _ (cayley_hasInv A hX) _) (fun n hn => ?_)
    · show φ (algebraMap A.K A.L (τ ^ (m + r))) =
        -∑ i, algebraMap F E (p i) • φ (algebraMap A.K A.L (τ ^ (m + (i : ℕ))))
      rw [pow_rec A hG, map_neg, map_sum, map_neg, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← IsScalarTower.algebraMap_apply F A.K A.L, IsScalarTower.algebraMap_apply F E A.L,
        ← Algebra.smul_def, map_smul]
    · have := hφb ⟨n, hn⟩
      rwa [bL_apply] at this
  have hτ : ∀ w, φ (algebraMap A.K A.L τ * w) = X.1.1 *ᵥ φ w := by
    have h : (φ.toLinearMap ∘ₗ LinearMap.mulLeft E (algebraMap A.K A.L τ)) =
        (Matrix.toLin' X.1.1) ∘ₗ φ.toLinearMap := by
      refine (bL A hG).ext fun i => ?_
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply,
        bL_apply]
      rw [← map_mul, ← pow_succ', hφ, hφ, Matrix.mulVec_mulVec, pow_succ']
    intro w
    exact LinearMap.congr_fun h w
  let u := hy.unit
  have h1 : y * ((u⁻¹ : A.Lˣ) : A.L) = 1 := hy.mul_val_inv
  have h2 : star y * star ((u⁻¹ : A.Lˣ) : A.L) = 1 := by rw [← star_mul', h1, star_one]
  let mE : A.L ≃ₗ[E] A.L := LinearEquiv.ofLinear (LinearMap.mulRight E ((u⁻¹ : A.Lˣ) : A.L))
    (LinearMap.mulRight E (u : A.L)) (by ext z; simp [mul_assoc]) (by ext z; simp [mul_assoc])
  have hj : ∀ z, (mE.trans φ) z = φ (z * ((u⁻¹ : A.Lˣ) : A.L)) := fun z => rfl
  refine ⟨mE.trans φ, fun z z' => ?_, fun z => ?_, ?_⟩
  · rw [hj, hj]
    refine (form_eq A hG a X.1.1 hAh X.2.1 (mom_all A hG hX) φ.toLinearMap hφb _ _).trans ?_
    congr 1
    rw [hxa, map_mul, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1 y, star_mul']
    linear_combination (algebraMap A.K A.L x * star z * z') * (star y * star ((u⁻¹ : A.Lˣ) : A.L)) * h1 +
      (algebraMap A.K A.L x * star z * z') * h2
  · rw [hj, hj, mul_assoc, hτ]
  · rw [hj, h1, ← map_one (algebraMap A.K A.L), ← pow_zero τ, hφ, pow_zero, Matrix.one_mulVec]

end GlobalTheory.EtIsom

theorem GlobalTheory.EtIsom.herm_iff_isom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → (∀ (a : A.K) (X : Hn r F E), IsUnit a → HasInv X (A.invK τ p lam a) → ∀ (x : A.K) (y : A.L), IsUnit y → a = x * A.NL y → ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom x j ∧ (∀ z, j (algebraMap A.K A.L τ * z) = X.1.1 *ᵥ j z) ∧ j y = X.2.1) ∧ ∀ (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∃ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) ∧ ∀ y, HasInv ((Ax, j y, lam) : Hn r F E) (A.invK τ p lam (x * A.NL y)) := by
  intro F E _ _ _ _ _ A r τ p lam hG
  exact ⟨fun a X ha hX x y hy hxa => GlobalTheory.EtIsom.herm_to_isom A hG ha hX x y hy hxa,
    fun x j hj => GlobalTheory.EtIsom.isom_to_herm A hG lam x j hj⟩
