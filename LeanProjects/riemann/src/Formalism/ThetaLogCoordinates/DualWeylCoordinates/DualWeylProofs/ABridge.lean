import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QaExpEqBidetExp

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

lemma qa_can_emb {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have := Finset.orderEmbOfFin_unique (s := (canT mu c).1) (canT mu c).2
    (f := fun a : Fin (colH mu c) => Fin.castLE (colH_le mu c) a) (by intro x; simp [canT])
    (Fin.strictMono_castLE _)
  exact (congrFun this a).symm

lemma qa_minor (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) :
    Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat R n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b)) =
    rename Prod.swap (initMinor R (qa_row I c) (colH_le mu c)) := by
  conv_rhs => rw [initMinor, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext a b
  simp [Matrix.transpose_apply, genMat, qa_row, qa_can_emb]

lemma qa_prod_minor (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    ∏ c : ↥(TCols mu), Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat R n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b)) =
    rename Prod.swap (qa_P R I) := by
  unfold qa_P
  rw [map_prod]
  exact Finset.prod_congr rfl fun c _ => qa_minor R I c

theorem qa_brk_eq {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brk mu I = ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      algebraMap (MvPolynomial (Fin n × Fin n) ℤ) (GLCoord ℤ n) (rename Prod.swap (qa_P ℤ I)) := by
  unfold brk TMat minorC
  rw [← qa_prod_minor, map_prod]

theorem qa_brkPol_eq {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brkPol mu I = (genMat ℤ n).det ^ (mu (lastIdx n)).toNat * rename Prod.swap (qa_P ℤ I) := by
  unfold brkPol
  rw [qa_prod_minor]

lemma qa_det_ne (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) : (genMat R n).det ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin n) R

lemma qa_algebraMap_inj (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) :=
  IsLocalization.injective (GLCoord R n)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (qa_det_ne R n))

def qa_Phi (R : Type*) [CommRing R] (n : ℕ) (u : GLCoord R n) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] GLCoord R n :=
  (LinearMap.mulLeft R u) ∘ₗ (IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).toLinearMap ∘ₗ
    (rename (R := R) (Prod.swap : Fin n × Fin n → Fin n × Fin n)).toLinearMap

lemma qa_Phi_apply (R : Type*) [CommRing R] (n : ℕ) (u : GLCoord R n) (f : MvPolynomial (Fin n × Fin n) R) :
    qa_Phi R n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (rename Prod.swap f) := rfl

lemma qa_Phi_inj (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) (u : GLCoord R n) (hu : IsUnit u) :
    Function.Injective (qa_Phi R n u) := by
  intro f g h
  rw [qa_Phi_apply, qa_Phi_apply] at h
  exact rename_injective _ Prod.swap_injective (qa_algebraMap_inj R n (hu.mul_left_cancel h))

def qa_intLin {M N : Type*} [AddCommGroup M] {i1 : Module ℤ M} [AddCommGroup N] {i2 : Module ℤ N}
    (f : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 i2) :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 (AddCommGroup.toIntModule N) :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 (AddCommGroup.toIntModule N) ⟨f, f.map_add⟩
    (fun z x => (f.map_smul z x).trans (int_smul_eq_zsmul i2 z (f x)))

def qa_PhiZ (n : ℕ) (u : GLCoord ℤ n) := qa_intLin (qa_Phi ℤ n u)

lemma qa_PhiZ_apply (n : ℕ) (u : GLCoord ℤ n) (f : MvPolynomial (Fin n × Fin n) ℤ) :
    qa_PhiZ n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) ℤ) (GLCoord ℤ n) (rename Prod.swap f) := rfl

lemma qa_PhiZ_inj (n : ℕ) (u : GLCoord ℤ n) (hu : IsUnit u) : Function.Injective (qa_PhiZ n u) :=
  qa_Phi_inj ℤ n u hu

lemma qa_mapCoord_algebraMap {n : ℕ} (F : Type) [CommRing F] (f : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) F (algebraMap _ (GLCoord ℤ n) f) =
      algebraMap _ (GLCoord F n) (MvPolynomial.map (Int.castRingHom F) f) := by
  unfold mapCoord
  rw [IsLocalization.Away.lift_eq]
  rfl

theorem qa_mapCoord_brk {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (F : Type) [CommRing F] (I : TIdx mu) :
    mapCoord (n := n) F (brk mu I) =
      qa_Phi F n (mapCoord (n := n) F ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) (qa_P F I) := by
  rw [qa_brk_eq, map_mul, qa_mapCoord_algebraMap, qa_Phi_apply, MvPolynomial.map_rename, map_tableauBideterminant]

end Formalism.InvariantFactorPaths.ColumnFamilies
