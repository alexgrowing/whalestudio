import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem norm_map_of_basis {F L A B ι : Type} [CommRing F] [CommRing L] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra L B] [Fintype ι] [DecidableEq ι] (φ : F →+* L) (ψ : A →+* B)
    (hψ : ∀ c, ψ (algebraMap F A c) = algebraMap L B (φ c))
    (b : Module.Basis ι F A) (b' : Module.Basis ι L B) (hb : ∀ i, ψ (b i) = b' i) (y : A) :
    Algebra.norm L (ψ y) = φ (Algebra.norm F y) := by
  have hr : ∀ (x : A) (i : ι), b'.repr (ψ x) i = φ (b.repr x i) := by
    intro x i
    have h1 : ψ x = ∑ j, φ (b.repr x j) • b' j := by
      conv_lhs => rw [← b.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hψ, hb]
    rw [h1, b'.repr_sum_self]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, hr]

theorem exists_basis_pow_root {L : Type} [Field L] {p : ℕ} (hp : 0 < p) (a : L) :
    ∃ b : Module.Basis (Fin p) L (AdjoinRoot (X ^ p - C a : L[X])),
      ∀ i, b i = AdjoinRoot.root (X ^ p - C a : L[X]) ^ (i : ℕ) := by
  have hne : (X ^ p - C a : L[X]) ≠ 0 := X_pow_sub_C_ne_zero hp a
  have hd : (AdjoinRoot.powerBasis hne).dim = p := by
    rw [AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  refine ⟨(AdjoinRoot.powerBasis hne).basis.reindex (finCongr hd), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen]
  simp

theorem powSub_le_kNorm_and_kNorm_map : ∀ (p : ℕ), 0 < p → (∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), powSub p φ ≤ kNorm p φ δ) ∧ ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), kNorm p (RingHom.id F) δ ≤ kNorm p φ δ := by
  intro p hp
  constructor
  · intro F L _ _ φ δ x hx
    obtain ⟨r, hr⟩ := (mem_powSub p φ x).1 hx
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne'] at hr
      exact (map_ne_zero φ).2 x.ne_zero hr.symm
    obtain ⟨b, -⟩ := exists_basis_pow_root hp (φ δ)
    refine (mem_kNorm p φ δ x).2
      ⟨Units.map (algebraMap L (AdjoinRoot (X ^ p - C (φ δ) : L[X]))).toMonoidHom
        (Units.mk0 r hr0), ?_⟩
    change Algebra.norm L (algebraMap L _ r) = _
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin, hr]
  · intro F L _ _ φ δ x hx
    obtain ⟨y, hy⟩ := (mem_kNorm p (RingHom.id F) δ x).1 hx
    obtain ⟨b, hb⟩ := exists_basis_pow_root hp (RingHom.id F δ)
    obtain ⟨b', hb'⟩ := exists_basis_pow_root hp (φ δ)
    have hdv : (X ^ p - C (φ δ) : L[X]) ∣ (X ^ p - C (RingHom.id F δ) : F[X]).map φ := by
      simp
    let ψ := AdjoinRoot.map φ _ _ hdv
    refine (mem_kNorm p φ δ x).2 ⟨Units.map ψ.toMonoidHom y, ?_⟩
    change Algebra.norm L (ψ y) = _
    rw [norm_map_of_basis φ ψ (fun c => by simp [ψ]) b b'
      (fun i => by simp [hb, hb', ψ]) y, hy]
    rfl

end GlobalTheory.CNorm
