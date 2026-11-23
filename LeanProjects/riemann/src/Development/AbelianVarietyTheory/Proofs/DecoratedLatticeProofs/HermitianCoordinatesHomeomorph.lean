import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoordPair
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC GlobalTheory.HermSD

noncomputable section

namespace GlobalTheory.HermCoordEquiv

open GlobalTheory.GaussMean.OneVec

theorem sum_sum_split {M : Type} [AddCommMonoid M] {n : ℕ} (f : Fin n → Fin n → M) :
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (f p.1.1 p.1.2 + f p.1.2 p.1.1) := by
  classical
  have h1 : ∀ a b, f a b = (if a < b then f a b else 0) + (if a = b then f a b else 0) +
      (if b < a then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.2 h.le]
  have hsub : ∀ g : Fin n → Fin n → M, ∑ p : {p : Fin n × Fin n // p.1 < p.2}, g p.1.1 p.1.2 =
      ∑ a, ∑ b, if a < b then g a b else 0 := by
    intro g
    rw [← Fintype.sum_prod_type' (f := fun a b => if a < b then g a b else 0), ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) (fun a : Fin n × Fin n => g a.1 a.2)).symm
  rw [Finset.sum_add_distrib, hsub (fun a b => f a b), hsub (fun a b => f b a)]
  conv_lhs => enter [2, a, 2, b]; rw [h1 a b]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun a b => if b < a then f a b else 0)]
  abel

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  (R : Type) [CommRing R] [Algebra F R]

def invMat (σ : E →ₐ[F] E) {n : ℕ} (x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun a b => if h : a < b then x.2 ⟨(a, b), h⟩ else if h' : b < a then sigR R σ (x.2 ⟨(b, a), h'⟩)
    else algebraMap R (R ⊗[F] E) (x.1 a)

theorem invMat_mem (h : IsCMExt F E σ) {n : ℕ} (x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) :
    invMat R σ x ∈ HermR R σ n := by
  intro a b
  rcases lt_trichotomy a b with hab | hab | hab
  · simp [invMat, hab, not_lt.2 hab.le, sigR_sigR R h]
  · subst hab; simp only [invMat, lt_self_iff_false, ↓reduceDIte]; exact sigR_algebraMap R _
  · simp [invMat, hab, not_lt.2 hab.le]

def coordEquiv (h : IsCMExt F E σ) (n : ℕ) :
    HermR R σ n ≃+ ((Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) where
  toFun := hermCoord R σ
  invFun x := ⟨invMat R σ x, invMat_mem R h x⟩
  left_inv S := by
    apply Subtype.ext
    funext a b
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [invMat, hab, hermCoord]
    · subst hab; simpa [invMat, hermCoord] using fixed_eq R h (S.2 a a)
    · simpa [invMat, hab, not_lt.2 hab.le, hermCoord] using S.2 a b
  right_inv x := by
    refine Prod.ext (funext fun a => ?_) (funext fun p => ?_)
    · simpa [hermCoord, invMat] using half_trace R h (x.1 a)
    · simp [hermCoord, invMat, p.2]
  map_add' S T := by
    refine Prod.ext (funext fun a => ?_) (funext fun p => rfl)
    simp [hermCoord, mul_add]

theorem pair_eq (h : IsCMExt F E σ) {n : ℕ} (S T : HermR R σ n) :
    pairHerm R σ n S T = coordPair R σ n (hermCoord R σ S) (hermCoord R σ T) := by
  unfold pairHerm coordPair
  rw [sum_sum_split (fun a b => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * (T : Matrix (Fin n) (Fin n) _) b a)]
  beta_reduce
  rw [map_add, map_sum, map_sum, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have := half_trace R h (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S.1 a a) *
      (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (T.1 a a)))
    rw [map_mul, fixed_eq R h (S.2 a a), fixed_eq R h (T.2 a a)] at this
    simpa [hermCoord] using this
  · refine Finset.sum_congr rfl fun p _ => ?_
    have hT : T.1 p.1.2 p.1.1 = sigR R σ (T.1 p.1.1 p.1.2) := (T.2 p.1.2 p.1.1).symm
    have hS : S.1 p.1.2 p.1.1 = sigR R σ (S.1 p.1.1 p.1.2) := (S.2 p.1.2 p.1.1).symm
    simp only [hermCoord]
    rw [hT, hS]
    have hw : S.1 p.1.1 p.1.2 * sigR R σ (T.1 p.1.1 p.1.2) + sigR R σ (S.1 p.1.1 p.1.2) * T.1 p.1.1 p.1.2 =
        algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) (sigR R σ (S.1 p.1.1 p.1.2) * T.1 p.1.1 p.1.2)) := by
      rw [← add_sigR R h, add_comm, map_mul, sigR_sigR R h]
    rw [hw, half_trace R h]

variable [TopologicalSpace R] [IsTopologicalRing R]

end Main

end GlobalTheory.HermCoordEquiv
