import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

variable {D : D7}

scoped instance lcAE : LocallyCompactSpace (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.1
scoped instance t2AE : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1

def halfMx (a : AE D) (m n : ℕ) : AddSubgroup (Mx D m n) where
  carrier := {t | IsHalf a t}
  add_mem' {x y} hx hy i j := by
    show a * (x i j + y i j) = x i j + y i j
    rw [mul_add, hx i j, hy i j]
  zero_mem' i j := mul_zero a
  neg_mem' {x} hx i j := by
    show a * (-x i j) = -x i j
    rw [mul_neg, hx i j]

theorem mem_halfMx {a : AE D} {m n : ℕ} {t : Mx D m n} : t ∈ halfMx a m n ↔ IsHalf a t := Iff.rfl

theorem isClosed_halfMx (a : AE D) (m n : ℕ) : IsClosed (halfMx a m n : Set (Mx D m n)) := by
  have : (halfMx a m n : Set (Mx D m n)) = ⋂ i, ⋂ j, {t : Mx D m n | a * t i j = t i j} := by
    ext t; simp only [SetLike.mem_coe, mem_halfMx, IsHalf, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
      ((continuous_apply j).comp (continuous_apply i))

scoped instance lcMx (m n : ℕ) : LocallyCompactSpace (Mx D m n) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin n → AE D))

scoped instance tagMx (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) :=
  inferInstanceAs (IsTopologicalAddGroup (Fin m → Fin n → AE D))

scoped instance t2Mx (m n : ℕ) : T2Space (Mx D m n) :=
  inferInstanceAs (T2Space (Fin m → Fin n → AE D))

scoped instance tagHalf (a : AE D) (m n : ℕ) : IsTopologicalAddGroup (halfMx a m n) :=
  inferInstance

scoped instance t2Space_halfAdelicMatrixAddSubgroup (a : AE D) (m n : ℕ) : T2Space (halfMx a m n) := inferInstance

scoped instance lcHalf (a : AE D) (m n : ℕ) : LocallyCompactSpace (halfMx a m n) :=
  (isClosed_halfMx a m n).isClosedEmbedding_subtypeVal.locallyCompactSpace

scoped instance measHalf (a : AE D) (m n : ℕ) : MeasurableSpace (halfMx a m n) := borel _

scoped instance borelHalf (a : AE D) (m n : ℕ) : BorelSpace (halfMx a m n) := ⟨rfl⟩

def haarHalf (a : AE D) (m n : ℕ) : Measure (halfMx a m n) := Measure.addHaar

instance (a : AE D) (m n : ℕ) : (haarHalf a m n).IsAddHaarMeasure := by
  unfold haarHalf; infer_instance

def restEmb (V W : HSp D) {r : ℕ} (K : Matrix (Fin r) (Fin V.rank) D.host.E) (t : Mx D W.rank r) : WO V W :=
  HMul.hMul (t : Matrix (Fin W.rank) (Fin r) (AE D)) (K.map (incA D))

def avgForm (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (K : Matrix (Fin r) (Fin V.rank) D.host.E) (e : AE D) (ℓ' : (WO V' W → ℂ) →ₗ[ℂ] ℂ) (f : WO V W → ℂ) : ℂ :=
  ∫ t : halfMx (cA D e) W.rank r,
    ℓ' (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f)) ∂haarHalf (cA D e) W.rank r

end GlobalTheory.HalfAverage

namespace GlobalTheory.HalfAverage

variable {D : D7}

theorem isHalf_mul {a : AE D} {m n k : ℕ} {t : Mx D m n} (ht : IsHalf a t) (M : Matrix (Fin n) (Fin k) (AE D)) :
    IsHalf a (HMul.hMul t M : Mx D m k) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, ht i _]

theorem mul_isHalf {a : AE D} {m n : ℕ} {t : Mx D m n} (ht : IsHalf a t) (M : Matrix (Fin m) (Fin m) (AE D)) :
    IsHalf a (HMul.hMul M t : Mx D m n) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, ht k j]

def leftMul (a : AE D) {m n : ℕ} (M : Matrix (Fin m) (Fin m) (AE D)) (t : halfMx a m n) : halfMx a m n :=
  ⟨HMul.hMul M (t : Mx D m n), mul_isHalf t.2 M⟩

theorem leftMul_coe (a : AE D) {m n : ℕ} (M : Matrix (Fin m) (Fin m) (AE D)) (t : halfMx a m n) :
    (leftMul a M t : Mx D m n) = HMul.hMul M (t : Mx D m n) := rfl

theorem restEmb_add (V W : HSp D) {r : ℕ} (K : Matrix (Fin r) (Fin V.rank) D.host.E) (t t' : Mx D W.rank r) :
    restEmb V W K (t + t') = restEmb V W K t + restEmb V W K t' := Matrix.add_mul _ _ _

end GlobalTheory.HalfAverage
