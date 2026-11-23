import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrientedFormLaws

theorem sum_mul_left {A : Type} [CommRing A] {m n : ℕ} (c : A →+* A) (P : Fin n → Fin n → A)
    (Q : Fin m → Fin m → A) (t : A) (x y : Matrix (Fin m) (Fin n) A) :
    (∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * (x.map fun z => t * z) d a) =
      t * ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * x d a := by
  simp only [Finset.mul_sum, Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

theorem sum_mul_right {A : Type} [CommRing A] {m n : ℕ} (c : A →+* A) (P : Fin n → Fin n → A)
    (Q : Fin m → Fin m → A) (t : A) (x y : Matrix (Fin m) (Fin n) A) :
    (∑ a, ∑ b, ∑ e, ∑ d, P a b * c ((y.map fun z => t * z) e b) * Q e d * x d a) =
      c t * ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * x d a := by
  simp only [Finset.mul_sum, Matrix.map_apply, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

variable {D : D7} {S T : HSp D}

theorem hO_mul_left (t : Formalism.L2.Theta.AE D) (x y : WO S T) :
    hO S T (x.map fun z => t * z) y = t * hO S T x y :=
  sum_mul_left (cA D) (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k)) t x y

theorem hO_mul_right (t : Formalism.L2.Theta.AE D) (x y : WO S T) :
    hO S T x (y.map fun z => t * z) = cA D t * hO S T x y :=
  sum_mul_right (cA D) (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k)) t x y

theorem hO_rat (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hO S T (M.map (incA D)) (N.map (incA D)) = incA D (GlobalTheory.LatVac.hRat S T M N) := by
  unfold hO GlobalTheory.LatVac.hRat
  simp only [Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, map_sum, RingHom.map_mul]

theorem symplOH_rat (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (M.map (incA D)) (N.map (incA D)) = algebraMap D.host.F (AF D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M N)) := by
  have h2 : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun x => rfl
  rw [symplOH, symplO, hO_rat, ← RingHom.map_mul, h2, GlobalTheory.LatVac.trace_tmul, one_mul, RingHom.map_mul]

theorem hO_half (e : Formalism.L2.Theta.AE D) (u : WO S T) (he : e * cA D e = 0) (hu : IsHalf e u) : hO S T u u = 0 := by
  have h : (u.map fun z => e * z) = u := by
    funext i j
    exact hu i j
  have h1 := hO_mul_left e u u
  have h2 := hO_mul_right e u u
  rw [h] at h1 h2
  rw [h1, h2, ← mul_assoc, he, zero_mul]

theorem symplOH_laws : ∀ (D : D7) (S T : HSp D), (∀ x y z : WO S T, symplOH S T (x + y) z = symplOH S T x z + symplOH S T y z) ∧ (∀ x y z : WO S T, symplOH S T x (y + z) = symplOH S T x y + symplOH S T x z) ∧ (∀ x : WO S T, symplOH S T x x = 0) ∧ (∀ x y : WO S T, symplOH S T x y + symplOH S T x y = symplO S T x y) ∧ Continuous (fun q : WO S T × WO S T => symplOH S T q.1 q.2) ∧ (∀ g ∈ ratL T S, ∀ g' ∈ ratL T S, ∃ a : D.host.F, symplOH S T g g' = algebraMap D.host.F (AF D.host.F) a) ∧ (∀ (a : AE D) (x y : WO S T), symplOH S T (x.map fun z => a * z) y = symplOH S T x (y.map fun z => cA D a * z)) ∧ (∀ (e a : AE D) (u : WO S T), e * cA D e = 0 → IsHalf e u → symplOH S T (u.map fun z => a * z) u = 0) ∧ ∀ x y : WO S T, x.map (finPart D) = 0 → y.map (infPart D) = 0 → symplOH S T x y = 0 := by
  intro D S T
  refine ⟨GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_self,
    fun x y => ?_, GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd, ?_, fun a x y => ?_,
    fun e a u he hu => ?_, fun x y hx hy => (GlobalTheory.OrientedHeis.symplOH_fin_real hy hx).2⟩
  · unfold symplOH
    rw [← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]
  · rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩
    exact ⟨_, symplOH_rat M N⟩
  · unfold symplOH symplO
    rw [hO_mul_left, hO_mul_right, GlobalTheory.DualPairCheck.cA_cA]
  · unfold symplOH symplO
    rw [hO_mul_left, hO_half e u he hu, mul_zero, mul_zero, LinearMap.map_zero, mul_zero]

end GlobalTheory.OrientedFormLaws
