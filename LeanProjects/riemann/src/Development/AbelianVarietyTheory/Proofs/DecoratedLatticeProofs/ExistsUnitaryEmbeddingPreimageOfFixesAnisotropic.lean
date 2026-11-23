import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory

theorem mt_jB_eq_of_fixes_lineVec (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (k : GA D S) (hk : mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ)) :
    mt S k ⬝ o.jB = o.jB := by
  obtain ⟨hL, hq⟩ := hζ
  obtain ⟨j0, hall⟩ : ∃ j0 : Fin L.rank, ∀ j : Fin L.rank, j = j0 :=
    ⟨⟨0, by omega⟩, fun j => Fin.ext (by have := j.isLt; show j.val = 0; omega)⟩
  have hζ0 : ζ j0 ≠ 0 := by
    intro h0
    apply hq
    have : ζ = 0 := funext fun j => by rw [hall j, h0]; rfl
    simp [this]
  have hv : ratV (o.iB *ᵥ ζ) = o.jB *ᵥ ratV ζ := by
    funext i; exact RingHom.map_mulVec (incA D) o.iB ζ i
  rw [hv, Matrix.mulVec_mulVec] at hk
  have hM : (mt S k ⬝ o.jB - o.jB) *ᵥ ratV ζ = 0 := by rw [Matrix.sub_mulVec, hk, sub_self]
  rw [← sub_eq_zero]
  funext i j
  rw [hall j]
  have h1 := congrFun hM i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
  rw [Fintype.sum_eq_single j0 (fun j hj => absurd (hall j) hj)] at h1
  have hu : incA D (ζ j0) * incA D (ζ j0)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hζ0, map_one]
  have e : (mt S k ⬝ o.jB - o.jB) i j0 = (mt S k ⬝ o.jB - o.jB) i j0 * ratV ζ j0 * incA D (ζ j0)⁻¹ := by
    rw [mul_assoc]; show _ = _ * (incA D (ζ j0) * _); rw [hu, mul_one]
  rw [e, h1, zero_mul]; rfl

theorem mat_eq_of_splitting {R : Type} [CommRing R] {n a b : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (jA : Matrix (Fin n) (Fin a) R) (pA : Matrix (Fin a) (Fin n) R) (jB : Matrix (Fin n) (Fin b) R)
    (pB : Matrix (Fin b) (Fin n) R) (H : Matrix (Fin a) (Fin a) R) (hX : M * jA = jA * H) (hfix : M * jB = jB)
    (hsum : jA * pA + jB * pB = 1) : M = jA * H * pA + jB * pB := by
  calc M = M * (jA * pA + jB * pB) := by rw [hsum, Matrix.mul_one]
    _ = M * jA * pA + M * jB * pB := by rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = jA * H * pA + jB * pB := by rw [hX, hfix]

theorem exists_emb_of_mt_jB_eq (D : D7) (S A B : HSp D) (o : OrthDec S A B) (k : GA D S)
    (hfix : mt S k ⬝ o.jB = o.jB) : ∃ h : GA D A, k = o.emb (h, 1) := by
  have hu : adj (mt S k) ⬝ (gA S ⬝ mt S k) = gA S := GlobalTheory.MixModel.mt_unitary S k
  have hBA : adj o.jB ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = 0 := by
    calc adj o.jB ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = adj (mt S k ⬝ o.jB) ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) := by rw [hfix]
      _ = adj o.jB ⬝ (gA S ⬝ o.jA) := by
        rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu o.jA]
      _ = 0 := o.gram_BA
  have hpB : o.pB ⬝ (mt S k ⬝ o.jA) = 0 := by
    rw [o.pB_eq, Matrix.mul_assoc, Matrix.mul_assoc, hBA, Matrix.mul_zero]
  have hX : mt S k ⬝ o.jA = o.jA ⬝ (o.pA ⬝ (mt S k ⬝ o.jA)) := by
    calc mt S k ⬝ o.jA = (o.jA ⬝ o.pA + o.jB ⬝ o.pB) ⬝ (mt S k ⬝ o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA ⬝ (o.pA ⬝ (mt S k ⬝ o.jA)) + o.jB ⬝ (o.pB ⬝ (mt S k ⬝ o.jA)) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by rw [hpB, Matrix.mul_zero, add_zero]
  have e1 : adj (mt S k ⬝ o.jA) ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = gA A := by
    rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu o.jA]
    exact o.gram_AA
  set H := o.pA ⬝ (mt S k ⬝ o.jA) with hHdef
  have e2 : adj (o.jA ⬝ H) ⬝ (gA S ⬝ (o.jA ⬝ H)) = adj H ⬝ (gA A ⬝ H) := by
    rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ o.gram_AA H]
  rw [← hX] at e2
  have hH : adj H * (gA A * H) = gA A := e2.symm.trans e1
  refine ⟨GlobalTheory.MixModel.ofMat A H hH, GlobalTheory.MixModel.mt_injective S ?_⟩
  rw [o.mt_emb, GlobalTheory.MixModel.mt_ofMat, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  exact mat_eq_of_splitting (mt S k) o.jA o.pA o.jB o.pB H hX hfix o.sum_eq_one

theorem exists_emb_of_fixes_lineVec (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (k : GA D S) (hk : mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ)) :
    ∃ h : GA D A, k = o.emb (h, 1) :=
  exists_emb_of_mt_jB_eq D S A L o k (mt_jB_eq_of_fixes_lineVec D S A L o ζ hζ k hk)

end GlobalTheory
