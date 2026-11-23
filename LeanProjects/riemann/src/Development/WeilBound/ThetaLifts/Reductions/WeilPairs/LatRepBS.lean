import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB_A
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SumFourEqTrace
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsMore
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeNotDvdRelIndexSplitPlace

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {nS nT : ℕ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

variable (F) in

def inrA : Af F →ₗ[F] AF F where
  toFun a := pairA F 0 a
  map_add' _ _ := Prod.ext (add_zero 0).symm rfl
  map_smul' c _ := Prod.ext (smul_zero c).symm rfl

variable (F E) in

def liftF : Af F ⊗[F] E →ₗ[F] AEF F E := TensorProduct.map (inrA F) LinearMap.id

theorem liftF_tmul (a : Af F) (t : E) : liftF F E (a ⊗ₜ[F] t) = pairA F 0 a ⊗ₜ[F] t := rfl

variable (E) in

abbrev hatO : AddSubgroup (Af F ⊗[F] E) := GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E))

theorem fin_mul_eq (y : AEF F E) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) * y = liftF F E (finPartF F E y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a t =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      show finPartF F E (a ⊗ₜ[F] t) = sndA F a ⊗ₜ[F] t from rfl, liftF_tmul]
    congr 1
    exact Prod.ext (zero_mul _) (one_mul _)
  | add x y hx hy => rw [mul_add, hx, hy, map_add, map_add]

theorem liftF_smul_mem {z : Af F ⊗[F] E} (hz : z ∈ hatO (F := F) E) {u : WOF F E nS nT}
    (hu : u ∈ latOF F E nS nT Λ) : liftF F E z • u ∈ latOF F E nS nT Λ := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨b, rfl⟩, rfl⟩ := hz
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨α, hα, γ, hγ, rfl⟩ := hu
      refine AddSubgroup.subset_closure ⟨a * α, fun v => GlobalTheory.AdLat.adele_mul_integral F (ha v) (hα v),
        b • γ, Λ.smul_mem b hγ, ?_⟩
      ext i j
      simp only [liftF_tmul, Matrix.smul_apply, smul_eq_mul, ratWF, Matrix.map_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      show (pairA F 0 a ⊗ₜ[F] (b : E)) * ((pairA F 0 α ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] γ i j)) =
        (pairA F 0 (a * α) ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] ((b • γ) i j))
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul, one_mul, Matrix.smul_apply]
      congr 1
      exact Prod.ext (mul_zero _) rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  | zero => rw [map_zero, zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, neg_smul]; exact neg_mem hx

theorem idem_smul_mem {e : AEF F E} (he : e * e = e) (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e)
    {u : WOF F E nS nT} (hu : u ∈ latOF F E nS nT Λ) : e • u ∈ latOF F E nS nT Λ := by
  have h1 : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, he])
  rw [← hf, fin_mul_eq]
  exact liftF_smul_mem h1 hu

theorem fin_of_place {e : AEF F E} {α : Af F} (h : algebraMap (AF F) (AEF F E) (pairA F 0 α) * e = e) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e := by
  rw [← h, ← mul_assoc, ← map_mul]
  congr 2
  exact Prod.ext (zero_mul _) (one_mul _)

theorem split_parts {e : AEF F E} (he : IsSplitIdemF σ e) :
    (algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) ∧
      (algebraMap (AF F) (AEF F E) (pairA F 0 1) * cAF σ e = cAF σ e) ∧ cAF σ e * cAF σ e = cAF σ e := by
  obtain ⟨hee, hec, v, ε, ⟨α, rfl, -⟩, hs⟩ := he
  have hce : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, hee]
  refine ⟨fin_of_place (α := α) ?_, fin_of_place (α := α) ?_, hce⟩
  · rw [← hs, add_mul, hee, mul_comm, hec, add_zero]
  · rw [← hs, add_mul, hec, hce, zero_add]

end PositivityTheory.ThKW.LatB

end
