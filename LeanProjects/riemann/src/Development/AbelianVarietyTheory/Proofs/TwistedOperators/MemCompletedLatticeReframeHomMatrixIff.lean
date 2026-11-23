import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.Lat

variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem gram_reS_eq : (reS S b).gram = (frP S b)ᴴ * S.gram * frP S b := by
  refine Matrix.ext fun (i j : Fin S.rank) => ?_
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k =>
    (Module.Basis.sum_toMatrix_smul_self S.frame b k).symm
  show S.hT (b i) (b j) = ∑ k, (∑ l, star (frP S b l i) * S.gram l k) * frP S b k j
  rw [hb i, hb j]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    HSpace.gram, Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem sum_frameMatrix_mulVec_smul (s' : Fin S.rank → D.host.E) :
    ∑ k, (frP S b *ᵥ s') k • S.frame k = ∑ a, s' a • b a := by
  have hb : ∀ a, b a = ∑ l, frP S b l a • S.frame l := fun a =>
    (Module.Basis.sum_toMatrix_smul_self S.frame b a).symm
  simp only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem mem_L0c_iff_mem_intVec_of_span_frame (s' : Fin S.rank → D.host.E) : s' ∈ L0c D (reS S b) ↔ frP S b *ᵥ s' ∈ L0c D S := by
  show ∑ a, s' a • b a ∈ S.L0 ↔ ∑ k, (frP S b *ᵥ s') k • S.frame k ∈ S.L0
  rw [sum_frameMatrix_mulVec_smul]

theorem reW_gen (X : AF D.host.F) (a : D.host.E) (t : Fin T.rank → D.host.E) (s' : Fin S.rank → D.host.E) :
    reW S T b (Matrix.of fun i j => X ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s' k) * (reS S b).gram k j)) =
      Matrix.of fun i j => X ⊗ₜ[D.host.F] (a * t i * ∑ k, star ((frP S b *ᵥ s') k) * S.gram k j) := by
  have h0 : ∀ G' : Matrix (Fin S.rank) (Fin S.rank) D.host.E, G' = (frP S b)ᴴ * S.gram * frP S b →
      (star s' ᵥ* G') ᵥ* frPinv S b = star (frP S b *ᵥ s') ᵥ* S.gram := by
    rintro G' rfl
    rw [Matrix.vecMul_vecMul, Matrix.mul_assoc, frameMatrix_mul_frameMatrixInv, Matrix.mul_one,
      Matrix.star_mulVec, Matrix.vecMul_vecMul]
  have h1 := h0 (reS S b).gram (gram_reS_eq S b)
  have hv : ∀ j, ∑ c, (∑ k, star (s' k) * (reS S b).gram k c) * frPinv S b c j =
      ∑ k, star ((frP S b *ᵥ s') k) * S.gram k j := fun j => congrFun h1 j
  ext i j
  change ∑ c, X ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s' k) * (reS S b).gram k c) * incA D (frPinv S b c j) = _
  rw [Matrix.of_apply, ← hv j, Finset.mul_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  show X ⊗ₜ[D.host.F] _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc]

theorem map_latO (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) :
    (latO (reS S b) T (L0c D (reS S b)) LT P).map (reWHom S T b) = latO S T (L0c D S) LT P := by
  unfold latO
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨w', ⟨α, hα, hP, a, ha, s', hs', t, ht, rfl⟩, rfl⟩
    exact ⟨α, hα, hP, a, ha, _, (mem_L0c_iff_mem_intVec_of_span_frame S b s').1 hs', t, ht, reW_gen S T b _ a t s'⟩
  · rintro ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    have hs' : frP S b *ᵥ (frPinv S b *ᵥ s) = s := by
      rw [Matrix.mulVec_mulVec, frameMatrix_mul_frameMatrixInv, Matrix.one_mulVec]
    refine ⟨_, ⟨α, hα, hP, a, ha, frPinv S b *ᵥ s, (mem_L0c_iff_mem_intVec_of_span_frame S b _).2 (hs'.symm ▸ hs), t, ht, rfl⟩, ?_⟩
    have key : ∀ s' s : Fin S.rank → D.host.E, frP S b *ᵥ s' = s →
        reW S T b (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
          (a * t i * ∑ k, star (s' k) * (reS S b).gram k j)) =
        Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
      rintro s' s rfl
      exact reW_gen S T b _ a t s'
    exact key _ _ hs'

end GlobalTheory.AdSpan.ReVec.Lat

open GlobalTheory.AdSpan.ReVec.Lat in

theorem GlobalTheory.AdSpan.ReVec.latO_reW_iff : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (LT : Set (Fin T.rank → D.host.E)) (u : WO (reS S b) T),
    u ∈ latO (reS S b) T (L0c D (reS S b)) LT (fun _ => True) ↔
      reW S T b u ∈ latO S T (L0c D S) LT (fun _ => True) := by
  intro D S T b LT u
  rw [← map_latO S T b LT]
  exact (AddSubgroup.mem_map_iff_mem (f := reWHom S T b) (reW_bijective S T b).1).symm

end
