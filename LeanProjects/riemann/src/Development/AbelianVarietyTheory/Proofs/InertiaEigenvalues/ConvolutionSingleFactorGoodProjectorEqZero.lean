import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.DownLift

theorem conv_single_prod_eq_zero {ι : Type} [Fintype ι] {Γ : ι → Type} [∀ i, Group (Γ i)]
    [∀ i, Finite (Γ i)] (G : Type) [Group G] [Fintype G] (eR : G ≃* (∀ i, Γ i)) (i0 : ι)
    (M : MonoidAlgebra ℂ (Γ i0)) (E : ∀ i, MonoidAlgebra ℂ (Γ i)) (hM : M * E i0 = 0) (x : G) :
    ∑ y : G, (open Classical in if ∀ i, i ≠ i0 → eR y i = 1 then M.coeff (eR y i0) else 0) *
      ∏ i, (E i).coeff (eR (y⁻¹ * x) i) = 0 := by
  classical
  haveI : Fintype (Γ i0) := Fintype.ofFinite _
  have hinj : Function.Injective (fun z : Γ i0 => eR.symm (Pi.mulSingle i0 z)) :=
    eR.symm.injective.comp (Pi.mulSingle_injective i0)
  rw [← Fintype.sum_of_injective (fun z : Γ i0 => eR.symm (Pi.mulSingle i0 z)) hinj
    (fun z => (M.coeff z * (E i0).coeff (z⁻¹ * eR x i0)) *
      ∏ i ∈ Finset.univ.erase i0, (E i).coeff (eR x i))]
  · rw [← Finset.sum_mul]
    have h := MonoidAlgebra.coeff_mul_apply_left M (E i0) (eR x i0)
    rw [hM, Finsupp.sum_fintype _ _ (by simp)] at h
    rw [← h]; simp
  · intro y hy
    rw [if_neg, zero_mul]
    intro h
    apply hy
    refine ⟨eR y i0, ?_⟩
    simp only
    rw [MulEquiv.symm_apply_eq]
    funext i
    by_cases hi : i = i0
    · subst hi; simp
    · rw [Pi.mulSingle_eq_of_ne hi, h i hi]
  · intro z
    rw [if_pos, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0), mul_assoc]
    · congr 1
      · simp
      · congr 1
        · simp
        · refine Finset.prod_congr rfl fun i hi => ?_
          have hi' := Finset.ne_of_mem_erase hi
          simp [Pi.mulSingle_eq_of_ne hi']
    · intro i hi
      simp [Pi.mulSingle_eq_of_ne hi]

theorem conv_single_goodProj_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (eR : G ≃* G0g D.nd) (kv0 : Σ k : Fin 2, D.nd.PlG k),
    haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
    ∀ M : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv0.1))),
    (∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) →
      M * D.ntypes.eSer kv0.1 (Formalism.CyclotomicNorms.monicOf (a kv0)) = 0) → ∀ x : G,
    ∑ y : G, (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then M.coeff (eR y kv0) else 0) *
      D.ntypes.e0.coeff (eR (y⁻¹ * x)) = 0 := by
  intro D G _ _ eR kv0 M hM x
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fintype (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))) :=
    Fintype.ofFinite _
  have he : ∀ g : G0g D.nd, D.ntypes.e0.coeff g =
      ∑ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
      (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0) := by
    intro g
    rw [← finsum_eq_sum_of_fintype]
    rfl
  simp only [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with ha
  · haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
    have := conv_single_prod_eq_zero (Γ := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
      G eR kv0 M (fun kv => D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) (hM a ha) x
    convert this
  · simp

end GlobalTheory.DownLift
