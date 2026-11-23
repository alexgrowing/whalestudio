import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSphericalStabilizerPreservesLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_snd_one_sub_idemS :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) => sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) atTop (𝓝 0) := by
  classical
  have hin : ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) w, w ∈ T → evalV F w (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) = 0 := by
    intro T w hw
    change evFin F w (1 - GlobalTheory.FinDecomp.idemS F T) = 0
    rw [map_sub, map_one, GlobalTheory.FinDecomp.evFin_idemS, if_pos hw, sub_self]
  have hint : ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) w,
      evalV F w (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) ∈ w.adicCompletionIntegers F := by
    intro T w
    change evFin F w (1 - GlobalTheory.FinDecomp.idemS F T) ∈ w.adicCompletionIntegers F
    rw [map_sub, map_one, GlobalTheory.FinDecomp.evFin_idemS]
    split_ifs
    · rw [sub_self]; exact zero_mem _
    · rw [sub_zero]; exact one_mem _
  let A : ∀ w : HeightOneSpectrum (𝓞 F), Set (w.adicCompletion F) := fun w => w.adicCompletionIntegers F
  let o : ∀ w, A w := fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩
  let g : Finset (HeightOneSpectrum (𝓞 F)) → ∀ w, A w := fun T w => ⟨_, hint T w⟩
  have hg : Tendsto g atTop (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({w} : Finset _)] with T hT
    exact Subtype.ext (hin T w (hT (Finset.mem_singleton_self w))).symm
  have h := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  exact h

end GlobalTheory.FinDecompLim
end

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_infIdem : At (evI F) (pairA F 1 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * 1, u.2 * 0) = (0, 0)
  rw [h1, zero_mul, mul_zero]

theorem one_sub_idemS_eq (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) :
    1 - GlobalTheory.FinDecomp.idemS F T = pairA F 1 0 + pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) := by
  have h := GlobalTheory.FinDecomp.fst_idemS (F := F) T
  refine Prod.ext ?_ ?_
  · change 1 - fstA F (GlobalTheory.FinDecomp.idemS F T) = 1 + 0
    rw [h, sub_zero, add_zero]
  · change sndA F (1 - GlobalTheory.FinDecomp.idemS F T) = 0 + sndA F (1 - GlobalTheory.FinDecomp.idemS F T)
    rw [zero_add]

theorem tendsto_cut :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) => pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T))) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (0 : Ainf F))).prodMk_nhds (tendsto_snd_one_sub_idemS (F := F))
  exact h

theorem tendsto_phi {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE F E)) (hM : pairA F 1 0 • (M - 1) = 0) :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) => GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M) atTop (𝓝 M) := by
  have key : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M =
      M + pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) • (1 - M) := by
    intro T
    have h0 : pairA F 1 0 • (1 - M) = 0 := by rw [← neg_sub, smul_neg, hM, neg_zero]
    have h1 : GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M = M + (1 - GlobalTheory.FinDecomp.idemS F T) • (1 - M) := by
      simp only [GlobalTheory.FinDecomp.phi, sub_smul, smul_sub, one_smul]; abel
    rw [h1, congrArg (· • (1 - M)) (one_sub_idemS_eq T), add_smul, h0, zero_add]
  simp_rw [key]
  have h := (tendsto_const_nhds (x := M)).add ((tendsto_cut (F := F)).smul_const (1 - M))
  have e : M + (0 : AF F) • (1 - M) = M := by rw [zero_smul, add_zero]
  rw [e] at h
  exact h

end GlobalTheory.FinDecompLim
end

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

theorem tendsto_loc_idemS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J),
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K - 1) = 0) →
    Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) =>
      GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idemS F T) (GlobalTheory.FinDecomp.idemS_mul_self T) K) Filter.atTop (nhds K) := by
  intro F E _ _ _ _ _ σ d J K hK
  have hM : pairA F 1 0 • (mat K - 1) = 0 := hK _ at_infIdem
  have hN : pairA F 1 0 • (mat K⁻¹ - 1) = 0 := by
    have h : mat K⁻¹ - 1 = mat K⁻¹ * (1 - mat K) := by
      rw [Matrix.mul_sub, Matrix.mul_one, GlobalTheory.FinDecomp.mat_inv_mul]
    rw [h, ← Matrix.mul_smul, ← neg_sub (mat K), smul_neg, hM, neg_zero, Matrix.mul_zero]
  rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  change Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) =>
      (GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) (mat K),
        MulOpposite.op (GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) (mat K⁻¹)))) atTop
      (𝓝 (mat K, MulOpposite.op (mat K⁻¹)))
  exact (tendsto_phi _ hM).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (tendsto_phi _ hN))

end GlobalTheory.FinDecompLim
end
