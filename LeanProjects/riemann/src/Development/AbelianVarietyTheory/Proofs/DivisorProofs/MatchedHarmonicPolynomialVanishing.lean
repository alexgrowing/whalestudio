import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensInclInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBMatchedThetaLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl

noncomputable section

open scoped Classical

namespace GlobalTheory.HarmKStab

variable {P Q R S : ℕ}

theorem fockAct2_mem_harmTy (x : ℚ) (Y : Mat R S) (hY : IsKC Y) {f : Formalism.BasicNotions.TH.Pol P Q R S}
    (hf : f ∈ harmTy P Q R S x) : fockAct2 P Q R S Y f ∈ harmTy P Q R S x := by
  have hH := GlobalTheory.T.fockHarmonics_graded_compactStable P Q R S _ (Or.inl rfl)
  induction hf using Submodule.span_induction with
  | mem g hg =>
    refine Submodule.subset_span ⟨?_, fun X hX => ?_⟩
    · have h1 : fockAct2 P Q R S Y g ∈ Submodule.span ℂ (GlobalTheory.FockAlg.harm1 P Q R S) :=
        hH.2.2.1 Y hY g (Submodule.subset_span hg.1)
      rw [← hH.1]; exact h1
    · have hc := (GlobalTheory.FockPair.pair_lie_commute P Q R S).2.2 X Y
      have e := congrArg (fun L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S) => L g) hc
      simp only [Module.End.mul_apply] at e
      rw [e, hg.2 X hX, map_smul]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

section Tens

variable (F : Type) [Field F] [NumberField F]

theorem atPl_mem_tensHarm (x : InfinitePlace F → ℚ) (w : InfinitePlace F) (Y : Mat R S) (hY : IsKC Y)
    {T : Tens F P Q R S} (hT : T ∈ tensHarm F P Q R S x) :
    atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y) T ∈ tensHarm F P Q R S x := by
  induction hT using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨f, hf, rfl⟩ := hg
    refine Submodule.subset_span ⟨fun i => Function.update (fun _ => (LinearMap.id : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))) w
      (fockAct2 P Q R S Y) i (f i), fun i => ?_, ?_⟩
    · by_cases h : i = w
      · subst h; simpa using fockAct2_mem_harmTy (x i) Y hY (hf i)
      · simpa [Function.update_of_ne h] using hf i
    · simp [atPl, PiTensorProduct.map_tprod]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem genOp_mem_tensHarm (x : InfinitePlace F → ℚ) (c : InfinitePlace F → ℂ) (Yg : InfinitePlace F → Mat R S)
    (hY : ∀ w, IsKC (Yg w)) {T : Tens F P Q R S} (hT : T ∈ tensHarm F P Q R S x) :
    GlobalTheory.FockBottom.genOp P Q c Yg T ∈ tensHarm F P Q R S x := by
  rw [GlobalTheory.FockBottom.genOp_apply]
  exact Submodule.sum_mem _ fun w _ =>
    Submodule.add_mem _ (atPl_mem_tensHarm F x w (Yg w) (hY w) hT) (Submodule.smul_mem _ _ hT)

end Tens

theorem kInf_mem_tensHarm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (Rm : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' Rm Rf →
    ∀ (P Q Rn Sn : ℕ) (A : InfinitePlace F → Matrix (Fin a) (Ix P Q) ℂ) (C : InfinitePlace F → Matrix (Fin (a + a')) (Ix Rn Sn) ℂ)
      (Φ : Tens F P Q Rn Sn →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))), GlobalTheory.FockBridge.IsFockData B G.M A C Φ →
      ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ (tensHarm F P Q Rn Sn (halfKap B)).map Φ, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
        Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ (tensHarm F P Q Rn Sn (halfKap B)).map Φ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' Rm Rf hM P Q Rn Sn A C Φ hD k hk f hf f₁ hf₁
  obtain ⟨T, hT, rfl⟩ := Submodule.mem_map.1 hf
  obtain ⟨Yg, U, hKC, hU, hA⟩ := GlobalTheory.FockBottom.exp_of_kInf hM.triple.base.cm hD.1.1.2.2 hD.1.2.2
    (GlobalTheory.FockBottom.actsBy_second hKP hM.triple hD) (GlobalTheory.FockBottom.admissible_weil_action hM.triple) hk
  rw [GlobalTheory.FockBottom.acts_unique hf₁ (hA T)]
  exact Submodule.mem_map_of_mem
    (GlobalTheory.FockBottom.isExp_mem hU _ (fun v hv => genOp_mem_tensHarm F _ _ Yg hKC hv) hT)

end GlobalTheory.HarmKStab
