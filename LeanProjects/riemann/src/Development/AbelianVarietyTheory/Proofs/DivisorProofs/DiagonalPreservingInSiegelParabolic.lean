import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralKeepsDoublingDiagonalAdicCompletio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormCmExtensionSplitPlaceEqZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

namespace GlobalTheory.ThK.SplitSiegel

theorem keepsDiag_map_of_sub_one {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    {M : Matrix (Fin (n + n)) (Fin (n + n)) A} (h : ∀ i j, f ((M - 1) i j) = 0) :
    KeepsDiag finSumFinEquiv (M.map f) := by
  have e : M.map f = 1 := by
    ext i j
    have h1 := h i j
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h1
    rw [Matrix.map_apply, h1, Matrix.one_apply, Matrix.one_apply, apply_ite f, map_one, map_zero]
  rw [e]
  exact mem_stabGL_diagSub.1 (one_mem (Formalism.UG.stabGL (diagSub B (finSumFinEquiv (m := n) (n := n)))))

theorem mem_siegel_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (X₂ : Spc F E (n + n)), J.det ≠ 0 → X₂.J = dblGram finSumFinEquiv J → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (p : UA σ X₂.J), p ∈ UAt σ X₂ (evFin F v) → KeepsDiag finSumFinEquiv ((mat p).map (piW t)) → p ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype := by
  intro F E _ _ _ _ _ σ hcm n J X₂ hJ hQ v t p hp hk
  have hent : ∀ i j, At (evFin F v) ((mat p - 1) i j) := fun i j u hu => congrFun (congrFun (hp u hu) i) j
  have hQ' : X₂.Jᵀ = dblGram finSumFinEquiv Jᵀ := by rw [hQ, GlobalTheory.DblIwasawa.transpose_dblGram]
  have key : (GlobalTheory.IwLine.ofGAd σ X₂.J).symm p ∈ siegelH (AF F) σ X₂.Jᵀ := by
    refine mem_siegelH_adelic.2 ⟨fun w => mem_siegelOf.2 ?_, fun u => ?_⟩
    · exact keepsDiag_map_of_sub_one (compInf F E w : AE F E →+* _) fun i j => (at_evFin_iff.1 (hent i j)).1 w
    · by_cases hu : u = v
      · subst hu
        exact GlobalTheory.Core.Rk.IwSplit.mem_siegelH_of_split hcm hQ' (by rwa [Matrix.det_transpose]) t
          (mem_stabGL_diagSub.2 hk)
      · exact mem_siegelOf.2 (keepsDiag_map_of_sub_one (compFin F E u : AE F E →+* _)
          fun i j => (at_evFin_iff.1 (hent i j)).2 u hu)
  exact mem_siegelOf.2 (mem_siegelOf.1 key)

end GlobalTheory.ThK.SplitSiegel
