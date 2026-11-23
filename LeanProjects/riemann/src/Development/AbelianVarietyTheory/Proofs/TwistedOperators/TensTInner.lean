import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Wsub (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) :
    Submodule ℂ (X.B.H (X.pl.symm τ)) :=
  ((MP R).sm τ).map ((c τ).toLinearEquiv.toLinearMap)

theorem symm_mem_sm (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) (y : Wsub R X c τ) :
    (c τ).symm (y : X.B.H (X.pl.symm τ)) ∈ (MP R).sm τ := by
  obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 y.2
  have : (c τ).symm (y : X.B.H (X.pl.symm τ)) = w := by
    rw [← hwy]
    exact (c τ).symm_apply_apply w
  rw [this]
  exact hw

def vecOf (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (y : ∀ τ, Wsub R X c τ) : (MP R).Vec :=
  fun τ => ⟨(c τ).symm (y τ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (y τ)⟩

def tensT {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (y : ∀ τ, X.B.H (X.pl.symm τ)) : X.B.Hs :=
  X.B.tens (Equiv.piCongrLeft X.B.H X.pl.symm y)

open Classical in

def evF (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R))
    (y : ∀ τ, Wsub R X c τ) : L2X X :=
  star (if hm : MemLp (fun x => ev (MP R) (vecOf R X c y) S
      (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X)
    then hm.toLp _ else 0)

end GlobalTheory.RowEvalHH

namespace GlobalTheory.RowEvalHH

theorem tensT_inner {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (a b : ∀ τ, X.B.H (X.pl.symm τ)) :
    ⟪tensT X a, tensT X b⟫_ℂ = ∏ τ, ⟪a τ, b τ⟫_ℂ := by
  unfold tensT
  rw [X.B.tens_spec.1]
  rw [← Equiv.prod_comp X.pl.symm]
  simp only [Equiv.piCongrLeft_apply_apply]

theorem tensT_dense {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    Dense (Submodule.span ℂ (Set.range (tensT X)) : Set X.B.Hs) := by
  have : Set.range (tensT X) = Set.range X.B.tens :=
    (Equiv.piCongrLeft X.B.H X.pl.symm).surjective.range_comp X.B.tens
  rw [this]
  exact X.B.tens_spec.2.2

theorem tensT_w {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    tensT X (fun τ => X.B.w (X.pl.symm τ)) = X.B.tens X.B.w := by
  unfold tensT
  congr 1
  have : (fun τ => X.B.w (X.pl.symm τ)) = (Equiv.piCongrLeft X.B.H X.pl.symm).symm X.B.w := by
    funext τ
    rw [Equiv.piCongrLeft_symm_apply]
  rw [this, Equiv.apply_symm_apply]

end GlobalTheory.RowEvalHH

namespace GlobalTheory.RowEvalHH

theorem Wsub_dense {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) :
    Dense (Wsub R X c τ : Set (X.B.H (X.pl.symm τ))) := by
  unfold Wsub
  rw [Submodule.map_coe]
  exact (c τ).surjective.denseRange.dense_image (c τ).continuous (Formalism.IndefR.SchurOrthogonalityAlt.sm_dense (MP R) τ)

end GlobalTheory.RowEvalHH
