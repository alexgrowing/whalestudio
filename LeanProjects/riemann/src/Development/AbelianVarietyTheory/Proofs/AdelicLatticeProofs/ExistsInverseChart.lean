import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmType
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealLineAt

theorem exists_inverse_chart {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) :
    ∃ σ : (D.what₂.Tau → ℂ) →+ AE D, GlobalTheory.FockCompare.Chart θ σ := by
  obtain ⟨ρ, h1, h2, h3⟩ := GlobalTheory.FockCompare.exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  exact GlobalTheory.FockCompare.RealChart.exists_chart D θ hθ ρ h1 h2 h3

open Classical in

def ray {ι : Type} (τ : ι) (c : ℂ) : ℝ →+ (ι → ℂ) where
  toFun t := fun τ' => if τ' = τ then (t : ℂ) * c else 0
  map_zero' := by funext τ'; simp
  map_add' s t := by
    funext τ'
    simp only [Pi.add_apply]
    split_ifs <;> simp [add_mul]

theorem continuous_ray {ι : Type} (τ : ι) (c : ℂ) : Continuous (ray τ c) := by
  refine continuous_pi fun τ' => ?_
  by_cases h : τ' = τ
  · have : (fun t : ℝ => ray τ c t τ') = fun t : ℝ => (t : ℂ) * c := funext fun t => if_pos h
    rw [this]
    exact Complex.continuous_ofReal.mul continuous_const
  · have : (fun t : ℝ => ray τ c t τ') = fun _ : ℝ => (0 : ℂ) := funext fun t => if_neg h
    rw [this]
    exact continuous_const

theorem lineAt_exists (D : D7) : LineAtExists D := by
  intro θ hθ m n τ z
  obtain ⟨σ, hσ⟩ := exists_inverse_chart hθ
  let L : ℝ →+ Mx D m n :=
    { toFun := fun t => Matrix.of fun i j => σ (ray τ (z i j) t)
      map_zero' := by
        funext i j
        show σ (ray τ (z i j) 0) = 0
        rw [(ray τ (z i j)).map_zero, σ.map_zero]
      map_add' := fun s t => by
        funext i j
        show σ (ray τ (z i j) (s + t)) = σ (ray τ (z i j) s) + σ (ray τ (z i j) t)
        rw [(ray τ (z i j)).map_add, σ.map_add] }
  refine ⟨L, ?_, fun t => ?_, fun t τ' => ?_⟩
  · exact continuous_pi fun i => continuous_pi fun j => hσ.cont.comp (continuous_ray τ (z i j))
  · funext i j
    exact hσ.fin _
  · funext i j
    refine (hσ.comp (ray τ (z i j) t) τ').trans ?_
    by_cases h : τ' = τ
    · rw [if_pos h]
      exact if_pos h
    · rw [if_neg h]
      exact if_neg h

theorem lineAt_unique (D : D7) : LineAtUnique D := by
  intro θ hθ m n τ z L L' hL hL'
  obtain ⟨σ, hσ⟩ := exists_inverse_chart hθ
  refine AddMonoidHom.ext fun t => ?_
  funext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ' => ?_)
  · have e1 : finPart D (L t i j) = 0 := congrFun (congrFun (hL.2.1 t) i) j
    have e2 : finPart D (L' t i j) = 0 := congrFun (congrFun (hL'.2.1 t) i) j
    rw [RingHom.map_sub, e1, e2, sub_zero]
  · have e : θ τ' (infPart D (L t i j)) = θ τ' (infPart D (L' t i j)) :=
      congrFun (congrFun ((hL.2.2 t τ').trans (hL'.2.2 t τ').symm) i) j
    rw [RingHom.map_sub, RingHom.map_sub, e, sub_self]

theorem lineAt_exists_unique : ∀ D : D7, LineAtExists D ∧ LineAtUnique D :=
  fun D => ⟨lineAt_exists D, lineAt_unique D⟩

end GlobalTheory.RealLineAt

end
