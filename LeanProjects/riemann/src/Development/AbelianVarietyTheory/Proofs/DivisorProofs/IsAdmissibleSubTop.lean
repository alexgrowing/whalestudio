import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeHW
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.PsCo.TrAdm

open ReciprocityTheory.ChartRestriction.DS CompanionTheory.D.gk.HC GlobalTheory.HcPort Formalism.MainNotions.S

section

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kfSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ (smD ε σ) where
  carrier := KF ε σ
  add_mem' := by
    rintro a b ⟨S, hS, ha, hSK⟩ ⟨T, hT, hb, hTK⟩
    refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup ha hb, fun g hg v hv => ?_⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hv
    rw [← hxy, map_add]
    exact Submodule.add_mem_sup (hSK g hg x hx) (hTK g hg y hy)
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact Submodule.zero_mem _⟩
  smul_mem' := fun c _ ⟨S, hS, ha, hSK⟩ => ⟨S, hS, by simpa using S.smul_mem c ha, hSK⟩

theorem kStableSub_iSup {ι : Type} {E : Fin n → Fin n → Module.End ℂ (smD ε σ)} (S : ι → Submodule ℂ (smD ε σ))
    (h : ∀ i, IsKStableSub ε E (S i)) : IsKStableSub ε E (⨆ i, S i) := by
  intro a b hab x hx
  refine Submodule.iSup_induction S (motive := fun x => E a b x ∈ ⨆ i, S i) hx (fun i y hy => ?_) ?_ ?_
  · exact Submodule.mem_iSup_of_mem i (h i a b hab y hy)
  · simp
  · intro y z hy hz; rw [map_add]; exact Submodule.add_mem _ hy hz

end

theorem isAdmissibleSub_top (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : GlobalTheory.GKModule.IsAdmissibleSub ε σ ⊤ := by
  classical
  intro Λ
  have hD := isDerivedOn_smE hσ
  set A := {v : smD ε σ | v ∈ KF ε σ ∧ IsKHWVec ε (smE ε σ) Λ v}
  have hAf : FiniteDimensional ℂ (Submodule.span ℂ A) := uAdm n ε H σ hσ hirr Λ
  have hAK : Submodule.span ℂ A ≤ kfSub ε σ := Submodule.span_le.2 fun v hv => hv.1
  let b := Module.finBasis ℂ (Submodule.span ℂ A)
  let M : Submodule ℂ (smD ε σ) := ⨆ i, Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)
  have hbi : ∀ i, FiniteDimensional ℂ (Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)) ∧
      IsKStableSub ε (smE ε σ) (Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)) := fun i =>
    kSpan_fin_B K_finite_smooth_vectors hσ hirr (hAK (b i).2)
  haveI : ∀ i, FiniteDimensional ℂ (Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)) := fun i => (hbi i).1
  have hMf : FiniteDimensional ℂ M := Submodule.finiteDimensional_iSup _
  have hMK : IsKStableSub ε (smE ε σ) M := kStableSub_iSup _ fun i => (hbi i).2
  have hAM : Submodule.span ℂ A ≤ M := by
    intro x hx
    have h1 := congrArg (fun z : Submodule.span ℂ A => (z : smD ε σ)) (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem i (Formalism.REAL.mem_compact_span_self _))
  let T : Submodule ℂ H := M.map (smD ε σ).subtype
  have hTf : FiniteDimensional ℂ T := Module.Finite.map _ _
  have hTK := kStable_of_isKStableSub hσ hD M hMf hMK
  refine Submodule.finiteDimensional_of_le (S₂ := T) (sSup_le fun S hS' => ?_)
  have hS := hS'.2
  obtain ⟨hSf, hSK, hirrS, -, -⟩ := id hS
  have hSD : S ≤ smD ε σ := fun v hv => (K_finite_smooth_vectors n ε H σ hσ hirr).1 v ⟨S, hSf, hv, hSK⟩
  obtain ⟨w, hwS, hw0, hwΛ⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hS hSD
  have hwA : w ∈ A := ⟨⟨S, hSf, hwS, hSK⟩, hwΛ⟩
  have hwM : w ∈ M := hAM (Submodule.subset_span hwA)
  have hST : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ T) := by
    intro g hg v hv
    refine ⟨hSK g hg v hv.1, ?_⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv.2
    obtain ⟨z, hz, hzeq⟩ := hTK g hg y hy
    exact Submodule.mem_map.2 ⟨z, hz, hzeq⟩
  rcases hirrS _ inf_le_left hST with h0 | hEq
  · exfalso
    have hmem : (w : H) ∈ S ⊓ T := ⟨hwS, Submodule.mem_map_of_mem hwM⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hw0 (Subtype.ext hmem)
  · rw [← hEq]; exact inf_le_right

end GlobalTheory.PsCo.TrAdm
