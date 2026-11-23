import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM IsKHWVec smD smE dS smE_apply)

namespace PositivityTheory.CW

namespace MatrixActionAdditive

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem actM_single {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b 1) = E a b := by
  simp [actM, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem actM_add' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

theorem actM_smul' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (c : ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  simp [actM, Finset.smul_sum, smul_smul]

theorem dS_eq_dRep (σ : Mx n → (H →L[ℂ] H)) (X : Mx n) (v : H) : dS σ X v = dRep σ X v := by
  have h : ∀ t : ℝ, ((t : ℂ) • X) = t • X := fun t => by
    ext i j
    simp
  simp only [dS, dRep, h]

theorem key {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (E : Fin n → Fin n → Module.End ℂ (kfin ε σ)) (hE : KDer ε σ E) (v : kfin ε σ) (hv : (v : H) ∈ smD ε σ)
    (a b : Fin n) : ((smE ε σ a b ⟨v, hv⟩ : smD ε σ) : H) = ((E a b v : kfin ε σ) : H) := by
  rw [smE_apply hσ ⟨v, hv⟩ a b]
  have hX := ReciprocityTheory.ChartRestriction.DS.S7.ccb_cpart_sum ε (single a b 1)
  have h1 : E a b = actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (single a b 1))
      + Complex.I • actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (single a b 1)) := by
    rw [← actM_single E a b, ← actM_smul', ← actM_add', hX]
  rw [h1]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul]
  rw [hE _ (ReciprocityTheory.ChartRestriction.DS.S7.ccb_inG_cpart1 ε _) v, hE _ (ReciprocityTheory.ChartRestriction.DS.S7.ccb_inG_cpart2 ε _) v,
    dS_eq_dRep, dS_eq_dRep]

end MatrixActionAdditive

open MatrixActionAdditive in
theorem c3a : HighestWeightSpaceFinite := by
  intro n ε H _ _ _ σ hσ hIrr E hE μ
  have hA := CompanionTheory.D.gk.HC.uAdm n ε H σ hσ hIrr μ
  have hsub : (kfin ε σ).subtype '' {v : kfin ε σ | IsKHWVec ε E μ v}
      ⊆ (smD ε σ).subtype '' {v : smD ε σ | v ∈ CompanionTheory.D.gk.HC.KF ε σ ∧ IsKHWVec ε (smE ε σ) μ v} := by
    rintro _ ⟨v, hvB, rfl⟩
    have hv : (v : H) ∈ smD ε σ := CompanionTheory.D.gk.HC.mem_smD_of_isKFin hσ hIrr v.2
    refine ⟨⟨v, hv⟩, ⟨v.2, ?_, ?_⟩, rfl⟩
    · intro a
      apply Subtype.ext
      rw [key hσ E hE v hv a a, hvB.1 a]
      rfl
    · intro a b hab he
      apply Subtype.ext
      rw [key hσ E hE v hv a b, hvB.2 a b hab he]
      rfl
  have hle : (Submodule.span ℂ {v : kfin ε σ | IsKHWVec ε E μ v}).map (kfin ε σ).subtype
      ≤ (Submodule.span ℂ {v : smD ε σ | v ∈ CompanionTheory.D.gk.HC.KF ε σ ∧ IsKHWVec ε (smE ε σ) μ v}).map
        (smD ε σ).subtype := by
    rw [Submodule.map_span, Submodule.map_span]
    exact Submodule.span_mono hsub
  haveI : FiniteDimensional ℂ ((Submodule.span ℂ {v : kfin ε σ | IsKHWVec ε E μ v}).map (kfin ε σ).subtype) :=
    Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (kfin ε σ).injective_subtype _).symm

end PositivityTheory.CW

end
