import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW.KFiniteInclusion

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def incl (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) :
    kfin ε σ →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ where
  toFun v := ⟨v, hK v v.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem incl_val (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) (v : kfin ε σ) :
    ((incl hK v : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) = v := rfl

theorem incl_inj (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) {v w : kfin ε σ}
    (h : incl hK v = incl hK w) : v = w := by
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

def Eop (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (h2 : ∀ a b, ∀ v ∈ CompanionTheory.D.gk.HC.KF ε σ, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ CompanionTheory.D.gk.HC.KF ε σ)
    (a b : Fin n) : Module.End ℂ (kfin ε σ) where
  toFun v := ⟨(ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (incl hK v) : H), h2 a b (incl hK v) v.2⟩
  map_add' x y := Subtype.ext (by simp only [map_add, Submodule.coe_add])
  map_smul' c x := Subtype.ext (by simp only [map_smul, Submodule.coe_smul, RingHom.id_apply])

variable (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (h2 : ∀ a b, ∀ v ∈ CompanionTheory.D.gk.HC.KF ε σ, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ CompanionTheory.D.gk.HC.KF ε σ)

theorem incl_E (a b : Fin n) (v : kfin ε σ) :
    incl hK (Eop hK h2 a b v) = ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (incl hK v) := Subtype.ext rfl

theorem incl_actM (X : Mx n) (v : kfin ε σ) :
    incl hK (ReciprocityTheory.ChartRestriction.DS.actM (Eop hK h2) X v) = ReciprocityTheory.ChartRestriction.DS.actM (ReciprocityTheory.ChartRestriction.DS.smE ε σ) X (incl hK v) := by
  simp only [ReciprocityTheory.ChartRestriction.DS.actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, incl_E]

end PositivityTheory.CW.KFiniteInclusion

namespace PositivityTheory.CW

open KFiniteInclusion

theorem c1 : C1 := by
  intro n ε H _ _ _ σ hσ hirr
  obtain ⟨hK, h2⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have hun := ReciprocityTheory.ChartRestriction.DS.isInfUnitary_of_isDerivedOn hσ hD
  refine ⟨Eop hK h2, ?_, ?_, ?_, ?_⟩
  · intro X hX v
    have h := ReciprocityTheory.ChartRestriction.DS.dS_eq_actM hD (X := X) hX (incl hK v)
    have e1 : ((ReciprocityTheory.ChartRestriction.DS.actM (Eop hK h2) X v : kfin ε σ) : H) =
        ((ReciprocityTheory.ChartRestriction.DS.actM (ReciprocityTheory.ChartRestriction.DS.smE ε σ) X (incl hK v) : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) := by
      rw [← incl_actM hK h2 X v]
      rfl
    rw [e1, ← h]
    simp only [ReciprocityTheory.ChartRestriction.DS.dS, dRep, Complex.coe_smul, incl_val]
  · intro a b c d
    refine LinearMap.ext fun v => incl_inj hK ?_
    have h := LinearMap.congr_fun (hD.glRep a b c d) (incl hK v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, incl_E] at h ⊢
    rw [h]
    split_ifs <;> simp [incl_E]
  · intro a b x y
    have h := hun a b (incl hK x) (incl hK y)
    rw [Submodule.coe_inner, Submodule.coe_inner] at h
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact h
  · intro N hN
    set M := N.map (incl hK) with hM
    have hMK : (M : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) ⊆ CompanionTheory.D.gk.HC.KF ε σ := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hMst : ∀ a b, ∀ v ∈ M, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ M := by
      rintro a b _ ⟨w, hw, rfl⟩
      exact ⟨Eop hK h2 a b w, hN a b w hw, incl_E hK h2 a b w⟩
    rcases CompanionTheory.D.gk.HC.uIrr n ε H σ hσ hirr M hMK hMst with h | h
    · left
      refine eq_bot_iff.2 fun x hx => ?_
      have : incl hK x ∈ M := ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact incl_inj hK (this.trans (map_zero _).symm)
    · right
      refine eq_top_iff.2 fun x _ => ?_
      have : incl hK x ∈ (M : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) := by rw [h]; exact x.2
      obtain ⟨w, hw, e⟩ := this
      rwa [← incl_inj hK e]

end PositivityTheory.CW
