import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.NilpotentOfPowerTraces

open Matrix Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW.DerivativeRepresentation

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dS_eq_dRep (X : Matrix (Fin n) (Fin n) ℂ) (w : H) : ReciprocityTheory.ChartRestriction.DS.dS σ X w = dRep σ X w := by
  unfold ReciprocityTheory.ChartRestriction.DS.dS dRep
  simp only [Complex.coe_smul]

theorem bridge (hσ : IsURepOn (UJset ε) σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)} (hE : PositivityTheory.CW.KDer ε σ E)
    (v : kfin ε σ) (hv : (v : H) ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) (a b : Fin n) :
    ((E a b v : kfin ε σ) : H) = ((ReciprocityTheory.ChartRestriction.DS.smE ε σ a b ⟨v, hv⟩ : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) := by
  rw [ReciprocityTheory.ChartRestriction.DS.smE_apply hσ]
  set Z : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1
  have h1 := ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε Z
  have h2 := ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε Z
  have hd : E a b = ReciprocityTheory.ChartRestriction.DS.actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε Z) +
      Complex.I • ReciprocityTheory.ChartRestriction.DS.actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε Z) := by
    rw [← ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_smul, ← ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_add,
      ← ReciprocityTheory.ChartRestriction.DS.SmDerA.cpart_decomp, ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_single]
  rw [hd, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    hE _ h1 v, hE _ h2 v, dS_eq_dRep, dS_eq_dRep]

end PositivityTheory.CW.DerivativeRepresentation

namespace PositivityTheory.CW

open DerivativeRepresentation in
theorem c2a : CardSubmodulesOfIndexLePow := by
  intro n ε H _ _ _ σ hσ hirr E hE v
  have hsm := (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1
  obtain ⟨S0, hS0f, hvS0, hS0K⟩ := v.2
  have hS0k : ∀ x ∈ S0, IsKFin ε σ x := fun x hx => ⟨S0, hS0f, hx, hS0K⟩
  let S : Submodule ℂ (kfin ε σ) := S0.comap (kfin ε σ).subtype
  let f : S →ₗ[ℂ] S0 :=
    { toFun := fun x => ⟨((x : kfin ε σ) : H), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun x y h => by
    apply Subtype.ext; apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact h'
  refine ⟨S, Module.Finite.of_injective f hf, hvS0, fun a b hab w hw => ?_⟩
  show ((E a b w : kfin ε σ) : H) ∈ S0
  rw [bridge hσ hE w (hsm _ w.2)]
  exact CompanionTheory.D.gk.HC.smE_mem_of_compact_A hσ hS0K hab _ hw

end PositivityTheory.CW
