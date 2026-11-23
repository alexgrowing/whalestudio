import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.IsIrreducibleOfIsIrrRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace UpperTheory.One.M

open GlobalTheory GlobalTheory.SerSys GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem mapsToProd_tw {g : ℕ} [Fact g.Prime] {n a b : ℕ} {V W W' W'' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup W''] [Module ℂ W'']
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) V} {σ : Representation ℂ (GL (Fin a) ℚ_[g]) W}
    {ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'} {ρ' : Representation ℂ (GL (Fin b) ℚ_[g]) W''} (μ : ℚ_[g]ˣ →* ℂˣ)
    (hμ : Supp.IsUnram μ) (e : W' ≃ₗ[ℂ] W'')
    (he : ∀ y v, ρ' y (e v) = ((μ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • e (ρ y v)) (h : Supp.MapsToProd π σ ρ) :
    Supp.MapsToProd π σ ρ' := by
  obtain ⟨hn, ν₁, ν₂, Λ, h₁, h₂, h0, H⟩ := h
  refine ⟨hn, ν₁, ν₂ * μ⁻¹, (TensorProduct.congr (LinearEquiv.refl ℂ W) e).toLinearMap ∘ₗ Λ, h₁, fun u => ?_, fun h => h0 (LinearMap.ext fun v => ?_),
    fun p x y hp hx hy v => ?_⟩
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h₂ u, hμ u, inv_one, mul_one]
  · exact (TensorProduct.congr (LinearEquiv.refl ℂ W) e).map_eq_zero_iff.1 (LinearMap.congr_fun h v)
  · have key : ∀ z, TensorProduct.map (σ x) (ρ' y) (TensorProduct.congr (LinearEquiv.refl ℂ W) e z) =
        ((μ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
          TensorProduct.congr (LinearEquiv.refl ℂ W) e (TensorProduct.map (σ x) (ρ y) z) := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s t => simp [he, TensorProduct.tmul_smul]
      | add s t hs ht => simp only [map_add, hs, ht, smul_add]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [H p x y hp hx hy v, key, map_smul, smul_smul]
    congr 1
    simp [mul_assoc]

theorem inInd_reps {g : ℕ} [Fact g.Prime] {π : Supp.GLRep g} {L : List (Supp.GLRep g)} (h : Supp.InInd π L) :
    ∀ y : List (IrrGL ℚ_[g]), List.Forall₂ (fun (ρ : Supp.GLRep g) (x : IrrGL ℚ_[g]) =>
      ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (IrrGL.of ρ.2.ρ hs hi).Inert x) L y →
      Supp.InInd π (y.map fun x => ⟨x.1, Rep.of x.rep⟩) := by
  induction h with
  | nil π h0 hi =>
    intro y hy
    cases hy
    exact .nil π h0 hi
  | cons π σ ρ S hπ hρ _ hM ih =>
    intro y hy
    cases hy with
    | cons h1 h2 =>
      obtain ⟨hs, hi, μ, hμ, rfl⟩ := h1
      let φ := (GlobalTheory.TypeRec.TwistInert.twistEquiv (IrrGL.equivOf ρ.2.ρ hs hi) (detChar (Fin ρ.1) μ)).trans
        (IrrGL.twEquiv (IrrGL.of ρ.2.ρ hs hi) μ (isSmoothChar_of_isUnram hμ))
      refine .cons π σ _ _ hπ (Ysupp.IrreducibleSupport.isIrrRep_of_isIrreducible (IrrRep.irr _)) (ih _ h2)
        (mapsToProd_tw μ (fun u => hμ _ ?_) φ.toLinearEquiv (fun y v => ?_) hM)
      · have hn : ‖((u : ℤ_[g]) : ℚ_[g])‖ = 1 := PadicInt.norm_units u
        have a1 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g ((u : ℤ_[g]) : ℚ_[g]) 1
        have a2 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 ((u : ℤ_[g]) : ℚ_[g])
        rw [hn, map_one, norm_one] at a1 a2
        exact le_antisymm (not_lt.1 fun h => lt_irrefl _ (a2.1 h)) (not_lt.1 fun h => lt_irrefl _ (a1.1 h))
      · rw [← map_smul]
        exact (LinearMap.congr_fun (φ.isIntertwining' y) v).symm

end UpperTheory.One.M
