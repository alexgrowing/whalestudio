import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ContScal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantFunctions

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem cont_smul (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (Γ : Type) [Group Γ]
    [TopologicalSpace Γ] (χ : Γ →* ℤ_[l]ˣ) (hχ : Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l])) (m : QO l O) :
    Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m := by
  refine (QO.isBaseChange l O).inductionOn m
    (motive := fun m => Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m) ?_ ?_ ?_ ?_
  · simpa using continuous_const
  · intro x
    have h1 : Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • x :=
      Continuous.comp (LDataCardLeFinrank.contScal l Γ χ hχ) (Continuous.prodMk_left x)
    have h2 : Continuous (QO.incl l O) := continuous_of_discreteTopology
    refine (h2.comp h1).congr fun g => ?_
    exact map_smul (QO.incl l O) _ x
  · intro s x hx
    have h2 : Continuous fun y : QO l O => s • y := continuous_of_discreteTopology
    exact (h2.comp hx).congr fun g => smul_comm _ _ _
  · intro x y hx hy
    exact (hx.add hy).congr fun g => (smul_add _ _ _).symm

private theorem locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantFunctions.locConst ψ h

theorem UpperTheory.V.Base.contTw :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime],
      Continuous (cycZ k Ω l) ∧ (∀ e : ℤ, ContAction (LDataCardLeFinrank.qzG k Ω l e)) ∧
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ψ : G k Ω →* Oˣ) (n : ℤ), IsOpen (ψ.ker : Set (G k Ω)) →
        ContAction (twist₂ l (ψ * chiO k Ω l O ^ n)) := by
  intro k Ω _ _ _ _ _ l _
  have hc := continuous_cycZ k Ω l
  refine ⟨hc, fun e => LDataCardLeFinrank.contScal l _ _ (Units.continuous_val.comp (hc.zpow (-e))), fun O _ _ ψ n hψ => ?_⟩
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  have h1 := cont_smul l O _ (cycZ k Ω l ^ n) (Units.continuous_val.comp (hc.zpow n)) m
  have h2 := ((locConst ψ hψ).prodMk ((IsLocallyConstant.iff_continuous _).2 h1)).comp
    fun p : Oˣ × QO l O => (p.1 : O) • p.2
  refine h2.continuous.congr fun g => ?_
  show (ψ g : O) • (((cycZ k Ω l g ^ n : ℤ_[l]ˣ) : ℤ_[l]) • m) = ((ψ g * chiO k Ω l O g ^ n : Oˣ) : O) • m
  have e : chiO k Ω l O g ^ n = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l g ^ n) :=
    (map_zpow (Units.map (algebraMap ℤ_[l] O).toMonoidHom) (cycZ k Ω l g) n).symm
  rw [Units.val_mul, mul_smul, e]
  exact congrArg _ (algebraMap_smul O _ m).symm
