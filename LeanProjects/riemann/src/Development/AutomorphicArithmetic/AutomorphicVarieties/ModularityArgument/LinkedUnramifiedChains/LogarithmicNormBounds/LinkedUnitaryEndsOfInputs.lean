import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.OpenEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.XiAdic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.NotIrrOfLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.XiArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IrrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LamDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.UnrAlgE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.UnrAlgW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.MuRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.CoefInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.LinkedUnlEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.ChiUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinPtDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AbsMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.OffSelf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.CRealAv

noncomputable section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.J
open private UpperTheory.V.J.oe_big UpperTheory.V.J.oe_res UpperTheory.V.J.oe_modIn from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.OpenEx

namespace UpperTheory.Gal.projectedFormsSystemPart

def OpenEx2E : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M → Even N →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → Φ.Big C₀ → SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    ∀ (A : Subalgebra c.O (PadicAlgCl l)) [Module.Finite c.O A],
    ∃ (c₁ : Coef l) (_ : Fr.IsCoef l c₁.O) (f : ResidueField c.O →+* ResidueField c₁.O) (R : CReal k c₁ f 3 (cycBar L Ω l)⁻¹)
      (Λ : LamObj R.r) (J : Ideal R.B₀.B) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) (m : ℕ),
      (∀ x ∈ A, x ∈ c₁.O) ∧ Large L c₁ ∧ IsKa σ M ι 3 (cycBar L Ω l)⁻¹ ∧ R.B₀.Modular ι J Λ ∧ Num R.B₀ Λ J ∧
      Nonempty (Λ.Λ ≃ₐ[c₁.O] MvPowerSeries (Fin m) c₁.O) ∧ R.T.IsPhi φ ∧ Function.Surjective φ ∧ AllGood R.S (J.map φ) ∧
      R.T.DimT J ∧ EndPt R ι φ

theorem linked_unitary_ends_of_inputs (hO : OpenEx2E) (hX : XiEx) (hT : XiTI) (hA : XiArith) (hTan : TanA) (hR : Red2) (hU : Unr) (hE : End)
    (hι : ∀ (l : ℕ) [Fact l.Prime], Nonempty (Qbar l ≃+* ℂ)) : UpperTheory.V.Z.J.LinkedUnlE := by
  intro Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M H hev L _ _ _ _ _ Φ C₀ k hok hbig hseed A _ _ _ ρ hρ hψ r hr hirr v hpc i j
  by_contra hno
  push Not at hno
  obtain ⟨ι⟩ := hι l
  obtain ⟨c₁, _, f, R, Λ, J, φ, m, hAc, hL, hka, hmod, hnum, hΛ, hφ, hsurj, hgood, hdim, hend⟩ :=
    hO Ω l ι c N e ψ η σ g₁ B M H hev L Φ C₀ k hok hbig hseed A
  obtain ⟨ξ, h1, h2⟩ := hX Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R A hAc ρ hρ
  have hr' : ∀ s, (r s).val = (R.S.ρ.r (k.p0 s)).map fun a => (ξ a).1 := fun s => by
    rw [hr s]; ext a b; exact (h1 _ a b).symm
  have hi : IsIrr r := by
    have := hirr ⊤ (by simp)
    exact ⟨this.1, fun s w hw => Submodule.mem_top, fun U hU h => this.2.2 U hU fun s w hw => h s.1 w hw⟩
  have hψ' : ∀ v i, ∀ g ∈ Φ.Iv v, (ξ (R.S.ρ.ψ v i g).val).1 =
      (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val.1 := fun v i g hg =>
    (h2 v i g).trans (by rw [hψ v i g hg]; rfl)
  obtain ⟨t1, t2, t3⟩ := hT Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R ξ r hr' hi
  obtain ⟨⟨w, hw⟩, hip⟩ := hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R hka φ hφ ξ r hr' hi hψ'
  obtain ⟨D, hD, D', hD', k1, k2, hli⟩ := hTan Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R ξ r hr' hi hψ' v hpc i j
    fun g => (h2 v i g).trans ((hno g).trans (congrArg (· * _) (h2 v j g).symm))
  exact hE Ω l c η _ σ g₁ B M L Φ k c₁ f _ R φ hφ hsurj J ξ w
    (hU l L Ω R.s R.V c₁ 3 R.r R.B₀ Λ ι J m (by norm_num) hΛ hmod.dense hmod.end1 hnum) t1 hw hip
    (hR Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f _ R hL hka φ hφ hsurj J hgood hdim hmod.dense hend (ptA R ξ) t2 t3)
    D hD D' hD' k1 k2 hli

end UpperTheory.Gal.projectedFormsSystemPart
