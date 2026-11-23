import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.PrimEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.FactEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.MinPol
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IntMod
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LeJoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.MuLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LyOver
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.DerZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LamDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KeepIrrOpenW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ArithmeticPointPurity

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.HV UpperTheory.V.W
open UpperTheory.V.Z.Desc.V0
theorem UpperTheory.V.Z.Desc.V0.unramified_at_of_dense_purity_num_e_power_series :
    UnrAlgE → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r)
    (ι : Qbar l ≃+* ℂ) (J : Ideal B.B) (m : ℕ), 1 ≤ n → Nonempty (Λ.Λ ≃ₐ[c.O] MvPowerSeries (Fin m) c.O) →
    B.Dense J → B.arithmeticPointPurityDense ι J → NumE B Λ J → UpperTheory.V.J.UnrAt B J := by
  intro hU l _ L Ω _ _ _ _ _ _ s V c n r B Λ ι J m hn hiso hD hE hN
  obtain ⟨M, _, _, _, h, e₀, hId, hmu⟩ := hN
  intro x w hJ hA hI δ hδ hJδ hψ
  obtain ⟨b₀, hb₀, hopen⟩ := _root_.UpperTheory.V.J.irrOpenW_alt l L Ω s V c n r B ι J hn hE x hI
  have hlam := UpperTheory.V.J.lamDer l L Ω s V c n r B Λ x m hiso δ hδ hψ
  have hdense : ∀ a : B.B, (∀ y ∈ {y : B.Pt | J ≤ RingHom.ker y ∧ y.Good w}, y a = 0) → a ∈ J :=
    fun a ha => hD w hA.1 a fun y hy hg => ha y ⟨hy, hg⟩
  have hex : ∃ y : B.Pt, (J ≤ RingHom.ker y ∧ y.Good w) ∧ y b₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hb₀ (hJ (hdense b₀ hcon))
  obtain ⟨y₀, hy₀, hyb₀⟩ := hex
  have hone := (hmu x y₀ w hJ hy₀.1 hA hy₀.2 hI (hopen y₀ w hy₀.1 hy₀.2 hyb₀)).1
  obtain ⟨e⟩ := hiso
  haveI : IsDomain (MvPowerSeries (Fin m) c.O) := GlobalTheory.CohenStructure.isDomain_mvPowerSeries c.O m
  haveI : IsDomain Λ.Λ := e.toRingEquiv.toMulEquiv.isDomain _
  haveI : IsIntegrallyClosed (MvPowerSeries (Fin m) c.O) := GlobalTheory.CohenStructure.isIntegrallyClosed_mvPowerSeries c.O m
  haveI : IsIntegrallyClosed Λ.Λ := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  haveI : IsNoetherianRing Λ.Λ := UpperTheory.V.Alg.IsCO.toIsNoetherian (O := c.O)
  haveI : CharZero Λ.Λ := by
    haveI : CharZero c.O :=
      (RingHom.charZero_iff (ϕ := (c.O.val : c.O →ₐ[ℤ_[l]] PadicAlgCl l).toRingHom) Subtype.val_injective).2 inferInstance
    have hC : Function.Injective (MvPowerSeries.C : c.O →+* MvPowerSeries (Fin m) c.O) := fun a b hab => by
      simpa using congrArg MvPowerSeries.constantCoeff hab
    exact (RingHom.charZero_iff (ϕ := (e.symm.toRingEquiv : MvPowerSeries (Fin m) c.O →+* Λ.Λ).comp MvPowerSeries.C)
      (e.symm.injective.comp hC)).1 inferInstance
  exact hU c.O Λ.Λ B.B _ (Λ.toPair B.u) J M h e₀ hId x {y : B.Pt | J ≤ RingHom.ker y ∧ y.Good w} b₀ hb₀ hdense hone
    (fun y hy hyb => (hmu x y w hJ hy.1 hA hy.2 hI (hopen y w hy.1 hy.2 hyb)).2)
    δ hδ hJδ hlam
end
