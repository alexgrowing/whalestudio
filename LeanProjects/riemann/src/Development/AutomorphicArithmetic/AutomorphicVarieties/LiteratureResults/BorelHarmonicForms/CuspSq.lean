import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpOfDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Assemble
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BrCusp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

open MeasureTheory GlobalTheory.UnitaryBC in
open scoped GlobalTheory.CuspRep.CuspidalL2GL in
private theorem isSqInt_of_cusp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {ψ : Sm E a}
    (hψ : IsCuspForm ψ) (hn : ∀ t g, ψ.1 (splitCentre E a t * g) = ψ.1 g) : IsSqInt ψ.1 := by
  classical
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (GA E a), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  have := (GlobalTheory.CovolGL.finvol E a μ).1
  have hc : Continuous ψ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E a ψ hψ.1.level
  obtain ⟨C, hC⟩ := UpperTheory.V.KernelIndexFullLattice.partC UpperTheory.V.KernelIndexFullLattice.splitEq_holds UpperTheory.V.KernelIndexFullLattice.brCusp_holds E a ψ hψ
    (fun t g => by rw [hn t g])
  exact (GlobalTheory.CuspRep.CuspidalL2GL.memL2_iff_isSqInt (μ := μ) hc hψ.1.left hn).1
    (GlobalTheory.CuspQuot.memL2_of_bound (μ := μ) hc (GlobalTheory.CuspRep.CuspidalL2GL.leftInv_latticeGL hψ.1.left hn) hC)

theorem UpperTheory.V.Lit.Bor.cuspSq :
    UpperTheory.V.Lit.Bor.CuspSq := by
  intro E _ _ _ a ha π r hr φ hφ
  obtain ⟨χ, ⟨s, hs⟩, hχ⟩ := UpperTheory.V.Lit.Bor.twEx E a ha r
  have key : ∀ ψ ∈ π.V, IsSqIntMod ψ := fun ψ hψ => by
    have h0 : lie E a (oneL E a) (mulChi a χ ψ) = (0 : ℂ) • mulChi a χ ψ := by
      rw [hχ, hr ψ hψ, (UpperTheory.V.Lit.Bor.ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, zero_smul,
        map_zero]
    have h1 := isSqInt_of_cusp ((π.cusp ψ hψ).mulChi χ) fun t g => by
      rw [UpperTheory.V.Lit.Bor.aInv E a _ 0 h0 t g, zero_mul, Complex.exp_zero, one_mul]
    refine ⟨s, χ, hs, ?_⟩
    have e : (fun g => ((chiDet a χ g : ℂˣ) : ℂ) * ψ.1 g) = (mulChi a χ ψ).1 := funext fun g => by
      rw [mulChi_apply, mul_comm]
    rw [e]
    exact h1
  refine ⟨(π.cusp φ hφ).1.left, (π.cusp φ hφ).1.level, hr φ hφ, fun l => key _ ?_⟩
  induction l with
  | nil => exact hφ
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons]
    exact π.stable (.lie X) _ ih
