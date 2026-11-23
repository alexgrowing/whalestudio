import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleRationalClassKernelIntegralsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgreeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRegularSemisimpleOfTestFunctionNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHasSumEqIntegralIndicatorHasSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumConjClassesRegroupWithInvariantSelectionStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section
namespace GlobalTheory.CompanionTheory.EllTrace
open GlobalTheory.TruncKer

theorem countable_GF {D : D7} (V : HSp D) : Countable (GF V) := by
  haveI : Countable D.host.E :=
    (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
    (show Countable (Fin V.rank → Fin V.rank → D.host.E) from inferInstance)
  haveI : Countable (GL (Fin V.rank) D.host.E) := Units.val_injective.countable
  infer_instance

theorem kernel_diag_hasSum {D : D7} (V : HSp D) {f : GA D V → ℂ} (hf : f ∈ CcGA V) (x : GA D V) :
    (Function.support fun δ : GF V => f (x⁻¹ * rat V δ * x)).Finite ∧
    HasSum (fun δ : GF V => f (x⁻¹ * rat V δ * x)) (GlobalTheory.AutomorphicL2Unitary.kernel (GQ V) f x x) := by
  have hcs := continuous_of_mem_ccAd hf
  have hr : (ratEmb D.sp.cm.sig V.gram).range = GQ V := by rw [range_ratEmb]; rfl
  let e : GF V ≃* GQ V :=
    (MonoidHom.ofInjective (ratEmb_injective D.sp.cm.sig V.gram)).trans (MulEquiv.subgroupCongr hr)
  have he : ∀ δ : GF V, ((e δ : GQ V) : GA D V) = rat V δ := fun δ => rfl
  refine ⟨?_, ?_⟩
  · have hC : IsCompact ((fun g : GA D V => x * g * x⁻¹) '' tsupport f) :=
      hcs.2.isCompact.image (by fun_prop)
    have hfin := finite_mem_compact (Γ := GQ V) hC
    refine (hfin.preimage e.injective.injOn).subset fun δ hδ => ?_
    refine ⟨x⁻¹ * rat V δ * x, subset_tsupport _ hδ, ?_⟩
    simp only [he]
    group
  · have := hasSum_kernel (Γ := GQ V) hcs.2 x x
    exact (e.toEquiv.hasSum_iff (f := fun γ : GQ V => f (x⁻¹ * (γ : GA D V) * x))).2 this

theorem charpoly_eq_of_isConj {D : D7} {V : HSp D} {a b : GF V} (h : IsConj a b) :
    a.1.1.charpoly = b.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  change a.1.1.charpoly = ((c.1 : GL _ _) * a.1 * (c.1)⁻¹ : GL _ _).1.charpoly
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem ellTrace_of_middle : MainStatements.RegularCuspidalTrace.RegClassInt → MainStatements.RegularCuspidalTrace.RegClassFin → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.NonFieldTypeVanishing → HyperZero → EllTrace := by
  intro hInt hFinC hCO hPC hIw _hRS hNF hHZ D V lam S M T U μa μf μ _ _ fa ff hT
  have hT' := hT
  obtain ⟨hodd, -, -, hnf, hμ, harch, hfin⟩ := hT'
  have hμ' := hμ
  obtain ⟨hμa, hμf, -, -⟩ := hμ'
  set f := tensor D.sp.cm.sig V.gram fa ff with hfdef
  have hcc : f ∈ CcGA V := tensor_mem_ccAd harch.mem hfin.isFinFamily
  have hcs := continuous_of_mem_ccAd hcc
  obtain ⟨hH, -⟩ := GlobalTheory.T.typeHypothesis_forms_agree D V T hnf
  haveI := hμa
  haveI := hμf
  have hconst := hPC.2 D V hodd S M T hH U μa μf f ⟨fa, ff, harch, hfin, rfl⟩
  have hcusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ f :=
    hCO D V μ f hcc (fun 𝔉 h𝔉 ν hν x y => ((hconst 𝔉 h𝔉).1 ν x y).2)
      (fun 𝔉 h𝔉 ν hν x y => ((hconst 𝔉 h𝔉).2 ν x y).2)
  have hcuspFn : MainStatements.RegularCuspidalTrace.IsCuspFn f := fun 𝔉 h => (hconst 𝔉 h).1
  refine ⟨hcusp.traceClass, ?_⟩
  rw [hcusp.trace_eq_integral]
  haveI : Countable (GF V) := countable_GF V
  let ι := {𝔬 : Set (GF V) // ∃ γ : GF V, IsRegSS γ.1.1 ∧ 𝔬 = {δ | IsConj γ δ}}
  haveI : Countable ι := by
    have hs : Function.Surjective
        (fun γ : {γ : GF V // IsRegSS γ.1.1} => (⟨{δ | IsConj γ.1 δ}, γ.1, γ.2, rfl⟩ : ι)) := by
      rintro ⟨_, γ, hγ, rfl⟩
      exact ⟨⟨γ, hγ⟩, rfl⟩
    exact hs.countable
  let k : ι → GlobalTheory.AutomorphicL2Unitary.Quot (GQ V) → ℂ := fun i =>
    GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun x => ∑' δ : i.1, f (x⁻¹ * rat V δ * x))
  have hkint : ∀ i : ι, Integrable (k i) (autMeasure V μ) := by
    rintro ⟨_, γ, hγ, rfl⟩
    obtain ⟨hcl, -⟩ := (GlobalTheory.T.regularSemisimple_rational_class_kernel_integrals D V γ hγ).2 f
    have := hInt D V μ f hcc hcuspFn γ hγ
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f = fun x => ∑' δ : {δ | IsConj γ δ}, f (x⁻¹ * rat V δ * x)
      from funext hcl] at this
    exact this
  have hreg : ∀ (δ : GF V) (x : GA D V), f (x⁻¹ * rat V δ * x) ≠ 0 → IsRegSS δ.1.1 :=
    fun δ x h => GlobalTheory.T.isRegularSemisimple_of_testFunction_ne_zero hIw D V T U μf ff hfin fa δ x h
  have hPc : ∀ a b : GF V, IsConj a b → Irreducible a.1.1.charpoly → Irreducible b.1.1.charpoly :=
    fun a b h ha => charpoly_eq_of_isConj h ▸ ha
  refine GlobalTheory.T.integral_hasSum_eq_integral_indicator_hasSum' (autMeasure V μ) k hkint ?_
    {i : ι | ∀ δ ∈ i.1, Irreducible δ.1.1.charpoly} _ _ (fun q => ?_) (fun q => ?_) ?_
  · refine ((hFinC D V f hcc).preimage Subtype.val_injective.injOn).subset fun i hi => ⟨i.2, ?_⟩
    by_contra hno
    apply hi
    have hz : ∀ q, k i q = 0 := by
      intro q
      change (∑' δ : i.1, f (q.out⁻¹ * rat V δ * q.out)) = 0
      have : ∀ δ : i.1, f (q.out⁻¹ * rat V δ * q.out) = 0 := fun δ => by
        by_contra h
        exact hno ⟨q.out, δ.1, δ.2, h⟩
      simp [this]
    simp [hz]
  · obtain ⟨hsupp, hsum⟩ := kernel_diag_hasSum V hcc q.out
    have := (GlobalTheory.T.hasSum_conjClasses_regroup_with_invariant_selection _ hsupp (fun δ => IsRegSS δ.1.1) (fun δ => Irreducible δ.1.1.charpoly)
      (fun δ h => hreg δ _ h) hPc).1
    rw [hsum.tsum_eq] at this
    exact this
  · obtain ⟨hsupp, -⟩ := kernel_diag_hasSum V hcc q.out
    have := (GlobalTheory.T.hasSum_conjClasses_regroup_with_invariant_selection _ hsupp (fun δ => IsRegSS δ.1.1) (fun δ => Irreducible δ.1.1.charpoly)
      (fun δ h => hreg δ _ h) hPc).2
    have hfs : (Function.support fun δ : {δ : GF V // Irreducible δ.1.1.charpoly} =>
        f (q.out⁻¹ * rat V δ.1 * q.out)).Finite :=
      (hsupp.preimage Subtype.val_injective.injOn).subset fun δ hδ => hδ
    have e : GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (ellKernel V f) q =
        ∑' δ : {δ : GF V // Irreducible δ.1.1.charpoly}, f (q.out⁻¹ * rat V δ.1 * q.out) := by
      change ellKernel V f q.out = _
      rw [ellKernel, tsum_eq_finsum hfs]
    rw [e]
    exact this
  · rintro ⟨_, γ, hγ, rfl⟩ hi
    have hirr : ¬ Irreducible γ.1.1.charpoly := fun h =>
      hi fun δ hδ => hPc γ δ hδ h
    have hZ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ZeroClause μ f (ratEmb D.sp.cm.sig V.gram γ) := by
      by_cases hA : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1
      · exact hNF.zero hodd hH hμ ⟨fa, ff, harch, hfin, rfl⟩ hA
      · exact hHZ D V lam S M T U μa μf μ fa ff hT γ hγ hirr hA
    obtain ⟨hcl, hiff⟩ := (GlobalTheory.T.regularSemisimple_rational_class_kernel_integrals D V γ hγ).2 f
    have := ((hiff hcs.1 hcs.2 μ 0).1 hZ).2
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f = fun x => ∑' δ : {δ | IsConj γ δ}, f (x⁻¹ * rat V δ * x)
      from funext hcl] at this
    exact this

end GlobalTheory.CompanionTheory.EllTrace
