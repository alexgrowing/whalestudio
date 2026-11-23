import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncatedKernelOrbitSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgreeStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.KTClass

theorem tsum_conj_eq_classKernel {D : D7} {V : HSp D} (γ : GF V) (f : GA D V → ℂ) (x : GA D V) :
    ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x) =
      GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f x := by
  have hGQ : ∀ g, g ∈ GQ V ↔ ∃ c, rat V c = g := fun g => by
    rw [show GQ V = (rat V).range from (range_ratEmb ..).symm]; rfl
  have himg : (rat V) '' {δ | IsConj γ δ} = GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) (rat V γ) := by
    ext y; constructor
    · rintro ⟨δ, hδ, rfl⟩
      obtain ⟨c, rfl⟩ := isConj_iff.1 hδ
      exact ⟨rat V c⁻¹, (hGQ _).2 ⟨c⁻¹, rfl⟩, by simp [map_mul, map_inv, mul_assoc]⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := (hGQ g).1 hg
      exact ⟨c⁻¹ * γ * c, isConj_iff.2 ⟨c⁻¹, by group⟩, by simp [map_mul, map_inv]⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel, ← himg,
    tsum_image (fun y => f (x⁻¹ * y * x)) (ratEmb_injective _ _).injOn]

theorem kT_eq_classKernel : ∀ {D : D7} {V : HSp D}, GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ {lam : D.what₂.Tau → Fin V.rank → ℤ} {S : D.what₂.Tau → SPar} {M : DSModel V S} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)} {μ : Measure (GA D V)} {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}, IsTestData V lam M T U μa μf μ fa ff → ∀ (Φ : WittFrame V) (K : Subgroup (GA D V)) (γ : GF V) (Tr : A0 (wittIndex V)) (x : GA D V), kT Φ K {δ | IsConj γ δ} (tensor D.sp.cm.sig V.gram fa ff) Tr x = classKernel (GQ V) (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x := by
  intro D V hPC lam S M T U μa μf μ fa ff hTD Φ K γ Tr x
  obtain ⟨hodd, -, -, hnf, hμ, ha, hb⟩ := hTD
  have hH := (GlobalTheory.T.typeHypothesis_forms_agree D V T hnf).1
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.haar_arch
  haveI : ∀ v, (μf v).IsHaarMeasure := hμ.haar_loc
  have hU : ∀ 𝔉 : IsoFlag V, 𝔉.Proper →
      GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish 𝔉 (tensor D.sp.cm.sig V.gram fa ff) := fun 𝔉 h𝔉 =>
    (hPC.2 D V hodd S M T hH U μa μf _ ⟨fa, ff, ha, hb, rfl⟩ 𝔉 h𝔉).1
  have hcl : ∀ δ ∈ {δ : GF V | IsConj γ δ}, ∀ g, g * δ * g⁻¹ ∈ {δ : GF V | IsConj γ δ} :=
    fun δ hδ g => (show IsConj γ δ from hδ).trans (isConj_iff.2 ⟨g, rfl⟩)
  rw [GlobalTheory.T.truncated_kernel_orbit_sum D V Φ K _ hU _ hcl Tr x]
  exact tsum_conj_eq_classKernel γ _ x

end GlobalTheory.KTClass
