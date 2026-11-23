import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFiniteAdelesGLStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrongApproximationUpperUnitriangularFiniteAdeleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactIntegralGLFiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabilizerConjFiniteAdeleGLIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteMeasureReductionDomainInfinityStatement

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CovolGL

theorem lcsc_GL (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [LocallyCompactSpace R] [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace, Units.isEmbedding_embedProduct.secondCountableTopology⟩

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem pFin_ratGL (γ : GL (Fin a) E) :
    GeneralLinearGroup.map (pFin E) (ratGL E a γ) = PIW.ClassFinD.glIncl E a γ := by
  ext i j
  rfl

variable [IsTotallyComplex E]

theorem pFin_splitCentre (t : ℝ) : GeneralLinearGroup.map (pFin E) (splitCentre E a t) = 1 :=
  pFin_infGL _

variable (E a) in

theorem isFiniteMeasure_quotMeasure (μ : Measure (GA E a)) [μ.IsHaarMeasure] :
    IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) := by
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin a) (Af E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Af E)) := ⟨rfl⟩
  obtain ⟨_, _⟩ := lcsc_GL (Cinf E) a
  obtain ⟨_, _⟩ := lcsc_GL (Af E) a
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_adelicGL_homeomorph_infinite_finite E a
  obtain ⟨S, hS⟩ := PIW.ClassFinD.borelKGL_of GlobalTheory.T.iwasawaDecomposition_finiteAdeles_GL GlobalTheory.T.strongApproximation_upperUnitriangular_finiteAdeles PIW.ClassFinD.idele_class_finite E a
  choose Λ hΛ hΛK using fun s => GlobalTheory.T.exists_lattice_stabilizer_conj_finiteAdeleGL_integral E a s
  choose Ω hΩ hcov using fun s => GlobalTheory.T.exists_finite_measure_reduction_domain_infinity E a (Λ s) (hΛ s) (Measure.haar : Measure (GL (Fin a) (Cinf E)))
  refine ⟨?_⟩
  rw [quotMeasure_univ (isFundamentalDomain_stdDom (latticeGL E a) μ)]
  refine GlobalTheory.Mem.VolFin.measure_lt_top_of_cover e (latticeGL E a) μ S (PIW.ClassFinD.KGL E a) (GlobalTheory.T.isCompact_integralGL_finiteAdeles E a) Ω hΩ
    (fun g => ?_) _ (isFundamentalDomain_stdDom _ μ)
  obtain ⟨γ, s, hs, k, hk, hx⟩ := hS (GeneralLinearGroup.map (pFin E) g)
  obtain ⟨η, hη, n, hn⟩ := hcov s (GeneralLinearGroup.map (pInf E) (ratGL E a γ⁻¹ * g))
  have hmem : ratGL E a η * splitCentre E a 1 ^ n * ratGL E a γ⁻¹ ∈ latticeGL E a :=
    mul_mem (mul_mem (ratGL_mem_latticeGL η) (zpow_mem_latticeGL n)) (ratGL_mem_latticeGL _)
  have hg : ratGL E a η * splitCentre E a 1 ^ n * ratGL E a γ⁻¹ * g =
      (ratGL E a η * splitCentre E a 1 ^ n) * (ratGL E a γ⁻¹ * g) := by simp only [mul_assoc]
  refine ⟨⟨_, hmem⟩, s, hs, ?_, ?_⟩
  · rw [Subgroup.smul_def, smul_eq_mul, he, hg, map_mul]
    exact hn
  · rw [Subgroup.smul_def, smul_eq_mul, he]
    simp only [map_mul, map_zpow, pFin_ratGL, pFin_splitCentre, _root_.one_zpow, mul_one, hx, map_inv]
    refine ⟨s⁻¹ * PIW.ClassFinD.glIncl E a η * s * k, (PIW.ClassFinD.KGL E a).mul_mem (hΛK s η hη) hk, ?_⟩
    simp only [smul_eq_mul]
    group

variable (E a) in

theorem isMulRightInvariant (μ : Measure (GA E a)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  have hd := isFundamentalDomain_stdDom (latticeGL E a) μ
  have hfin := isFiniteMeasure_quotMeasure E a μ
  have h1 : μ (stdDom (latticeGL E a)) ≠ ⊤ := by
    rw [← quotMeasure_univ hd]; exact measure_ne_top _ _
  exact GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain _ μ hd (hd.measure_ne_zero (NeZero.ne μ)) h1

theorem finvol : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure], IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) ∧ μ.IsMulRightInvariant :=
  fun E _ _ _ a μ _ => ⟨isFiniteMeasure_quotMeasure E a μ, isMulRightInvariant E a μ⟩

end GlobalTheory.CovolGL
