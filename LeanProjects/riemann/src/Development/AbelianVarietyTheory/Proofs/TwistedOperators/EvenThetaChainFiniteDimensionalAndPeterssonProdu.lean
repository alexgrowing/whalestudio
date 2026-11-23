import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenMetric

variable {D : D7}

theorem finDim : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, FinDim D := by
  intro hP D c hc j _ s hs
  obtain ⟨U, hU, hUJ⟩ := hs.isOpen
  have : FiniteDimensional ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) 1) :=
    GlobalTheory.MultFinite.hcFinite hP hc.inf ⟨U, hU, fun k hk hf => ⟨hUJ k hk hf, rfl⟩⟩
  exact Module.Finite.map _ _

theorem metEx : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  intro hP D c hc j _ s hs
  obtain ⟨ipD, hpure, hhermD, hposD⟩ := GlobalTheory.ChainOnto.exists_ipD_smT D s.V s.par s.M
  set J : Set (GA D s.V) := (s.J : Set (GA D s.V))
  set χ : GA D s.V → ℂ := 1
  have hS : SchurMult c.θ s.M J χ s.ν s.fd := GlobalTheory.MultFinite.schurMult hP s.ν s.fd
  obtain ⟨hI1, hI2⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M J χ s.ν s.fd hc.inf hs.haar hs.fund hS
    (GlobalTheory.GardingVec.sm_ne_bot D s.V s.par s.M)
  let T : s.CC c → MMap s.M := fun x => PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
  have hT : ∀ x : s.CC c, T x ∈ Mult c.θ s.M J χ := fun x => (mem_multT c.θ s.M J χ _).1 x.2
  have hTadd : ∀ x y : s.CC c, T (x + y) = T x + T y := fun x y => by
    simp only [T, Submodule.coe_add, map_add]
  have hTsmul : ∀ (a : ℂ) (x : s.CC c), T (a • x) = a • T x := fun a x => by
    simp only [T, Submodule.coe_smul, map_smul]
  have hlin : ∀ x y y' : s.CC c, ∀ a : ℂ,
      ipM s.M s.ν s.fd (T x) (T y + a • T y') = ipM s.M s.ν s.fd (T x) (T y) + a * ipM s.M s.ν s.fd (T x) (T y') :=
    fun x y y' a => (hI1 _ (hT x) _ (hT y) _ (hT y') a).1
  have hsym : ∀ x y : s.CC c, ipM s.M s.ν s.fd (T y) (T x) = star (ipM s.M s.ν s.fd (T x) (T y)) :=
    fun x y => (hI1 _ (hT x) _ (hT y) _ (hT y) 0).2
  have hzero : ∀ x : s.CC c, ipM s.M s.ν s.fd (T x) (T 0) = 0 := fun x => by
    have h := hlin x 0 0 1
    rw [one_smul, one_mul, show T 0 + T 0 = T 0 by simp [T]] at h
    linear_combination -h
  have hlin' : ∀ x y y' : s.CC c, ∀ a : ℂ,
      ipM s.M s.ν s.fd (T x) (T (y + a • y')) = ipM s.M s.ν s.fd (T x) (T y) + a * ipM s.M s.ν s.fd (T x) (T y') :=
    fun x y y' a => by rw [hTadd, hTsmul]; exact hlin x y y' a
  let ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => ipM s.M s.ν s.fd (T y) (T x))
      (fun x x' y => by simpa using hlin' y x x' 1)
      (fun a x y => by
        have h := hlin' y 0 x a
        rw [zero_add, hzero, zero_add] at h
        simpa using h)
      (fun x y y' => by
        rw [hsym x (y + y'), hsym x y, hsym x y']
        have h := hlin' x y y' 1
        rw [one_mul, one_smul] at h
        rw [h, star_add])
      (fun a x y => by
        rw [hsym x (a • y), hsym x y]
        have h := hlin' x 0 y a
        rw [zero_add, hzero, zero_add] at h
        rw [h, star_mul', smul_eq_mul, starRingEnd_apply])
  have hip : ∀ x y, ip x y = ipM s.M s.ν s.fd (T y) (T x) := fun _ _ => rfl
  have hpair : ∀ x y : s.CC c, ∀ w w', IntegrableOn (fun g => PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g)) s.fd s.ν ∧
      ∫ g in s.fd, PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g) ∂s.ν = ip x y * ipD w w' := by
    intro x y
    refine GlobalTheory.ChainMetric.integ_pair (μ := s.ν) (A := s.fd) (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
      (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ipD (ip x y) ?_
    intro v v'
    obtain ⟨hi, he⟩ := ipM_spec s.M s.ν s.fd (T y) (T x) (hS hc.inf hs.haar hs.fund _ (hT y) _ (hT x)) v' v
    have e : (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v) g *
        conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v') g)) = fun g => star (T y v' g) * T x v g := by
      funext g
      rw [GlobalTheory.ChainMetric.val_tprod, GlobalTheory.ChainMetric.val_tprod, starRingEnd_apply, mul_comm]
    rw [e, hip, hpure]
    exact ⟨hi, he⟩
  refine ⟨ipD, ip, hpure, hhermD, hposD, fun x y => ?_, fun x hx => ?_, fun x y w w' => (hpair x y w w').1,
    fun x y w w' => (hpair x y w w').2⟩
  · rw [hip, hip, hsym, starRingEnd_apply]
  · rw [hip]
    refine hI2 _ (hT x) fun h0 => hx ?_
    exact Submodule.coe_eq_zero.1 ((LinearEquiv.map_eq_zero_iff _).1 h0)

theorem finDim_and_metEx : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D ∧ MetEx D :=
  fun h h' D => ⟨finDim h D, metEx h' D⟩

end GlobalTheory.EvenMetric

end
