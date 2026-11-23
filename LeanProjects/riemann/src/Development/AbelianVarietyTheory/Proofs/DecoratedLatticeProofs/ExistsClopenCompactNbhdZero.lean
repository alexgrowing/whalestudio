import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AfTensNbhd

variable (F : Type) [Field F] [NumberField F]

def intAf : Set (FiniteAdeleRing (𝓞 F) F) :=
  {a | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}

theorem isOpen_intAf : IsOpen (intAf F) := by
  unfold intAf
  exact RestrictedProduct.isOpen_forall_mem (fun v => by
    exact Valued.isOpen_integer _)

theorem isCompact_intAf : IsCompact (intAf F) :=
  (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1

theorem isClosed_intAf : IsClosed (intAf F) := by
  haveI := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' F
  exact (isCompact_intAf F).isClosed

theorem zero_mem_intAf : (0 : FiniteAdeleRing (𝓞 F) F) ∈ intAf F := fun v => by
  exact zero_mem _

end GlobalTheory.AfTensNbhd

namespace GlobalTheory.AfTensNbhd

section Tens

variable (F : Type) [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E]

local notation "A" => FiniteAdeleRing (𝓞 F) F

noncomputable def coordEquiv : (A ⊗[F] E) ≃ₗ[A] (Module.Free.ChooseBasisIndex F E → A) :=
  (Algebra.TensorProduct.basis A (Module.Free.chooseBasis F E)).equivFun

local instance : IsModuleTopology A (A ⊗[F] E) := ⟨rfl⟩

theorem continuous_coordEquiv : Continuous (coordEquiv F E) :=
  IsModuleTopology.continuous_of_linearMap (coordEquiv F E).toLinearMap

theorem continuous_coordEquiv_symm : Continuous (coordEquiv F E).symm := by
  haveI : ContinuousAdd (A ⊗[F] E) := IsModuleTopology.toContinuousAdd A _
  haveI : ContinuousSMul A (A ⊗[F] E) := IsModuleTopology.toContinuousSMul A _
  exact IsModuleTopology.continuous_of_linearMap (coordEquiv F E).symm.toLinearMap

def intTens : Set (A ⊗[F] E) := coordEquiv F E ⁻¹' Set.univ.pi (fun _ => intAf F)

theorem isClopen_intTens : IsClopen (intTens F E) :=
  ⟨(isClosed_set_pi fun _ _ => isClosed_intAf F).preimage (continuous_coordEquiv F E),
   (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_intAf F).preimage (continuous_coordEquiv F E)⟩

theorem isCompact_intTens : IsCompact (intTens F E) := by
  have h := (isCompact_univ_pi fun _ => isCompact_intAf F).image (continuous_coordEquiv_symm F E)
  convert h using 1
  ext x
  constructor
  · intro hx
    exact ⟨coordEquiv F E x, hx, (coordEquiv F E).symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    change coordEquiv F E ((coordEquiv F E).symm y) ∈ Set.univ.pi (fun _ => intAf F)
    rw [LinearEquiv.apply_symm_apply]
    exact hy

theorem zero_mem_intTens : (0 : A ⊗[F] E) ∈ intTens F E := by
  intro i _
  rw [map_zero]
  exact zero_mem_intAf F

end Tens

end GlobalTheory.AfTensNbhd

namespace GlobalTheory.AfTensNbhd

theorem exists_clopen_compact_nbhd_zero : ∀ (D : D7) (m n : ℕ), ∃ U : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U ∧ IsCompact U ∧ (0 : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U := by
  intro D m n
  refine ⟨Set.univ.pi (fun _ => Set.univ.pi (fun _ => intTens D.host.F D.host.E)), ⟨?_, ?_⟩, ?_, ?_⟩
  · exact isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => (isClopen_intTens D.host.F D.host.E).1
  · exact isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => (isClopen_intTens D.host.F D.host.E).2
  · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_intTens D.host.F D.host.E
  · intro i _ j _
    exact zero_mem_intTens D.host.F D.host.E

end GlobalTheory.AfTensNbhd
