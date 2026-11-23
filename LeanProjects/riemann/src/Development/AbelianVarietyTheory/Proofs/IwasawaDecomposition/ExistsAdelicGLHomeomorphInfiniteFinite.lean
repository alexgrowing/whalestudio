import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CuspRep.GASplit
variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

theorem continuous_infEq_symm : Continuous (infEq E).symm := by
  refine continuous_pi fun w => ?_
  exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
    (continuous_apply w)

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_infEq_symm E).comp continuous_fst

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_sInf : Continuous (sInf E) :=
  (continuous_infEq E).prodMk continuous_const

theorem continuous_sFin : Continuous (sFin E) :=
  continuous_const.prodMk continuous_id

theorem continuous_glMap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (p : R →+* S) (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) := by
  refine Continuous.units_map _ ?_
  exact continuous_pi fun i => continuous_pi fun j => hp.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_cornerGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) :
    Continuous (cornerGL a s) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) R => 1 - matN a s 1 + matN a s x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j => hs.comp ((continuous_apply j).comp (continuous_apply i))

def splitMulEquiv : GA E a ≃* GL (Fin a) (Cinf E) × GL (Fin a) (Af E) where
  toFun g := (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g)
  invFun p := infGL E a p.1 * finGL E a p.2
  left_inv g := infGL_mul_finGL g
  right_inv p := by
    obtain ⟨y, k⟩ := p
    refine Prod.ext ?_ ?_ <;> simp
  map_mul' g h := by simp

def splitEquiv : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E) where
  toMulEquiv := splitMulEquiv E a
  continuous_toFun :=
    ((continuous_glMap a (pInf E) (continuous_pInf E))).prodMk (continuous_glMap a (pFin E) (continuous_pFin E))
  continuous_invFun :=
    ((continuous_cornerGL a (sInf E) (continuous_sInf E)).comp continuous_fst).mul
      ((continuous_cornerGL a (sFin E) (continuous_sFin E)).comp continuous_snd)

theorem exists_split : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∃ e : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E),
      ∀ g, e g = (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g) :=
  fun E _ _ _ a => ⟨splitEquiv E a, fun _ => rfl⟩

end GlobalTheory.CuspRep.GASplit
end
