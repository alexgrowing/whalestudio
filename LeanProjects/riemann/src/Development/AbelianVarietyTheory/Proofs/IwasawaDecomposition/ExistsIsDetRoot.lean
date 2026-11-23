import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilDatumOOfRankEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoordSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctionsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilTwist

variable {D : D7}

theorem exists_isDetRoot (V : HSp D) (g : GA D V) : ∃ x, IsDetRoot V g x := by
  obtain ⟨a, aval, -⟩ := GlobalTheory.Member.exists_muVal D V 1 (isHC_one D).1 (fun _ => rfl)
  exact aval.1 g

theorem twist_both {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' ν ν' : IdC D}
    (ha : AdmE V W χ χ') (hν : IsHC D ν) (rν : ResEta D ν 0) (hν' : IsHC D ν') (rν' : ResEta D ν' 0)
    {om om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (ho : IsWeilOn ψ V W χ χ' om)
    (ho' : IsWeilOn ψ V W (χ * ν) (χ' * ν') om') {g : GA D V} {h : GA D W} {x y : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hy : IsDetRoot W h y) :
    om' (g, h) = (((ν' x)⁻¹ * ν y : Circle) : ℂ) • om (g, h) := by
  obtain ⟨⟨C, hC⟩, -⟩ := GlobalTheory.Mem.HeckeExp.hecke_exp_laws D
  have hmul : ∀ a b : IdC D, IsHC D a → IsHC D b → IsHC D (a * b) := fun a b k l =>
    (hC _).1 (C.mul_mem ((hC _).2 k) ((hC _).2 l))
  have ha' : AdmE V W (χ * ν) (χ' * ν') :=
    ⟨ha.1, hmul _ _ ha.2.1 hν, hmul _ _ ha.2.2.1 hν', resEta_mul ha.2.2.2.1 rν, resEta_mul ha.2.2.2.2 rν'⟩
  obtain ⟨o, hd, ht⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W χ χ' om ha ho
  obtain ⟨o', hd', ht'⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W _ _ om' ha' ho'
  obtain ⟨o'', hd'', hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hψ V W χ χ' ν ν' o hd hν.1 hν'.1 rν rν'
  obtain ⟨e, -, -, he, -, -, -, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W ha.1.le
  refine LinearMap.ext fun Φ => Subtype.ext (funext fun w => ?_)
  have hΦ : IsThetaFunO ψ V W fun x => Φ.1 (toTWsmall V W x) := by
    simp only [← he]
    exact (hth ψ _).2 (mem_ThS.1 Φ.2)
  have k := GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ V W _ _ o' o'' hd' hd'' (g, h) _ hΦ
  rw [ht', hv g h x y hx hy, LinearMap.smul_apply, ht] at k
  have k2 := congrFun k (e.symm w)
  simp only [← he, e.apply_symm_apply, Pi.smul_apply] at k2
  exact k2

theorem weilTwEq : ∀ D : D7, WeilTwEq D := by
  intro D ψ hψ V W χ χ' ν ha hν rν om ho
  have r1 : ResEta D 1 0 := ⟨rν.1, fun _ _ _ => by simp⟩
  refine ⟨fun om' ho' g h x hx => ?_, fun om' ho' g h x hx => ?_⟩
  · obtain ⟨y, hy⟩ := exists_isDetRoot W h
    have := twist_both hψ ha (isHC_one D) r1 hν rν ho (om' := om') (by rwa [mul_one]) hx hy
    rwa [MonoidHom.one_apply, mul_one] at this
  · obtain ⟨y, hy⟩ := exists_isDetRoot V g
    have := twist_both hψ ha hν rν (isHC_one D) r1 ho (om' := om') (by rwa [mul_one]) hy hx
    rwa [MonoidHom.one_apply, inv_one, one_mul] at this

end GlobalTheory.Mem.WeilTwist
