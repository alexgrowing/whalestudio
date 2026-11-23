import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

theorem residue_eq_zero_iff_val_lt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : 𝒪[k]) : residue 𝒪[k] t = 0 ↔ valuation k (t : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem resField_equiv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → (∀ x : 𝓞 D.host.E, q.pr (incA D (x : D.host.E)) ∈ 𝒪[k]) ∧ ∃ ρ : 𝓀[k] ≃+* (𝓞 D.host.E ⧸ PP.asIdeal), ∀ (x : 𝓞 D.host.E) (t : 𝒪[k]), (t : k) = q.pr (incA D (x : D.host.E)) → ρ (residue 𝒪[k] t) = Ideal.Quotient.mk PP.asIdeal x := by
  intro D k _ _ _ _ q PP he
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  have hmem : ∀ x : 𝓞 D.host.E, q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := fun x => by
    rw [q.pr_mem_iff]
    exact mul_mem hint (Formalism.L2.DIV.oToS D.host.F D.host.E x).2
  refine ⟨hmem, ?_⟩
  let ψ : 𝓞 D.host.E →+* 𝒪[k] :=
    ((q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[k] hmem
  have hψ : ∀ x, (ψ x : k) = q.pr (incA D (x : D.host.E)) := fun x => rfl
  let φ : 𝓞 D.host.E →+* 𝓀[k] := (residue 𝒪[k]).comp ψ
  have hker : RingHom.ker φ = PP.asIdeal := by
    ext x
    have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
        toEAf D (incA D (x : D.host.E)) := rfl
    rw [RingHom.mem_ker, RingHom.comp_apply, residue_eq_zero_iff_val_lt, hψ, q.mem_iff_val_lt he, e1, prF_toEAf]
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    set z : EAf D := toEAf D (q.sec a) with hz
    have hprz : q.prF he z = a := by rw [hz, prF_toEAf, q.pr_sec]
    have hoff : (1 - toEAf D q.e) * z = 0 := by
      have he1 : toEAf D q.e * z = z := by
        rw [hz, ← RingHom.map_mul, ← q.sec_pr, q.pr_sec]
      rw [sub_mul, one_mul, he1, sub_self]
    have hzint : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      (q.mem_intAf_iff he z).2 ⟨by rw [hoff]; exact zero_mem _, by rw [hprz]; exact a.2⟩
    obtain ⟨x, hx0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot ⟨z, hzint⟩
    have hx : (⟨z, hzint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E x ∈
        Formalism.L2.DIV.idS D.host.F PP.asIdeal := hx0
    have hv := q.val_lt_of_mem_idS he hx
    refine ⟨x, ?_⟩
    show residue 𝒪[k] (ψ x) = residue 𝒪[k] a
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_val_lt]
    have e1 : (((⟨z, hzint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E x :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = z - toEAf D (incA D (x : D.host.E)) := rfl
    rw [e1, map_sub, hprz, prF_toEAf] at hv
    have e2 : ((ψ x - a : 𝒪[k]) : k) = -((a : k) - q.pr (incA D (x : D.host.E))) := by
      rw [AddSubgroupClass.coe_sub, hψ]; ring
    rw [e2, Valuation.map_neg]; exact hv
  refine ⟨((Ideal.quotEquivOfEq hker).symm.trans (RingHom.quotientKerEquivOfSurjective hsurj)).symm, ?_⟩
  intro x t ht
  have htx : t = ψ x := Subtype.ext (by rw [ht, hψ])
  rw [RingEquiv.symm_apply_eq, htx]
  rfl

end GlobalTheory.FinPl.SplitPt
