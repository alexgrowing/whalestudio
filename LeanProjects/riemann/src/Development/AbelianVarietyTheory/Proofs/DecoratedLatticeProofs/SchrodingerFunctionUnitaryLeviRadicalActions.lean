import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProof
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

noncomputable section

namespace GlobalTheory.Core.Rk.SchLaws

variable {D : D7}

theorem isWeilDatumO_zero_one {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χB : (AE D)ˣ →* Circle}
    {omh : WRep (dblSp A) B} (hW : IsWeilDatumO ψ (dblSp A) B 1 χB omh) :
    IsWeilDatumO ψ (zeroSp D) B 1 χB 1 where
  std := hW.std
  hecS := hW.hecS
  hecT := hW.hecT
  resS := ⟨hW.resS.1, fun η _ a => by rw [show (zeroSp D).rank = 0 from rfl, pow_zero]; rfl⟩
  resT := hW.resT
  om_pres := fun _ _ hf => hf
  om_heis := fun g h w₀ f _ => by
    have e : actO (zeroSp D) B g h w₀ = w₀ := Matrix.ext fun _ j => Fin.elim0 j
    rw [e]; rfl
  om_aut := fun _ _ _ _ _ _ => rfl
  om_cont := fun _ _ _ => continuous_const
  om_unit := fun _ _ _ _ _ _ _ => rfl
  om_split := fun e _ g h _ _ x y hx _ => by
    have hx1 : x = 1 := by
      apply Units.ext
      unfold IsDetAt at hx
      haveI : IsEmpty (Fin (zeroSp D).rank) := Fin.isEmpty
      rw [Matrix.det_isEmpty] at hx
      rw [hx]; simp
    refine ⟨1, one_pos, fun ℓ _ f _ => ?_⟩
    simp [splitFacO, hx1]

theorem chr_gramOf_eq (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (x : Mx D B.rank A.rank) (c : skewA D A.rank) :
    chr ψ (gramOf B x) c = ψ ((dblDec A).qS B c x) := by
  rw [chr, HypDec.qS, HypDec.symplOH_extX_extY, pairS, adj_mul, mem_skewA.1 c.2, Matrix.mul_assoc, Matrix.neg_mul,
    Matrix.trace_neg, map_neg (trHalf D), Matrix.trace_mul_comm, gramOf]

theorem sch_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → (∀ h x, sch ψ A B ν 𝓨 (omh (1, h) f) x = sch ψ A B ν 𝓨 f (mt B h⁻¹ ⬝ x)) ∧ (∀ (m : GL (Fin A.rank) (AE D)) x, sch ψ A B ν 𝓨 (omh ((dblDec A).levi m, 1) f) x = ((χB⁻¹ (Matrix.GeneralLinearGroup.det m) : Circle) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det m)) ((B.rank : ℂ) / 2) * sch ψ A B ν 𝓨 f (x ⬝ m.1)) ∧ (∀ c x, sch ψ A B ν 𝓨 (omh ((dblDec A).nC c, 1) f) x = chr ψ (gramOf B x) c * sch ψ A B ν 𝓨 f x) ∧ swSec A B omh ν 𝓨 f 1 = sch ψ A B ν 𝓨 f 0 := by
  intro D ψ A B χB omh hW ν 𝓨 hν f hf
  have h := GlobalTheory.MixSourceFormulas.mixed_source D ψ (dblSp A) (zeroSp D) B A.rank (dblDec A) 1 χB omh 1 hW
    (isWeilDatumO_zero_one hW) ν 𝓨 hν f hf
  refine ⟨fun g x => ?_, fun m x => ?_, fun c x => ?_, ?_⟩
  · rw [sch, h.target]
    rfl
  · rw [sch, h.levi, Pi.smul_apply, smul_eq_mul, MonoidHom.inv_apply, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, GlobalTheory.Doubling.npow,
      Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    push_cast
    rfl
  · rw [sch, h.centre, chr_gramOf_eq ψ A B]
    rfl
  · rw [sch, mixS_dblDec_zero, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec, Prod.mk_one_one, map_one, Module.End.one_apply]

end GlobalTheory.Core.Rk.SchLaws

end
