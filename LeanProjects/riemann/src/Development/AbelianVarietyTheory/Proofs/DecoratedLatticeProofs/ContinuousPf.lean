import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

theorem PM_map {r : ℕ} {B : Type} [CommRing B] (f : AE D →+* B) (M : Matrix (Fin r) (Fin r) (AE D)) :
    (PM M).map f = f (eps D) • M.map f + f (1 - eps D) • (1 : Matrix (Fin r) (Fin r) B) := by
  ext i j
  simp only [PM, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add, map_mul]
  split_ifs <;> simp

theorem cT_PM {r : ℕ} (M : Matrix (Fin r) (Fin r) (AE D)) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (PM M) =
      eps D • cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M + (1 - eps D) • (1 : Matrix (Fin r) (Fin r) (AE D)) := by
  unfold cT
  rw [PM_map, RingHom.map_sub, RingHom.map_one, sig_eps, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_one]

theorem PM_unit {r : ℕ} (J M : Matrix (Fin r) (Fin r) (AE D))
    (hM : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * J * M = J) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (PM M) * J * PM M = J := by
  rw [cT_PM, PM]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    eps_mul_self, one_sub_mul_self, eps_mul_one_sub, mul_comm (1 - eps D) (eps D), zero_smul, add_zero, zero_add, hM]
  rw [← add_smul, add_sub_cancel, one_smul]

def PGL (D : D7) (r : ℕ) : GL (Fin r) (AE D) →* GL (Fin r) (AE D) where
  toFun g := ⟨PM g.1, PM (g⁻¹).1, by rw [← PM_mul, Units.mul_inv, PM_one], by rw [← PM_mul, Units.inv_mul, PM_one]⟩
  map_one' := Units.ext PM_one
  map_mul' a b := Units.ext (PM_mul a.1 b.1)

theorem PGL_mem (V : HSp D) (g : GL (Fin V.rank) (AE D)) (hg : g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) :
    PGL D V.rank g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
  PM_unit _ g.1 hg

def pf (V : HSp D) (h : GA D V) : GA D V :=
  (⟨PGL D V.rank (matHom V h), PGL_mem V (matHom V h) (Subtype.property (h : ↥(HR (AF D.host.F) D.sp.cm.sig V.gram)))⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

theorem mt_pf (V : HSp D) (h : GA D V) : Formalism.L2.Theta.mt V (pf V h) = PM (Formalism.L2.Theta.mt V h) := rfl

theorem pf_one (V : HSp D) : pf V 1 = 1 := by
  apply Subtype.ext
  show PGL D V.rank (matHom V 1) = 1
  rw [map_one, map_one]

theorem pf_fin (V : HSp D) (h : GA D V) : pf V h ∈ GfC V := by
  show infHom V (pf V h) = 1
  apply Units.ext
  show (Formalism.L2.Theta.mt V (pf V h)).map (infPart D) = 1
  rw [mt_pf, PM_map, infPart_eps, RingHom.map_sub, RingHom.map_one, infPart_eps, sub_zero, zero_smul, zero_add, one_smul]

theorem finM_pf (V : HSp D) (h : GA D V) : finM V rfl (pf V h) = finM V rfl h := by
  rw [finM_rfl, finM_rfl, mt_pf, PM_map, toEAf_eps, RingHom.map_sub, RingHom.map_one, toEAf_eps, sub_self, zero_smul, add_zero, one_smul]

theorem continuous_pf (V : HSp D) : Continuous (pf V) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hm : Continuous fun h : GA D V => Formalism.L2.Theta.mt V h :=
    Units.continuous_val.comp continuous_subtype_val
  have hP : Continuous fun M : Matrix (Fin V.rank) (Fin V.rank) (AE D) => PM M :=
    (continuous_const_smul _).add continuous_const
  refine Continuous.subtype_mk (f := fun h => PGL D V.rank (matHom V h)) (Units.continuous_iff.2 ⟨hP.comp hm, ?_⟩) _
  have e : (fun h : GA D V => ((PGL D V.rank (matHom V h))⁻¹ : GL (Fin V.rank) (AE D)).val) =
      fun h => PM (Formalism.L2.Theta.mt V h⁻¹) := by
    funext h
    rw [← map_inv, ← map_inv]; rfl
  rw [e]
  exact hP.comp (hm.comp continuous_inv)

end GlobalTheory.AdForm.RdLaw
