import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelGroupFaceLevelIffFlagGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.DefiniteMult

theorem toMap_mem_levP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → R.cX.toMap R.prX Fn ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB b t Fn hFn hP
  have h := GlobalTheory.DefiniteEnd.isMultMap_toMap hB.models.inf D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX hB.models.cX
    hB.models.prX hFn
  refine (mem_multT R.θ R.MX _ _ _).2 (Submodule.subset_span ⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩)
  have hkC : k ∈ GfC D.sp.X' := hk.1
  obtain ⟨hiff, hchi⟩ := GlobalTheory.T.mem_level_group_face_level_iff_flag_group D G Pl0 T A Ks R F hB.grp.red_R b t k hkC
  have hh := hiff.1 hk
  obtain ⟨hq, hp⟩ := hh
  have hc := hchi hq hp
  have hd := hP ⟨_, hq⟩ hp ((finHom D.sp.X').rangeRestrict g)
  have e : Fn ((finHom D.sp.X').rangeRestrict (g * k)) =
      levChi _ R.βX (datXP R t (R.levR F b)) k • Fn ((finHom D.sp.X').rangeRestrict g) :=
    (congrArg Fn (map_mul _ g k)).trans (hd.trans (congrArg (· • Fn ((finHom D.sp.X').rangeRestrict g)) hc.symm))
  have e2 : R.cX.ext Fn (g * k) = levChi _ R.βX (datXP R t (R.levR F b)) k • R.cX.ext Fn g :=
    ((congrArg (R.cX.ρ (g * k)⁻¹) e).trans
      (LinearMap.congr_fun (rho_right_inv R.cX.ρ g (hB.models.cX.1 _ (inv_mem hkC))) _)).trans (map_smul _ _ _)
  exact (congrArg (fun w => R.prX w (PiTensorProduct.tprod ℂ v)) e2).trans (LinearMap.congr_fun (map_smul R.prX _ _) _)

end GlobalTheory.DefiniteMult

end
