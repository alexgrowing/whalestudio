import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictAll

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm.CompatPf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

theorem fixedFrameOfWord_isotropic_eq_flag : (F0 X u).X = (X.Fu u).X := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa FlagG.X
  congr 1
  ext x
  constructor
  · rintro ⟨b, -, rfl⟩; exact ⟨b, (fv_cast _ b).symm⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, b.2, fv_cast _ b⟩

theorem compatC : CompatC := by
  rintro D X Y u ⟨s₁, s₂⟩ ⟨-, -, hp⟩
  have hp' : rowOf Y.TR (Y.cs u) (Y.cs u) s₁ = rowOf Y.TR (Y.cs u) (Y.cs u) s₂ := hp
  have hl : s₁.lam = s₂.lam := congrArg (fun r => r.1.1) hp'
  have hl' : s₁.lam' = s₂.lam' := congrArg (fun r => r.2.1.1) hp'
  have hi : iotaOf Y.TR (Y.cs u) (Y.cs u) s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u) s₂ := congrArg (fun r => r.2.2) hp'
  have h := (Formalism.L2.SG.Pf.Act.ratIotaC' Y u u s₁ s₂ hl hl').1 (Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ hl hl' hi)
  refine ⟨hl, hl', fun x hx => ?_⟩
  have hx2 : x ∈ GlobalTheory.HermLat.perp (HV D) (F0 X u).X := hx.2
  rw [GlobalTheory.HermLat.mem_perp_iff, fixedFrameOfWord_isotropic_eq_flag] at hx2
  have hx' : x ∈ Lrep s₁.lam (lf D (X.Fu u)) := by
    refine ⟨hx.1, ?_⟩
    show x ∈ orth (VS D) (X.Fu u).X
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    exact hx2
  have h2 := h x hx'
  unfold NgX at h2
  rw [sup_assoc, sup_idem] at h2
  rw [fixedFrameOfWord_isotropic_eq_flag]
  refine SetLike.le_def.1 (sup_le_sup ?_ le_rfl) h2
  rw [Submodule.ideal_span_singleton_smul]
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hy, rfl⟩
end GlobalTheory.TypeAsm.CompatPf
