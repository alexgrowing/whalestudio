import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ToTermAct

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pair

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

def mvRow (L : Iof Y.TR) (r : Rw (Y.what₂ u) (Y.what₂ u') Y.TR) : Rw (Y.what₂ u) (Y.what₂ u') Y.TR :=
  (r.1, r.2.1, r.2.2 * L)

theorem row_act (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (q : {Λ // Λ ∈ Y.what₂ u'})
    (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (s : TT Y u u') (hs : s.lam' = q.1) :
    row Y (act Y q γ s) = mvRow (levi Y.TR (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1))⁻¹ (row Y s) := by
  unfold row rowOf mvRow
  rw [iota_act hIR q γ s hs]
  rfl

theorem pair_core (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC)
    (hAR : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC) (hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll)
    (hOI : OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (q : {Λ // Λ ∈ Y.what₂ u'})
    (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (a₁ a₂ b₁ b₂ : TT Y u u') (ha₁ : a₁.lam' = q.1) (ha₂ : a₂.lam' = q.1)
    (hr : row Y a₁ = row Y a₂) (hr' : row Y b₁ = row Y b₂) (hγ : b₁ = act Y q γ a₁) (h2 : a₂.toTerm = b₂.toTerm) :
    Formalism.MainNotions.S.hsInner (amp Y a₁) (amp Y a₂) = Formalism.MainNotions.S.hsInner (amp Y b₁) (amp Y b₂) := by
  have h1 : row Y (act Y q γ a₁) = row Y b₂ := by rw [← hγ]; exact hr'
  have hrow : row Y (act Y q γ a₂) = row Y b₂ :=
    (row_act hIR q γ a₂ ha₂).trans ((congrArg (mvRow _) hr.symm).trans ((row_act hIR q γ a₁ ha₁).symm.trans h1))
  have hb2 : act Y q γ a₂ = b₂ := hRF u u' _ _ ((toTerm_act q γ a₂).trans h2) hrow
  have hs : ((γ.1 : Gam X u') : X.B.I.GA).1 ∈ Hinf X u' := (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.1.2).2).1
  have hP : X.piU u' (((γ.1 : Gam X u') : X.B.I.GA).1)⁻¹ =
      cl (Formalism.L2.SG.Pf.SatGramActL.piUe u' (((γ.1 : Gam X u') : X.B.I.GA).1) hs).symm := by
    ext v; rfl
  rw [hγ, ← hb2, amp_act hB hAR hOI q γ a₁ ha₁, amp_act hB hAR hOI q γ a₂ ha₂, hP]
  exact (hsInner_comp_isom _ _ _).symm

theorem pairAmpConst_of (hN : ∀ w, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X w Y.hK)
    (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC)
    (hAR : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC) (hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll)
    (hOI : ∀ w w', OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w')) : PairAmpConst Y := by
  intro u u' t₁ t₂ r r' hr hr'
  have hab : r.1.1.toTerm = r'.1.1.toTerm := r.1.2.trans r'.1.2.symm
  obtain ⟨γ, hγ⟩ := fib_gam (hN u') hab
  have hl := lam_eq_of_row hr
  exact pair_core hRF hIR hAR hB (hOI u u') _ γ r.1.1 r.2.1 r'.1.1 r'.2.1 rfl hl.2.symm hr hr' hγ
    (r.2.2.trans r'.2.2.symm)

end Pair

end Formalism.L2.SG.Pf.KernelOfEmbedding
