import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ToTermAct
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LiftMassCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActRow
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AmpIota

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.FibreEq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {u u' : D.what₂.Word}

theorem partner (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC)
    {l₁ l₂ s₁ : TT Y u u'} (hrow : rowOf Y.TR (Y.cs u) (Y.cs u') l₁ = rowOf Y.TR (Y.cs u) (Y.cs u') l₂)
    (h : l₁.toTerm = s₁.toTerm) :
    ∃ s₂ : TT Y u u', s₂.toTerm = l₂.toTerm ∧
      rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ := by
  obtain ⟨γ, rfl⟩ := Formalism.L2.SG.Pf.KernelOfEmbedding.fib_gam hN h
  refine ⟨Formalism.L2.SG.Pf.KernelOfEmbedding.act Y ⟨l₁.lam', l₁.mem'⟩ γ l₂, Formalism.L2.SG.Pf.KernelOfEmbedding.toTerm_act _ _ _, ?_⟩
  have hl := Formalism.L2.SG.Pf.KernelOfEmbedding.lam_eq_of_row hrow
  have i1 := Formalism.L2.SG.Pf.KernelOfEmbedding.iota_act hIR ⟨l₁.lam', l₁.mem'⟩ γ l₁ rfl
  have i2 := Formalism.L2.SG.Pf.KernelOfEmbedding.iota_act hIR ⟨l₁.lam', l₁.mem'⟩ γ l₂ hl.2.symm
  have hι : iotaOf Y.TR (Y.cs u) (Y.cs u') l₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') l₂ :=
    congrArg (fun r => r.2.2) hrow
  unfold rowOf
  simp only [Prod.mk.injEq, Subtype.mk.injEq]
  exact ⟨hl.1, hl.2, by rw [i1, i2, hι]⟩

theorem fibreCountEq_of (hF : FinX Y) (hN : ∀ u' : D.what₂.Word, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK)
    (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y) :
    Formalism.L2.SG.Pf.KernelOfEmbedding.FibreCountEq hF := by
  intro u u' q
  let _ := hF.fibFT q.1.1
  let _ := hF.fibFT q.1.2
  obtain ⟨l₁, l₂, hrow⟩ := q.2
  have hinner : ∀ r₁ : fib Y q.1.1,
      ∑ r₂ : fib Y q.1.2, (if Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₁.1 = Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₂.1 then
        Formalism.MainNotions.S.wRow D (X.Fu u') r₁.1.lam' else 0) = Formalism.MainNotions.S.wRow D (X.Fu u') r₁.1.lam' := by
    intro r₁
    obtain ⟨s₂, hs₂t, hs₂r⟩ := partner (hN u') hIR hrow (l₁.2.trans r₁.2.symm)
    have hs₂ : s₂.toTerm = q.1.2 := hs₂t.trans l₂.2
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (fib Y q.1.2))) (show fib Y q.1.2 from ⟨s₂, hs₂⟩)
      (fun b _ hb => ?_) (fun hb => absurd (Finset.mem_univ _) hb)).trans (if_pos hs₂r)
    refine if_neg (fun hrb => hb (Subtype.ext ?_))
    exact hRF u u' b.1 s₂ (b.2.trans hs₂.symm) (hrb.symm.trans hs₂r)
  have hlam : ∀ r₁ : fib Y q.1.1, r₁.1.lam' = l₁.1.lam' := fun r₁ =>
    Formalism.L2.SG.Pf.FibreCounting.lam'_eq (r₁.2.trans l₁.2.symm)
  have hsum : ∑ r₁ : fib Y q.1.1, ∑ r₂ : fib Y q.1.2, (if Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₁.1 = Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₂.1
      then Formalism.MainNotions.S.wRow D (X.Fu u') r₁.1.lam' else 0) =
      (Fintype.card (fib Y q.1.1) : ℝ) * Formalism.MainNotions.S.wRow D (X.Fu u') l₁.1.lam' := by
    rw [Finset.sum_congr rfl (fun r₁ _ => (hinner r₁).trans (by rw [hlam r₁])), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.sum_prod_type]
  refine hsum.trans ?_
  obtain ⟨f, hf⟩ := Formalism.L2.SG.Pf.FibreCounting.fib_bij (hN u') l₁.1
  have hcard : Fintype.card (fib Y q.1.1) = Nat.card ↥(autLz D (X.Fu u') l₁.1.lam') := by
    rw [← Nat.card_eq_fintype_card]
    have e1 : fib Y q.1.1 ≃ {s : TT Y u u' // s.toTerm = l₁.1.toTerm} :=
      Equiv.subtypeEquivRight (fun s => by rw [l₁.2])
    exact (Nat.card_congr e1).trans (Nat.card_congr (Equiv.ofBijective f hf))
  have hpos : 0 < Fintype.card (fib Y q.1.1) := Fintype.card_pos_iff.2 ⟨l₁⟩
  unfold Formalism.MainNotions.S.wRow
  rw [← hcard]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 hpos.ne')

theorem fibreCountEq_of' (hF : FinX Y) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y) :
    Formalism.L2.SG.Pf.KernelOfEmbedding.FibreCountEq hF :=
  fibreCountEq_of hF (fun u' => Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK) hIR hRF

theorem FibreCountEq_holds (hF : FinX Y) : Formalism.L2.SG.Pf.KernelOfEmbedding.FibreCountEq hF :=
  fibreCountEq_of' hF Formalism.L2.SG.Pf.iotaRepC_holds
    (Formalism.L2.SG.Pf.Act.rowFree_of (fun u' => Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK) Formalism.L2.SG.Pf.iotaRepC_holds)

end Formalism.L2.SG.Pf.FibreEq
