import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToBlocksMulFinZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PenVol

section Gen

open ValuativeRel

variable {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n]

theorem mulVec_mem_box_of_int (A : Matrix n n k) (hA : ∀ i j, valuation k (A i j) ≤ 1) {c : kˣ} {y : n → k}
    (hy : y ∈ GlobalTheory.StepData.box n c) : A *ᵥ y ∈ GlobalTheory.StepData.box n c := by
  intro i
  show valuation k ((A *ᵥ y) i) ≤ valuation k (c : k)
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  calc valuation k (A i j) * valuation k (y j) ≤ 1 * valuation k (c : k) := mul_le_mul' (hA i j) (hy j)
    _ = valuation k (c : k) := one_mul _

theorem val_le_one_of_mem_KO {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (i j : n ⊕ Fin 0) :
    valuation k (g.val i j) ≤ 1 := by
  obtain ⟨h, rfl⟩ := hg
  exact (h.val i j).2

theorem toBlocks₁₁_mulVec_mem_box {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) {c : kˣ}
    {y : n → k} (hy : y ∈ GlobalTheory.StepData.box n c) : g.val.toBlocks₁₁ *ᵥ y ∈ GlobalTheory.StepData.box n c :=
  mulVec_mem_box_of_int _ (fun i j => val_le_one_of_mem_KO hg (Sum.inl i) (Sum.inl j)) hy

def boxQ {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) :
    ((n → k) ⧸ GlobalTheory.StepData.box n c) →ₗ[𝒪[k]] ((n → k) ⧸ GlobalTheory.StepData.box n c) :=
  Submodule.mapQ _ _ ((Matrix.mulVecLin g.val.toBlocks₁₁).restrictScalars 𝒪[k])
    (fun _ hy => toBlocks₁₁_mulVec_mem_box hg hy)

theorem boxQ_mk {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) (y : n → k) :
    boxQ hg c (Submodule.Quotient.mk y) = Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) := rfl

def boxAct (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) :
    MulAction J ((n → k) ⧸ GlobalTheory.StepData.box n c) where
  smul g q := boxQ (hJ g.2) c q
  one_smul q := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show boxQ _ c _ = _
    rw [boxQ_mk, show ((1 : J) : GL (n ⊕ Fin 0) k).val = 1 from rfl, toBlocks_one_fin_zero, Matrix.one_mulVec]
  mul_smul g h q := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show boxQ _ c _ = boxQ _ c (boxQ _ c _)
    rw [boxQ_mk, boxQ_mk, boxQ_mk, show ((g * h : J) : GL (n ⊕ Fin 0) k).val = g.val.val * h.val.val from rfl,
      toBlocks_mul_fin_zero, Matrix.mulVec_mulVec]

theorem relIndex_cosStab_box (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ)
    (x : (n → k) ⧸ GlobalTheory.StepData.box n c) :
    (cosStab J (GlobalTheory.StepData.box n c) x).relIndex J = Nat.card {yb | GlobalTheory.QPl.SameOrb J (GlobalTheory.StepData.box n c) x yb} := by
  letI := boxAct J hJ c
  have smk : ∀ (g : J) (y : n → k), g • (Submodule.Quotient.mk y : (n → k) ⧸ GlobalTheory.StepData.box n c) =
      Submodule.Quotient.mk (g.val.val.toBlocks₁₁ *ᵥ y) := fun _ _ => rfl
  have hst : (cosStab J (GlobalTheory.StepData.box n c) x).subgroupOf J = MulAction.stabilizer J x := by
    ext g
    rw [Subgroup.mem_subgroupOf, mem_cosStab, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [smk]
      exact (h y).2 rfl
    · intro h
      refine ⟨g.2, fun y => ?_⟩
      rw [← smk]
      constructor
      · intro h'
        rw [← h] at h'
        exact smul_left_cancel g h'
      · intro h'
        rw [h', h]
  have horb : MulAction.orbit J x = {yb | GlobalTheory.QPl.SameOrb J (GlobalTheory.StepData.box n c) x yb} := by
    ext yb
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq, GlobalTheory.QPl.SameOrb]
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨g.1, g.2, y, rfl, (smk g y).symm⟩
    · rintro ⟨g, hg, y, rfl, h⟩
      exact ⟨⟨g, hg⟩, by rw [smk]; exact h⟩
  rw [Subgroup.relIndex, hst, MulAction.index_stabilizer, horb, Nat.card_coe_set_eq]

end Gen

end GlobalTheory.PenVol

end

namespace GlobalTheory.PenVol

theorem relIndex_cosStab_eq_wt {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E}
    (G : QGeo v B PP) {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) (y : E.Ch (G.s + 1)) :
    (((GlobalTheory.PenVol.cosStab ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (GlobalTheory.StepData.box _ (G.ϖ ^ E.M)) (E.cos y)).relIndex
      (GlobalTheory.SplitWeil.KO G.k _) : ℕ) : ℂ) = E.wt (G.s + 1) y := by
  have hJ := E.le (G.s + 1) 0 rfl
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (cosStab_le _ _ _) hJ, relIndex_cosStab_box _ hJ, E.wt_pen y,
    E.idx_mid (G.s + 1) 0 rfl]
  push_cast
  ring

end GlobalTheory.PenVol
