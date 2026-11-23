import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQOfCongE
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

set_option maxHeartbeats 1600000 in
private theorem mem_GLint_and_exists_liftsInv_of_congE : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K),
    MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
      ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' →
        ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := by
  classical
  intro B X I hI u a i hi b P g z hmid
  have hO := hI.idx_ok a
  have hpr := (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P
    ((I.idx a).h i (Idx.get b hi) P) g).mp ⟨z, hmid⟩
  have hgi : g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 := hO.int i (Idx.get b hi) P hpr
  refine ⟨hgi, fun g' hg' hc => ?_⟩
  have hb : b.1 = some (Idx.get b hi) := (Option.some_get _).symm
  have hstd : ∀ (k : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) {x : Sp B.fields.E (B.R.N i)},
      x ∈ stdAt B.fields.E (B.R.N i) P.1 → k.1 x ∈ stdAt B.fields.E (B.R.N i) P.1 :=
    fun k _ hx => GlobalTheory.TopStep.glint_mem k hx
  refine ⟨⟨1, ⟨fun w => if h : w.1 = P.1 then
      (GlobalTheory.TopStep.redGL (B.R.N i) w.1 ⟨g, by rw [h]; exact hgi⟩)⁻¹ else 1, ?_⟩,
    ⟨fun w => if h : w.1 = P.1 then
      (⟨g', by rw [h]; exact hg'⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) w.1))⁻¹ else 1, ?_⟩⟩, ?_, ?_, ?_⟩
  · rw [LevFam.grp, Subgroup.mem_pi]
    intro w _
    simp only [levGAt, hb, Option.elim]
    by_cases hw : w.1 = P.1
    · rw [dif_pos hw]
      apply inv_mem
      rw [hO.grpG]
      obtain ⟨w, hwG⟩ := w
      simp only at hw
      subst hw
      exact ⟨g, hpr, fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hgi⟩ hx⟩
    · rw [dif_neg hw]
      exact one_mem _
  · rw [LevQFam.grp, Subgroup.mem_pi]
    intro w _
    simp only [levQAt, hb, Option.elim]
    by_cases hw : w.1 = P.1
    · rw [dif_pos hw]
      apply inv_mem
      obtain ⟨w, hwQ⟩ := w
      simp only at hw
      subst hw
      have hgQ : (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) ∈
          ((I.idx a).levQ i (Idx.get b hi) ⟨P.1, hwQ⟩).H := by
        rw [hO.grpQ, Subgroup.mem_subgroupOf]
        exact hpr
      set k := (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1))⁻¹ with hk
      have hkg : ∀ v, k.1 (g v) = v := by
        intro v
        have h1 : k * (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) = 1 := inv_mul_cancel _
        exact congrArg (fun m : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1) => m.1 v) h1
      have hdeep := levQ_deep I hI a i hi (Idx.get b hi) P hwQ (k * ⟨g', hg'⟩)
      obtain ⟨hd, -⟩ := hdeep (by
        intro x hx
        have hneg := Submodule.neg_mem _ (hstd k (hc x hx))
        rw [map_smul, map_sub, hkg, ← smul_neg, neg_sub] at hneg
        exact hneg)
      have e2 : (⟨g', hg'⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) = ⟨g, hgi⟩ * (k * ⟨g', hg'⟩) := by
        rw [hk, mul_inv_cancel_left]
      rw [e2]
      exact mul_mem hgQ hd
    · rw [dif_neg hw]
      exact one_mem _
  · exact map_one (ufGL B.fields.E (B.R.N i))
  · refine ⟨hg', ?_, ?_⟩
    · intro h x hx
      dsimp only
      rw [dif_pos rfl, inv_inv, ← GlobalTheory.TopStep.redV_redGL ⟨g, hgi⟩ hx]
      have hD : (I.cst a).D P = 1 := hO.depthG P h
      have hq := hc x hx
      rw [hD, pow_one] at hq
      funext l
      have h1 : IntAt P.1 (g x l) := GlobalTheory.TopStep.mem_stdAt.mp (hstd ⟨g, hgi⟩ hx) l
      have h2 : IntAt P.1 (g' x l) := GlobalTheory.TopStep.mem_stdAt.mp (hstd ⟨g', hg'⟩ hx) l
      have h3 : IntAt P.1 (((qOf P.1 : ℕ) : B.fields.E)⁻¹ * (g x l - g' x l)) := GlobalTheory.TopStep.mem_stdAt.mp hq l
      have h0 := GlobalTheory.TopStep.redP_eq_zero_of_div (P := P.1) (a := g x l - g' x l) (by rw [div_eq_inv_mul]; exact h3)
      rw [GlobalTheory.TopStep.reduction_sub h1 h2, sub_eq_zero] at h0
      exact h0.symm
    · intro h
      dsimp only
      rw [dif_pos rfl, inv_inv]
  · intro P' hP'
    have hne : P'.1 ≠ P.1 := fun e => hP' (Subtype.ext e)
    refine ⟨one_mem _, ?_, ?_⟩
    · intro h x hx
      dsimp only
      rw [dif_neg hne, inv_one]
      simp
    · intro h
      dsimp only
      rw [dif_neg hne, inv_one]
      all_goals rfl

open Classical in

theorem midAt_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K),
    MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
      ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' →
        ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := mem_GLint_and_exists_liftsInv_of_congE

end GlobalTheory.Mem.Col2.AdT

end
