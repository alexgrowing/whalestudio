import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties

namespace IteratedIwahori
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.IterJ

section Gen
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem intM_submatrix_iff (e : a ≃ b) (M : Matrix a a k) :
    GlobalTheory.StepData.IntM (M.submatrix e.symm e.symm) ↔ GlobalTheory.StepData.IntM M :=
  ⟨fun h i j => by simpa using h (e i) (e j), fun h _ _ => h _ _⟩

theorem reGL_mem_KO_iff (e : a ≃ b) (g : GL a k) : reGL e g ∈ KO k b ↔ g ∈ KO k a := by
  rw [GlobalTheory.StepData.mem_KO, GlobalTheory.StepData.mem_KO, ← map_inv, reGL_val, reGL_val,
    intM_submatrix_iff, intM_submatrix_iff]

omit [Fintype a] [Fintype b] [DecidableEq b] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem symm_sub_one_apply [Fintype a] [Fintype b] [DecidableEq b] (e : a ≃ b) (h : GL b k) (x y : a) :
    (((reGL e).symm h).val - 1) x y = (h.val - 1) (e x) (e y) := by
  simp [reGL_symm_val, Matrix.one_apply]

end Gen

section Iter
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

theorem blk_le {j : ℕ} (x : Ix r t j) : Ix.blk x ≤ j := by
  rcases x with x | ⟨c, s⟩
  · simp [Ix.blk]
  · simpa [Ix.blk] using c.2

theorem blk_ixSucc_inl {j : ℕ} (x : Ix r t j) : Ix.blk (ixSucc r t j (Sum.inl x)) = Ix.blk x := by
  rcases x with x | ⟨c, s⟩ <;> simp [Ix.blk, ixSucc]

theorem blk_ixSucc_inr {j : ℕ} (s : t) : Ix.blk (ixSucc r t j (Sum.inr s)) = j + 1 := by
  simp [Ix.blk, ixSucc]

theorem mem_iter_J (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (h : GL (Ix r t j) k) :
    h ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ h ∈ KO k (Ix r t j) ∧
      (∀ a b, Ix.blk b < Ix.blk a → valuation k (h.val a b) < 1) ∧
      ∀ a b : r, valuation k ((h.val - 1) (Sum.inl a) (Sum.inl b)) < 1 := by
  induction j with
  | zero =>
    rw [TypeDatum.iter_zero]
    have hK : (reGL (ixZero r t)).symm h ∈ KO k r ↔ h ∈ KO k (Ix r t 0) := by
      rw [← reGL_mem_KO_iff (ixZero r t), MulEquiv.apply_symm_apply]
    have mem : h ∈ ((TypeDatum.principal k r).reindex (ixZero r t)).J ↔
      (reGL (ixZero r t)).symm h ∈ KOne k r := Iff.rfl
    rw [mem, GlobalTheory.StepData.mem_KOne]
    constructor
    · intro hh
      refine ⟨hK.1 (GlobalTheory.StepData.KOne_le_KO (GlobalTheory.StepData.mem_KOne.2 hh)), fun a b hab => ?_, fun a b => ?_⟩
      · rcases a with a | ⟨c, _⟩
        · simp [Ix.blk] at hab
        · exact c.elim0
      · have := hh a b
        rwa [symm_sub_one_apply] at this
    · rintro ⟨-, -, h3⟩ a b
      rw [symm_sub_one_apply]
      exact h3 a b
  | succ j ih =>
    rw [TypeDatum.iter_succ]
    have hK : (reGL (ixSucc r t j)).symm h ∈ KO k (Ix r t j ⊕ t) ↔ h ∈ KO k (Ix r t (j + 1)) := by
      rw [← reGL_mem_KO_iff (ixSucc r t j), MulEquiv.apply_symm_apply]
    have mem : h ∈ ((((TypeDatum.principal k r).iter t μ hμ j).step t (μ (j + 1)) (hμ _)).reindex (ixSucc r t j)).J ↔
      (reGL (ixSucc r t j)).symm h ∈ ((TypeDatum.principal k r).iter t μ hμ j).stepJ t := Iff.rfl
    have ent : ∀ x y, ((reGL (ixSucc r t j)).symm h).val x y = h.val (ixSucc r t j x) (ixSucc r t j y) := fun _ _ => rfl
    rw [mem, TypeDatum.mem_stepJ_iff]
    constructor
    · rintro ⟨h0, ⟨g, hg, eg⟩, hC⟩
      obtain ⟨-, g2, g3⟩ := (ih g).1 hg
      have eg' : ∀ x y, g.val x y = h.val (ixSucc r t j (Sum.inl x)) (ixSucc r t j (Sum.inl y)) := fun x y => by
        rw [eg]; rfl
      refine ⟨hK.1 h0, fun a b hab => ?_, fun a b => ?_⟩
      · obtain ⟨x, rfl⟩ := (ixSucc r t j).surjective a
        obtain ⟨y, rfl⟩ := (ixSucc r t j).surjective b
        rcases x with x | s <;> rcases y with y | s'
        · rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          rw [← eg']
          exact g2 x y hab
        · rw [blk_ixSucc_inl, blk_ixSucc_inr] at hab
          have := blk_le x
          omega
        · have := hC s y
          rwa [toBlocks₂₁, Matrix.of_apply, ent] at this
        · rw [blk_ixSucc_inr, blk_ixSucc_inr] at hab
          omega
      · have := g3 a b
        have e1 : ∀ c : r, (Sum.inl c : Ix r t (j + 1)) = ixSucc r t j (Sum.inl (Sum.inl c)) := fun c => rfl
        rw [e1 a, e1 b, ← symm_sub_one_apply, Matrix.sub_apply, ent]
        rw [Matrix.sub_apply, eg'] at this
        simpa [Matrix.one_apply] using this
    · rintro ⟨h1, h2, h3⟩
      have h0 := hK.2 h1
      have hC : GlobalTheory.StepData.MaxM ((reGL (ixSucc r t j)).symm h).val.toBlocks₂₁ := fun s y => by
        rw [toBlocks₂₁, Matrix.of_apply, ent]
        refine h2 _ _ ?_
        rw [blk_ixSucc_inl, blk_ixSucc_inr]
        have := blk_le y
        omega
      obtain ⟨⟨g, hg, eg⟩, -⟩ := GlobalTheory.StepData.exists_diag_blocks h0 hC
      have eg' : ∀ x y, g.val x y = h.val (ixSucc r t j (Sum.inl x)) (ixSucc r t j (Sum.inl y)) := fun x y => by
        rw [eg]; rfl
      refine ⟨h0, ⟨g, (ih g).2 ⟨hg, fun a b hab => ?_, fun a b => ?_⟩, eg⟩, hC⟩
      · rw [eg']
        refine h2 _ _ ?_
        rwa [blk_ixSucc_inl, blk_ixSucc_inl]
      · have := h3 a b
        have e1 : ∀ c : r, (Sum.inl c : Ix r t (j + 1)) = ixSucc r t j (Sum.inl (Sum.inl c)) := fun c => rfl
        rw [e1 a, e1 b, ← symm_sub_one_apply, Matrix.sub_apply, ent] at this
        rw [Matrix.sub_apply, eg']
        simpa [Matrix.one_apply] using this

end Iter

theorem blkOf_ixFin {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (j : ℕ)
    (x : Ix (Fin D.R.r) (Fin D.R.t) j) :
    Formalism.L2.DIV.blkOf D.R.r D.R.t (ixFin G t w j x) = Ix.blk x := by
  obtain ⟨h1, h2⟩ := ixFin_val G t w j
  rcases x with a | ⟨c, b⟩
  · simp [Formalism.L2.DIV.blkOf, h1, Ix.blk]
  · have hb := b.2
    have hpos : 0 < D.R.t := by omega
    have hdiv : (b.val + D.R.t * c.val) / D.R.t = c.val := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hb, zero_add]
    simp [Formalism.L2.DIV.blkOf, h2, Ix.blk, hdiv]

theorem mem_stepGroup_map_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∈ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (∀ a b, Formalism.L2.DIV.blkOf D.R.r D.R.t b < Formalism.L2.DIV.blkOf D.R.r D.R.t a → valuation (Kw w) (g.1 a b) < 1) ∧ ∀ a b : Fin ((locGrid G t w).rank (0, j)), a.val < D.R.r → b.val < D.R.r → valuation (Kw w) ((g.1 - 1) a b) < 1 := by
  intro D T L sc G t w hw j g
  have hmap : g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔
      (reGL (ixFin G t w j)).symm g ∈ stepGroup L t w j := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hx
      exact ⟨_, hx, by simp⟩
  have hK : (reGL (ixFin G t w j)).symm g ∈ KO (Kw w) (Ix (Fin D.R.r) (Fin D.R.t) j) ↔
      g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) := by
    rw [← reGL_mem_KO_iff (ixFin G t w j), MulEquiv.apply_symm_apply]
  rw [hmap, stepGroup, if_pos hw, mem_iter_J, hK]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · constructor
    · intro h a b hab
      obtain ⟨x, rfl⟩ := (ixFin G t w j).surjective a
      obtain ⟨y, rfl⟩ := (ixFin G t w j).surjective b
      rw [blkOf_ixFin, blkOf_ixFin] at hab
      exact h x y hab
    · intro h x y hxy
      refine h _ _ ?_
      rwa [blkOf_ixFin, blkOf_ixFin]
  · obtain ⟨h1, -⟩ := ixFin_val G t w j
    constructor
    · intro h a b ha hb
      have e : ∀ (c : Fin ((locGrid G t w).rank (0, j))) (hc : c.val < D.R.r),
          ixFin G t w j (Sum.inl ⟨c.val, hc⟩) = c := fun c hc => Fin.ext (h1 _)
      have := h ⟨a.val, ha⟩ ⟨b.val, hb⟩
      rwa [symm_sub_one_apply, e, e] at this
    · intro h a b
      rw [symm_sub_one_apply]
      exact h _ _ (by rw [h1]; exact a.2) (by rw [h1]; exact b.2)

end GlobalTheory.CompanionTheory.IterJ

end
end

end IteratedIwahori
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∈ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (∀ a b, Formalism.L2.DIV.blkOf D.R.r D.R.t b < Formalism.L2.DIV.blkOf D.R.r D.R.t a → valuation (Kw w) (g.1 a b) < 1) ∧ ∀ a b : Fin ((locGrid G t w).rank (0, j)), a.val < D.R.r → b.val < D.R.r → valuation (Kw w) ((g.1 - 1) a b) < 1 := by
  first | exact @IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff | exact IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff | (intros; apply IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff <;> assumption)

end
end
