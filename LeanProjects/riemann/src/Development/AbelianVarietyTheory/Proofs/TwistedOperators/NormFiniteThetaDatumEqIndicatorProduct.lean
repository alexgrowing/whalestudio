import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.LevelVecNorm.NormFac

variable {E : Type} [Field E] [NumberField E]

instance finKP (PP : Pl E) : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot

theorem norm_char_fin {G : Type} [Group G] [Finite G] (f : G →* ℂˣ) (g : G) : ‖((f g : ℂˣ) : ℂ)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card G) ?_ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

theorem mem_blockTri_blkOf {κ : Type} [CommRing κ] {r t : ℕ} (g : GL (Fin r) κ) : g ∈ blockTri (blkOf r t) := by
  rw [mem_blockTri]
  intro i j h
  simp [blkOf, i.2, j.2] at h

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {r : ℕ} (hr : r ≤ r) (g : GL (Fin r) κ) : upperLeftBlock hr g = g := by
  have hm : g ∈ blockTri (blk2 r) := by
    rw [mem_blockTri]
    intro i j h
    simp [blk2, i.2, j.2] at h
  ext i j
  rw [upper_block_val_submatrix hr hm]
  rfl

theorem exists_GL_iff {κ : Type} [CommRing κ] {r : ℕ} (M : Matrix (Fin r) (Fin r) κ) :
    (∃ g : GL (Fin r) κ, (g : Matrix (Fin r) (Fin r) κ) = M) ↔ IsUnit M.det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨g, hg⟩⟩

theorem locH_of_mem (Pg : Finset (Pl E)) {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) {PP : Pl E}
    (h : PP ∈ Pg) : locH Pg Hl PP = Hl ⟨PP, h⟩ := dif_pos h

theorem locH_of_not (Pg : Finset (Pl E)) {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) {PP : Pl E}
    (h : PP ∉ Pg) : locH Pg Hl PP = ⊤ := dif_neg h

theorem norm_omegaQ {D : D7} {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    ‖omegaQ Q r ξ k y‖ = if ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then 1 else 0 := by
  unfold omegaQ
  split
  · rename_i h
    simp only [norm_prod, norm_zpow, norm_char_fin, _root_.one_zpow, Finset.prod_const_one]
  · rename_i h
    rw [norm_zero]

theorem norm_omegaG {D : D7} {b r t : ℕ} (hr : r ≤ r) (Pg : Finset (Pl D.host.E))
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* ℂˣ)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin r) (kP PP)) :
    ‖omegaG (Lev.datY r r t 0 hr Pg ∅ (LevelP.ofLocal Hl cl) χ ξ Lev.Frm.B) m y‖ =
      if ∀ PP (h : PP ∈ Pg), LowZero r (y PP) ∧
          ∃ g ∈ Hl ⟨PP, h⟩, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP) then 1 else 0 := by
  by_cases hc : ∀ PP (h : PP ∈ Pg), LowZero r (y PP) ∧
      ∃ g ∈ Hl ⟨PP, h⟩, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP)
  · rw [if_pos hc]
    unfold omegaG
    split
    · simp only [norm_mul, norm_prod, norm_inv, norm_char_fin, Finset.prod_const_one, inv_one, mul_one]
    · rename_i h
      exfalso
      apply h
      refine ⟨fun PP hP => (hc PP hP).1, fun PP => (hc PP.1 PP.2).2.choose,
        fun PP => (hc PP.1 PP.2).2.choose_spec.2, fun PP => mem_blockTri_blkOf _, ?_⟩
      show (fun PP : ↥Pg => upperLeftBlock hr ((hc PP.1 PP.2).2.choose)) ∈ Subgroup.pi Set.univ Hl
      intro PP _
      simp only [restrictedBlock_self_apply]
      exact (hc PP.1 PP.2).2.choose_spec.1
  · rw [if_neg hc]
    unfold omegaG
    split
    · rename_i h
      exfalso
      obtain ⟨hlow, g, hg1, -, hg3⟩ := h
      apply hc
      intro PP hP
      have h3 : (fun PP : ↥Pg => upperLeftBlock hr (g PP)) ∈ Subgroup.pi Set.univ Hl := hg3
      have h4 := h3 ⟨PP, hP⟩ (Set.mem_univ _)
      simp only [restrictedBlock_self_apply] at h4
      exact ⟨hlow PP hP, g ⟨PP, hP⟩, h4, hg1 ⟨PP, hP⟩⟩
    · rw [norm_zero]

theorem norm_omegaG_mul_omegaQ {D : D7} {b a r t : ℕ} (hr : r ≤ a) (har : a = r) (Pg Q : Finset (Pl D.host.E))
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* ℂˣ)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    ‖omegaG (Lev.datY a r t 0 hr Pg ∅ (LevelP.ofLocal Hl cl) (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) m y *
        omegaQ Q a m (-1) y‖ = ∏ PP ∈ Pg ∪ Q, suppInd r (locH Pg Hl PP) (y PP) := by
  subst a
  rw [norm_mul, norm_omegaG, norm_omegaQ, ite_zero_mul_ite_zero, mul_one]
  unfold suppInd
  rw [Finset.prod_ite_zero, Finset.prod_const_one]
  by_cases hc : ∀ PP ∈ Pg ∪ Q, LowZero r (y PP) ∧
      ∃ g ∈ locH Pg Hl PP, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP)
  · rw [if_pos hc, if_pos]
    refine ⟨fun PP hP => ?_, fun PP hP => ?_⟩
    · have h1 := hc PP (Finset.mem_union_left _ hP)
      rwa [locH_of_mem Pg Hl hP] at h1
    · have h1 := hc PP (Finset.mem_union_right _ hP)
      refine ⟨h1.1, ?_⟩
      obtain ⟨g, -, hg⟩ := h1.2
      exact (exists_GL_iff _).1 ⟨g, hg⟩
  · rw [if_neg hc, if_neg]
    rintro ⟨hA, hB⟩
    apply hc
    intro PP hP
    by_cases hg : PP ∈ Pg
    · rw [locH_of_mem Pg Hl hg]
      exact hA PP hg
    · rw [locH_of_not Pg Hl hg]
      have hq : PP ∈ Q := (Finset.mem_union.1 hP).resolve_left hg
      obtain ⟨g, hg'⟩ := (exists_GL_iff _).2 (hB PP hq).2
      exact ⟨(hB PP hq).1, g, Subgroup.mem_top _, hg'⟩

end GlobalTheory.LevelVecNorm.NormFac

namespace GlobalTheory.LevelVecNorm

theorem normFac : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)),
  ‖omegaG (R.datWp i (LevelP.ofLocal Hl cl)) m y * omegaQ (R.Q t) (Wc D i).rank m (-1) y‖ = ∏ PP ∈ R.Pg ∪ R.Q t, GlobalTheory.LevelVecNorm.suppInd D.R.r (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP) (y PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t Hl cl m y
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  exact NormFac.norm_omegaG_mul_omegaQ (le_of_eq hW.symm) hW R.Pg (R.Q t) Hl cl m y

end GlobalTheory.LevelVecNorm
