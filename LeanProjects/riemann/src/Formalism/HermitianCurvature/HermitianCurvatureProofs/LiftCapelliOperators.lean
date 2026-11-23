import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliDetAdInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntUv

namespace Formalism.FourierDecayAlt.P.TLB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

open Classical in

def cTerm (c : ℂ) (w : List (B.Mat k r)) : B.DTerm k r Wp Wq where
  coef := fun _ => c • ContinuousLinearMap.id ℂ _
  coefAdj := fun _ => conj c • ContinuousLinearMap.id ℂ _
  word := if ∀ X ∈ w, B.inLie k r X then w else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := by
    intro x A B'
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
    rw [Formalism.FourierDecayAlt.P5.HerB.hs_smul_left, Formalism.FourierDecayAlt.P5.HerB.hs_smul_right, Complex.conj_conj]

theorem cTerm_word {c : ℂ} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) :
    (cTerm (Wp := Wp) (Wq := Wq) c w).word = w := by
  unfold cTerm
  dsimp only
  rw [if_pos hw]

theorem cTerm_word_le (c : ℂ) (w : List (B.Mat k r)) :
    (cTerm (Wp := Wp) (Wq := Wq) c w).word.length ≤ w.length := by
  unfold cTerm
  dsimp only
  split_ifs <;> simp

theorem cTerm_apply (c : ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    (cTerm (Wp := Wp) (Wq := Wq) c w).coef g (B.Rw (cTerm (Wp := Wp) (Wq := Wq) c w).word F g) = c • B.Rw w F g := by
  rw [cTerm_word hw]
  simp [cTerm]

theorem opOrder_le_of (Θ : B.DiffOp k r Wp Wq) (n : ℕ) (h : ∀ T ∈ Θ, T.word.length ≤ n) : B.opOrder Θ ≤ n := by
  induction Θ with
  | nil => simp [B.opOrder]
  | cons T Θ ih =>
    simp only [B.opOrder, List.map_cons, List.foldr_cons] at ih ⊢
    exact max_le (h T List.mem_cons_self) (ih fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))

theorem opOrder_cons_eq (T : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq)
    (h : ∀ T' ∈ Θ, T'.word.length ≤ T.word.length) : B.opOrder (T :: Θ) = T.word.length := by
  have h2 := opOrder_le_of Θ _ h
  simp only [B.opOrder, List.map_cons, List.foldr_cons] at h2 ⊢
  exact max_eq_left h2

def capOp (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (s : ℂ)
    (Lw : List (ℂ × List (B.Mat k r))) : B.DiffOp k r Wp Wq :=
  cTerm 0 (List.replicate (2 * r + k + 1) 0) :: Lw.map fun cw => cTerm (s * cw.1) cw.2

theorem zero_lie : B.inLie k r (0 : B.Mat k r) := by
  simp [B.inLie]

theorem opApply_capOp_tail (s : ℂ) (Lw : List (ℂ × List (B.Mat k r)))
    (hL : ∀ cw ∈ Lw, ∀ X ∈ cw.2, B.inLie k r X) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (Lw.map fun cw => (cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2)) F g =
      s • (Lw.map fun cw => cw.1 • B.Rw cw.2 F g).sum := by
  induction Lw with
  | nil => simp [B.opApply]
  | cons cw Lw ih =>
    have ih' := ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h)
    simp only [B.opApply, List.map_cons, List.sum_cons, List.map_map] at ih' ⊢
    rw [smul_add, ← ih']
    congr 1
    rw [cTerm_apply _ _ (hL cw List.mem_cons_self), mul_smul]

theorem opApply_capOp (s : ℂ) (Lw : List (ℂ × List (B.Mat k r)))
    (hL : ∀ cw ∈ Lw, ∀ X ∈ cw.2, B.inLie k r X) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (capOp k r Wp Wq s Lw) F g = s • (Lw.map fun cw => cw.1 • B.Rw cw.2 F g).sum := by
  have e : B.opApply (capOp k r Wp Wq s Lw) F g =
      (cTerm (Wp := Wp) (Wq := Wq) 0 (List.replicate (2 * r + k + 1) 0)).coef g
        (B.Rw (cTerm (Wp := Wp) (Wq := Wq) 0 (List.replicate (2 * r + k + 1) 0)).word F g) +
      B.opApply (Lw.map fun cw => (cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2)) F g := by
    simp [B.opApply, capOp]
  rw [e, opApply_capOp_tail s Lw hL F g]
  simp [cTerm]

theorem opOrder_capOp (s : ℂ) (Lw : List (ℂ × List (B.Mat k r)))
    (hL : ∀ cw ∈ Lw, cw.2.length ≤ 2 * r + k + 1) :
    B.opOrder (capOp k r Wp Wq s Lw) = 2 * r + k + 1 := by
  have hw : (cTerm (Wp := Wp) (Wq := Wq) 0 (List.replicate (2 * r + k + 1) (0 : B.Mat k r))).word =
      List.replicate (2 * r + k + 1) 0 :=
    cTerm_word fun X hX => by rw [List.eq_of_mem_replicate hX]; exact zero_lie
  unfold capOp
  rw [opOrder_cons_eq, hw, List.length_replicate]
  intro T hT
  rw [hw, List.length_replicate]
  obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
  exact (cTerm_word_le _ _).trans (hL cw hcw)

theorem cTerm_inDDPlus (D : B.RealPlaceData k r Wp Wq) (c : ℂ) (w : List (B.Mat k r)) (o : ℕ) (hw : w.length ≤ o)
    (T : B.DTerm k r Wp Wq) (hT : T = cTerm c w) :
    (B.CkOn ⊤ (C6.domL D ∅) T.coef ∧ B.CkOn ⊤ (C6.domL D ∅) T.coefAdj) ∧
    ∃ (P : B.Mat k r → ℂ) (a b : Fin (r + 2) → ℕ) (cc : ℕ) (es : List (Fin 0 × List (B.Mat k r))),
      U.IsPolyDeg 0 P ∧ (∀ l, l ∉ (∅ : Finset (Fin (r + 2))) → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) ∧
      T.word.length + (es.map fun e => e.2.length).sum ≤ o ∧ (∀ e ∈ es, ∀ X ∈ e.2, B.inLie k r X) ∧
      ∀ g ∈ C6.domL D ∅, T.coef g = (P g * C6.monoM D a b cc g) • C6.Epart (fun j : Fin 0 => j.elim0) es g := by
  subst hT
  refine ⟨⟨fun g₀ _ => ⟨Set.univ, fun _ => c • ContinuousLinearMap.id ℂ _, isOpen_univ, trivial, contDiffOn_const,
      fun _ _ _ => rfl⟩, fun g₀ _ => ⟨Set.univ, fun _ => conj c • ContinuousLinearMap.id ℂ _, isOpen_univ, trivial,
      contDiffOn_const, fun _ _ _ => rfl⟩⟩, fun _ => c, fun _ => 0, fun _ => 0, 0, [], ?_, ?_, ?_, by simp, ?_⟩
  · exact ⟨MvPolynomial.C c, by simp, fun g => by simp⟩
  · intro l _ _; exact ⟨rfl, rfl⟩
  · simpa using (cTerm_word_le (Wp := Wp) (Wq := Wq) c w).trans hw
  · intro g _
    simp [C6.monoM, C6.Epart, cTerm]
    rfl

end terms

end

end Formalism.FourierDecayAlt.P.TLB

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

theorem lift_capelli_operators : TL.LiftCap := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hD Y
  obtain ⟨Lw, hLw, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum P.k P.r Y
  set s : ℂ := M.sgn P l0 with hs
  have hLie : ∀ cw ∈ Lw, ∀ X ∈ cw.2, B.inLie P.k P.r X := fun cw h X hX => ((hLw cw h).1 X hX).1
  have hlen : ∀ cw ∈ Lw, cw.2.length ≤ 2 * P.r + P.k + 1 := fun cw h => (hLw cw h).2
  set Dop := TLB.capOp P.k P.r Wp Wq s Lw with hDop
  have hApp : ∀ f : B.Mat P.k P.r → (Wq →L[ℂ] Wp), B.CkOn ((2 * P.r + P.k + 1 : ℕ) : ℕ∞) (B.GV P.k P.r) f →
      ∀ g ∈ B.GV P.k P.r, B.opApply Dop f g = s • Q.CV P.k P.r Y f g := by
    intro f hf g hg
    rw [hDop, TLB.opApply_capOp s Lw hLie, hCV _ _ f hf g hg hg]
  refine ⟨0, fun j => j.elim0, Dop, fun j => j.elim0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (TLB.cTerm_inDDPlus Bs 0 _ _ (le_of_eq (List.length_replicate ..)) _ rfl).1
    · obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
      exact (TLB.cTerm_inDDPlus Bs _ _ _ (hlen cw hcw) _ rfl).1
  · intro p hp f hf g hg
    rw [hDop, TLB.opOrder_capOp s Lw hlen] at hf
    have hgG : g ∈ B.GV P.k P.r := hg.1
    have hs' := Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hgG
    rw [hApp _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho Bs hp hf) g hgG,
      Formalism.FourierDecayAlt.P.capelli_rho_commute P.k P.r Wp Wq Bs Y f p hp hf g hgG]
    simp only [B.rho]
    rw [hApp f hf _ hs', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (TLB.cTerm_inDDPlus Bs 0 _ _ (le_of_eq (List.length_replicate ..)) _ rfl).2
    · obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
      exact (TLB.cTerm_inDDPlus Bs _ _ _ (hlen cw hcw) _ rfl).2
  · intro F hF Φ hΦ y hy
    obtain ⟨ε, hε, hN⟩ := (compact_support_facts P.k P.r Wp Wq Bs F hF).1
    have hz := Bs.z_mem
    have hz' := Bs.z'_mem
    have hL := hD.2.2.1
    have hst := hD.2.2.2.1
    have hJ := Formalism.FourierDecayAlt.P.bessel_function_finite_class P.k P.r Wp Wq Bs F ε hε hN
    have hGV : wCell P.k P.r (Fin.last P.r) y.1 * y.2 ∈ B.GV P.k P.r := by
      rw [P5.Rad.wCell_last_eq]
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
    have hh : wCell P.k P.r (Fin.last P.r) y.1 * y.2 ∈ JF.Om P.k P.r Bs.z Bs.z' :=
      ⟨hGV, P5.Rad.wCell_mem_omPlus hz hz' hy.1 hy.2.1 hy.2.2⟩
    have h1 := JCx2.rma_QQi X L hL st s hst Y 0 0 Φ hy
    have h2 := (JCx2.rma_sandw X L hL Y P.r le_rfl _ _ (JCx2.rma_base X Y) (JCx2.rma_QL_loc Y)).2 0 0
      (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (resG P.k P.r (Fin.last P.r) (B.JF Bs F)) (fun y' hy' => hΦ y' hy') y hy
    have h3 := Formalism.FourierDecayAlt.P.chain_recursion_all_levels Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) _ Y 0 0 hz hz'
      (JCx2.rma_isDom_omPlus hz hz') _ hJ y.1 hy.1 y.2 hy.2.1 hh.2
    rw [Fin.val_last] at h3
    have h4 := (JCx2.bcGood_tL (Bs := Bs) (ε := ε) s Y 0 0).2.1 F hN _ hh
    have h5 := Formalism.FourierDecayAlt.P.Qx8.JF_congr Bs (F := fun g => s • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 F g)
      (F' := B.opApply Dop F) (a := 1) (fun g hg => by
        rw [one_smul, hApp F (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF.1) g hg]; rfl) hGV
    refine Eq.trans h1 ?_
    rw [h2, ← h3]
    simp only [Q.resG]
    have h4' : B.JF Bs (fun g => s • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 F g) (wCell P.k P.r (Fin.last P.r) y.1 * y.2) =
        s • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 (B.JF Bs F) (wCell P.k P.r (Fin.last P.r) y.1 * y.2) := h4
    rw [h5, one_smul, h4', smul_comm]

end

end Formalism.FourierDecayAlt.P
