import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem summable_of_fibre_bound {P T : Type*} (A : P → T → Prop)
    (hA : ∀ p p' t, A p t → A p' t → p = p') (g : T → ℝ) (hg0 : ∀ t, 0 ≤ g t) (hg : Summable g)
    (F : P → ℝ) (hF0 : ∀ p, 0 ≤ F p) (hF : ∀ p, F p ≤ ∑' t : {t // A p t}, g t) : Summable F := by
  refine summable_of_sum_le hF0 (c := ∑' t, g t) (fun S => ?_)
  have hind : ∀ p, ∑' t : {t // A p t}, g t = ∑' t, Set.indicator {t | A p t} g t :=
    fun p => tsum_subtype {t | A p t} g
  calc ∑ p ∈ S, F p ≤ ∑ p ∈ S, ∑' t, Set.indicator {t | A p t} g t :=
        Finset.sum_le_sum fun p _ => (hF p).trans (hind p).le
    _ = ∑' t, ∑ p ∈ S, Set.indicator {t | A p t} g t :=
        (Summable.tsum_finsetSum fun p _ => hg.indicator _).symm
    _ ≤ ∑' t, g t := by
        refine Summable.tsum_le_tsum (fun t => ?_) (summable_sum fun p _ => hg.indicator _) hg
        by_cases h : ∃ p ∈ S, A p t
        · obtain ⟨p, hp, hpt⟩ := h
          rw [Finset.sum_eq_single p]
          · exact (Set.indicator_of_mem (show t ∈ {t | A p t} from hpt) g).le
          · intro q _ hq
            exact Set.indicator_of_notMem (fun hqt => hq (hA q p t hqt hpt)) g
          · intro h
            exact absurd hp h
        · simp only [not_exists, not_and] at h
          exact (Finset.sum_eq_zero fun p hp =>
            Set.indicator_of_notMem (show t ∉ {t | A p t} from h p hp) g).le.trans (hg0 t)

theorem sign_list_injective {K : Type} [Ring K] (r : ℕ) :
    ∀ (b : ℕ) (x y : TB.Pt K), DataInst.signAux r b x = DataInst.signAux r b y → x = y
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => by simp [DataInst.signAux] at h
  | _, _ :: _, [], h => by simp [DataInst.signAux] at h
  | b, (s, t) :: xs, (s', t') :: ys, h => by
    simp only [DataInst.signAux, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, ht⟩, hr⟩ := h
    have hu : IsUnit ((-1 : K) ^ (r + 1 - (b + s - 1))) := isUnit_one.neg.pow _
    rw [hu.mul_left_cancel ht, sign_list_injective r (b + s) xs ys hr]

theorem ptOfList_inj {D : Formalism.BasicNotions.D7} {i : ℕ} {x y : TB.Pt D.host.E} {w : Point D.host.E i}
    (hx : DataInst.ptOfList (D := D) i x = some w) (hy : DataInst.ptOfList (D := D) i y = some w) : x = y := by
  unfold DataInst.ptOfList at hx hy
  by_cases h1 : Formalism.L2.S.IsPtL (DataInst.signPt D.R.rS x) i
  · by_cases h2 : Formalism.L2.S.IsPtL (DataInst.signPt D.R.rS y) i
    · rw [dif_pos h1] at hx
      rw [dif_pos h2] at hy
      have he := (Option.some.inj hx).trans (Option.some.inj hy).symm
      have hv := congrArg Subtype.val ((Formalism.L2.S.ptEquiv D.host.E i).symm.injective he)
      exact sign_list_injective D.R.rS 1 x y hv
    · rw [dif_neg h2] at hy
      exact absurd hy (by simp)
  · rw [dif_neg h1] at hx
    exact absurd hx (by simp)

end Gen

section Inputs

variable {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)

def PtUniq : Prop :=
  ∀ (t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u)) (w w' : Point D.host.E (D.R.rS + 1)), t.atPt w → t.atPt w' → w = w'

def OONormLe (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ (s : TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (w : Point D.host.E (D.R.rS + 1)),
    s.toTerm.generic → s.toTerm.G ≠ 0 → s.toTerm.atPt w →
      |PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) δ M s.toTerm| *
          ‖PackageTie.hsEmb (RealObj.unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq w)‖ ≤
        ‖PackageTie.hsEmb (TermOp.OOt s)‖

def AmpLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ s : TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
    c * ‖PackageTie.hsEmb (TermOp.OOt s)‖ ≤ ‖(Y.tO u u').vec s‖

def WeightBound (nc : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (p : TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)), DataInst.ptOfList (D.R.rS + 1) p = some w →
    (∃ γ, RealObj.IsPtRep X u u' w γ) → (∃ t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 ∧ t.atPt w) →
      Real.sqrt (RealObj.nW X u u' w) ≤
        C * |Real.sqrt (n0 nc (D.mem u).A.T (D.mem u').A.T w) * DataInst.phi (D.R.rS + 1) p|

end Inputs

section Main

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem massTerm_le (t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u)) :
    PairVal.massTerm t ≤ ∑ Λ ∈ Y.what₂ u, |PairVal.massRow D (X.Fu u) (Y.what₂ u) Λ| := by
  exact (le_abs_self _).trans
    (Finset.single_le_sum (f := fun Λ => |PairVal.massRow D (X.Fu u) (Y.what₂ u) Λ|)
      (fun _ _ => abs_nonneg _) t.mem)

end Main

end Formalism.L2.SG.RowsAbsX
