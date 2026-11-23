import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def LiftIotaFreeC : Prop :=
  ∀ s₁ s₂ : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
    Formalism.L2.SG.DataInst.Elig s₁.toTerm → s₁.toTerm = s₂.toTerm →
      (Y.tO u u').rowOf s₁ = (Y.tO u u').rowOf s₂ → s₁ = s₂

def LiftMassC : Prop :=
  ∀ t : Term D u u' (X.Fu u) (Y.what₂ u), Formalism.L2.SG.DataInst.Elig t →
    ∑' s : {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // s.toTerm = t},
      Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' = 1

def LiftRowCohC : Prop :=
  ∀ (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (t : Term D u u' (X.Fu u) (Y.what₂ u)),
    Formalism.L2.SG.DataInst.Elig s.toTerm → Formalism.L2.SG.DataInst.Elig t → Formalism.L2.SG.Corank.TermScal D s.toTerm t →
      ∃ s' : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
        s'.toTerm = t ∧ (Y.tO u u').rowOf s' = (Y.tO u u').rowOf s

namespace TorsorStructure

variable {X Y u u' κ}

theorem torsor_G_gener (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (h : Formalism.L2.SG.DataInst.Elig s.toTerm) : (Y.tO u u').G s ≠ 0 ∧ (Y.tO u u').gener s := by
  refine ⟨?_, h.1⟩
  unfold Formalism.L2.SG.Full.Full.tO Formalism.L2.SG.TermOp.tOf
  dsimp only
  unfold Formalism.L2.SG.TermOp.Gt
  rw [if_neg (show s.G ≠ 0 from h.2)]
  exact one_ne_zero

theorem torsor_elig {R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR} {ρ : ℕ} (s : LiftT X Y u u' κ R ρ) :
    Formalism.L2.SG.DataInst.Elig s.1.toTerm := by
  have hG := s.2.1
  unfold Formalism.L2.SG.Full.Full.tO Formalism.L2.SG.TermOp.tOf at hG
  dsimp only at hG
  unfold Formalism.L2.SG.TermOp.Gt at hG
  refine ⟨s.2.2.1, fun h0 => hG ?_⟩
  exact if_pos (show s.1.G = 0 from h0)

theorem torsor_lam {R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR} {ρ : ℕ} (s : LiftT X Y u u' κ R ρ) :
    s.1.lam = R.1.1 ∧ s.1.lam' = R.2.1.1 := by
  obtain ⟨-, -, hR, -⟩ := s.2
  have h1 : ((Y.tO u u').rowOf s.1).1.val = R.1.val := congrArg (fun r => r.1.val) hR
  have h2 : ((Y.tO u u').rowOf s.1).2.1.val = R.2.1.val := congrArg (fun r => r.2.1.val) hR
  rw [← h1, ← h2]
  exact ⟨rfl, rfl⟩

def torsor_toCls {R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR} {ρ : ℕ} (s : LiftT X Y u u' κ R ρ) :
    ClassT X Y u u' κ ρ :=
  ⟨s.1.toTerm, torsor_elig s, s.2.2.2.2⟩

end TorsorStructure

open TorsorStructure

theorem torsorC_of (hRL : Formalism.L2.SG.DataInst.RowLabel κ) (hI : LiftIotaFreeC X Y u u')
    (hM : LiftMassC X Y u u') (hC : LiftRowCohC X Y u u') : TorsorC X Y u u' vR i0 i0' νq κ := by
  intro ρ
  have hw' : ∀ Λ, 0 ≤ Formalism.MainNotions.S.wRow D (X.Fu u') Λ := fun Λ => by
    unfold Formalism.MainNotions.S.wRow; positivity
  have hw : ∀ Λ, 0 ≤ Formalism.MainNotions.S.wRow D (X.Fu u) Λ := fun Λ => by
    unfold Formalism.MainNotions.S.wRow; positivity
  have hlift : ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (s0 : LiftT X Y u u' κ R ρ)
      (t : ClassT X Y u u' κ ρ), ∃ s : LiftT X Y u u' κ R ρ, s.1.toTerm = t.1 := by
    intro R s0 t
    have he0 := torsor_elig s0
    have hsc : Formalism.L2.SG.Corank.TermScal D s0.1.toTerm t.1 :=
      (hRL _ _ he0 t.2.1).mp (s0.2.2.2.2.trans t.2.2.symm)
    obtain ⟨s', hs't, hs'r⟩ := hC s0.1 t.1 he0 t.2.1 hsc
    have hel : Formalism.L2.SG.DataInst.Elig s'.toTerm := by rw [hs't]; exact t.2.1
    obtain ⟨hG, hgen⟩ := torsor_G_gener s' hel
    have hk : κ s'.toTerm = ρ := by rw [hs't]; exact t.2.2
    exact ⟨⟨s', hG, hgen, hs'r.trans s0.2.2.2.1, hk⟩, hs't⟩
  let hE : ∀ R, LiftT X Y u u' κ R ρ → (LiftT X Y u u' κ R ρ ≃ ClassT X Y u u' κ ρ) := fun R s0 =>
    Equiv.ofBijective torsor_toCls
      ⟨fun s s' h => Subtype.ext (hI s.1 s'.1 (torsor_elig s) (congrArg Subtype.val h)
          (s.2.2.2.1.trans s'.2.2.2.1.symm)),
        fun t => by
          obtain ⟨s, hs⟩ := hlift R s0 t
          exact ⟨s, Subtype.ext hs⟩⟩
  have hF : ∀ R, liftVal X Y u u' vR i0 i0' νq κ R ρ =
      if Nonempty (LiftT X Y u u' κ R ρ) then
        ((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') R.2.1.1) : ℝ) : ℂ) • clsVec X Y u u' vR i0 i0' νq κ ρ
      else 0 := by
    intro R
    split_ifs with h
    · obtain ⟨s0⟩ := h
      unfold liftVal clsVec
      rw [← tsum_const_smul'', ← (hE R s0).tsum_eq]
      refine tsum_congr fun s => ?_
      rw [smul_smul]
      congr 1
      have hl := (torsor_lam s).2
      have key : (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) s.1.lam * Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam')) : ℝ) : ℂ) *
          Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm =
          ((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') R.2.1.1) : ℝ) : ℂ) *
            ((((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) s.1.lam)) : ℝ) : ℂ) *
              Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm) := by
        rw [Real.sqrt_mul (hw _), hl]; push_cast; ring
      exact key
    · haveI : IsEmpty (LiftT X Y u u' κ R ρ) := not_nonempty_iff.mp h
      unfold liftVal
      exact tsum_empty
  by_cases hcl : Nonempty (ClassT X Y u u' κ ρ)
  · obtain ⟨t0⟩ := hcl
    let g : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR → ℝ := fun R =>
      if Nonempty (LiftT X Y u u' κ R ρ) then Formalism.MainNotions.S.wRow D (X.Fu u') R.2.1.1 else 0
    have hnorm : ∀ R, ‖liftVal X Y u u' vR i0 i0' νq κ R ρ‖ ^ 2 =
        g R * ‖clsVec X Y u u' vR i0 i0' νq κ ρ‖ ^ 2 := by
      intro R
      simp only [g]
      rw [hF R]
      split_ifs with h
      · rw [norm_smul, mul_pow, Complex.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw' _)]
      · simp
    let S : Set (Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) :=
      {R | Nonempty (LiftT X Y u u' κ R ρ)}
    have hlift0 : ∀ s : {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') //
        s.toTerm = t0.1}, LiftT X Y u u' κ ((Y.tO u u').rowOf s.1) ρ := fun s => by
      have hel : Formalism.L2.SG.DataInst.Elig s.1.toTerm := by rw [s.2]; exact t0.2.1
      obtain ⟨hG, hgen⟩ := torsor_G_gener s.1 hel
      have hk : κ s.1.toTerm = ρ := by rw [s.2]; exact t0.2.2
      exact ⟨s.1, hG, hgen, rfl, hk⟩
    let e2 : {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') //
        s.toTerm = t0.1} ≃ S :=
      Equiv.ofBijective (fun s => ⟨(Y.tO u u').rowOf s.1, ⟨hlift0 s⟩⟩)
        ⟨fun s s' h => by
            have hr : (Y.tO u u').rowOf s.1 = (Y.tO u u').rowOf s'.1 := congrArg Subtype.val h
            have hel : Formalism.L2.SG.DataInst.Elig s.1.toTerm := by rw [s.2]; exact t0.2.1
            exact Subtype.ext (hI s.1 s'.1 hel (s.2.trans s'.2.symm) hr),
          fun R => by
            obtain ⟨s1⟩ := R.2
            obtain ⟨s, hs⟩ := hlift R.1 s1 t0
            exact ⟨⟨s.1, hs⟩, Subtype.ext s.2.2.2.1⟩⟩
    have hmass := hM t0.1 t0.2.1
    have hsumg : ∑' R, g R = 1 := by
      have h1 : ∑' R, g R = ∑' x : S, Formalism.MainNotions.S.wRow D (X.Fu u') x.1.2.1.1 := by
        rw [tsum_subtype S (fun R => Formalism.MainNotions.S.wRow D (X.Fu u') R.2.1.1)]
        refine tsum_congr fun R => ?_
        simp only [g, S, Set.indicator_apply, Set.mem_setOf_eq]
      rw [h1, ← e2.tsum_eq]
      exact hmass
    have hg0 : ∀ R, 0 ≤ g R := fun R => by
      simp only [g]; split_ifs
      · exact hw' _
      · exact le_rfl
    have hsum : Summable g := by
      by_contra hns
      rw [tsum_eq_zero_of_not_summable hns] at hsumg
      norm_num at hsumg
    refine ⟨?_, ?_⟩
    · simp_rw [hnorm]
      exact hsum.mul_right _
    · simp_rw [hnorm]
      rw [tsum_mul_right, hsumg, one_mul]
  · haveI : IsEmpty (ClassT X Y u u' κ ρ) := not_nonempty_iff.mp hcl
    have hC0 : clsVec X Y u u' vR i0 i0' νq κ ρ = 0 := by
      unfold clsVec; exact tsum_empty
    have hF0 : ∀ R, liftVal X Y u u' vR i0 i0' νq κ R ρ = 0 := by
      intro R
      rw [hF R, if_neg]
      rintro ⟨s⟩
      exact hcl ⟨torsor_toCls s⟩
    simp [hF0, hC0]

end Formalism.L2.SG.Pf.RowForm
