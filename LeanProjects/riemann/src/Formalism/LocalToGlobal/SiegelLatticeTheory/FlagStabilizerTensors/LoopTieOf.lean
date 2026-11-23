import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LoopsCut

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.LoopTieOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pins

variable {D : D7} {X : HidaSetting D}

def ampL {Y : Full X} {u u' : D.what₂.Word} (s : TT Y u u') : ℝ :=
  ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s)‖

def rowL {Y : Full X} {u u' : D.what₂.Word} (s : TT Y u u') :=
  Formalism.L2.SG.TermOp.rowOf Y.TR (Y.cs u) (Y.cs u') s

variable (Y : Full X)

def AmpFibreConst : Prop :=
  ∀ (u u' : D.what₂.Word) (t : RT Y u u') (s s' : fib Y t), ampL s.1 = ampL s'.1

def FibreCount : Prop :=
  ∀ (u u' : D.what₂.Word) (t₁ t₂ : RT Y u u') (S : Finset (TT Y u u' × TT Y u u')),
    (∀ x ∈ S, x.1.toTerm = t₁ ∧ x.2.toTerm = t₂ ∧ rowL x.1 = rowL x.2) →
      ∑ x ∈ S, wRow D (X.Fu u') x.1.lam' ≤ 1

def GamPin : Prop := ∀ u u' : D.what₂.Word, (Y.tO u u').Gam1 = gaG D

variable {Y} (hF : FinX Y) (hI : SIso D.s (sOf hF))

def JtPin (T : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = hI.eT u u' t →
    hsNormSq (T.Jt t) = ampL s ^ 2

def WRowPin (T : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (p : D.s.Pair u u') (s : TT Y u u'), s.toTerm = hI.eT u u' (D.s.pfst p) →
    T.wRow p = wRow D (X.Fu u) s.lam

end Pins

section Cmp

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} {hI : SIso D.s (sOf hF)}

def pairOf {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) : RP Y u u' :=
  ⟨(x.1.toTerm, x.2.toTerm), ⟨x.1, rfl⟩, ⟨x.2, rfl⟩, h⟩

theorem wRow_nonneg' {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    0 ≤ wRow D F0 Λ := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem lam_eq_of_row {u u' : D.what₂.Word} {s₁ s₂ : TT Y u u'} (h : rowL s₁ = rowL s₂) :
    s₁.lam = s₂.lam ∧ s₁.lam' = s₂.lam' := by
  unfold rowL Formalism.L2.SG.TermOp.rowOf at h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact ⟨h.1, h.2.1⟩

private theorem norm_tO_vec_eq_wt_mul_ampL {u u' : D.what₂.Word} (s : TT Y u u') :
    ‖(Y.tO u u').vec s‖ = Formalism.L2.SG.TermOp.wt s * ampL s := by
  classical
  have key : ∀ i, (Y.tO u u').vec s i = if i = (⟨s.lam, s.mem⟩, ⟨s.lam', s.mem'⟩) then
      ((Formalism.L2.SG.TermOp.wt s : ℝ) : ℂ) • Formalism.L2.SG.PackageTie.hsEmb
        (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) else 0 := fun i => rfl
  have hwt : 0 ≤ Formalism.L2.SG.TermOp.wt s := Real.sqrt_nonneg _
  rw [PiLp.norm_eq_of_L2, Finset.sum_eq_single (⟨s.lam, s.mem⟩, ⟨s.lam', s.mem'⟩)]
  · rw [key, if_pos rfl, Real.sqrt_sq (norm_nonneg _), norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hwt]
    rfl
  · intro b _ hb
    rw [key, if_neg hb, norm_zero]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fibre_le (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y)
    {u u' : D.what₂.Word} (p : D.s.Pair u u') (S : Finset (TT Y u u' × TT Y u u'))
    (hS : ∀ x ∈ S, ∃ h : rowL x.1 = rowL x.2, hI.eP u u' p = pairOf x h) :
    ∑ x ∈ S, ‖(Y.tO u u').vec x.1‖ * ‖(Y.tO u u').vec x.2‖ ≤ Formalism.MainNotions.BridgeLemma.wP T p := by
  classical
  have hq1 : ((hI.eP u u' p).l1).toTerm = hI.eT u u' (D.s.pfst p) := by
    rw [hI.pfst]
    exact (hI.eP u u' p).2.choose.2
  have hw0 : 0 ≤ T.wRow p := by
    rw [hW u u' p _ hq1]
    exact wRow_nonneg' _ _
  have hwP : 0 ≤ Formalism.MainNotions.BridgeLemma.wP T p :=
    mul_nonneg hw0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have ee : ∀ x ∈ S, x.1.toTerm = hI.eT u u' (D.s.pfst p) ∧ x.2.toTerm = hI.eT u u' (D.s.psnd p) ∧
      rowL x.1 = rowL x.2 := by
    intro x hx
    obtain ⟨h, hp⟩ := hS x hx
    refine ⟨?_, ?_, h⟩
    · rw [hI.pfst, hp]
      rfl
    · rw [hI.psnd, hp]
      rfl
  have key : ∀ x ∈ S, ‖(Y.tO u u').vec x.1‖ * ‖(Y.tO u u').vec x.2‖ =
      Formalism.MainNotions.BridgeLemma.wP T p * wRow D (X.Fu u') x.1.lam' := by
    intro x hx
    obtain ⟨e1, e2, h⟩ := ee x hx
    have a1 : Formalism.MainNotions.BridgeLemma.aT T (D.s.pfst p) = ampL x.1 := by
      unfold Formalism.MainNotions.BridgeLemma.aT
      rw [hJ u u' _ x.1 e1]
      exact Real.sqrt_sq (norm_nonneg _)
    have a2 : Formalism.MainNotions.BridgeLemma.aT T (D.s.psnd p) = ampL x.2 := by
      unfold Formalism.MainNotions.BridgeLemma.aT
      rw [hJ u u' _ x.2 e2]
      exact Real.sqrt_sq (norm_nonneg _)
    obtain ⟨hl, hl'⟩ := lam_eq_of_row h
    rw [norm_tO_vec_eq_wt_mul_ampL, norm_tO_vec_eq_wt_mul_ampL, Formalism.MainNotions.BridgeLemma.wP, a1, a2, hW u u' p x.1 e1]
    have hw2 : Formalism.L2.SG.TermOp.wt x.2 = Formalism.L2.SG.TermOp.wt x.1 := by
      unfold Formalism.L2.SG.TermOp.wt
      rw [hl, hl']
    have hs : Formalism.L2.SG.TermOp.wt x.1 * Formalism.L2.SG.TermOp.wt x.1 =
        wRow D (X.Fu u) x.1.lam * wRow D (X.Fu u') x.1.lam' :=
      Real.mul_self_sqrt (mul_nonneg (wRow_nonneg' (X.Fu u) x.1.lam) (wRow_nonneg' (X.Fu u') x.1.lam'))
    rw [hw2]
    linear_combination (ampL x.1 * ampL x.2) * hs
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  calc Formalism.MainNotions.BridgeLemma.wP T p * ∑ x ∈ S, wRow D (X.Fu u') x.1.lam'
      ≤ Formalism.MainNotions.BridgeLemma.wP T p * 1 :=
        mul_le_mul_of_nonneg_left (hC u u' (hI.eT u u' (D.s.pfst p)) (hI.eT u u' (D.s.psnd p)) S ee) hwP
    _ = Formalism.MainNotions.BridgeLemma.wP T p := mul_one _

def recP {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) : D.s.Pair u u' :=
  (hI.eP u u').symm (pairOf x h)

theorem eP_recP {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) :
    hI.eP u u' (recP (hI := hI) x h) = pairOf x h := by
  exact (hI.eP u u').apply_symm_apply _

theorem finSum_le (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y)
    {u u' : D.what₂.Word} (S : Finset (TT Y u u' × TT Y u u')) (hS : ∀ x ∈ S, rowL x.1 = rowL x.2) :
    ∑ x ∈ S, ‖(Y.tO u u').vec x.1‖ * ‖(Y.tO u u').vec x.2‖ ≤
      ∑ p ∈ S.attach.image (fun x => recP (hI := hI) x.1 (hS x.1 x.2)), Formalism.MainNotions.BridgeLemma.wP T p := by
  classical
  have hmap : ∀ x ∈ S.attach, (fun x : {x // x ∈ S} => recP (hI := hI) x.1 (hS x.1 x.2)) x ∈
      S.attach.image (fun x => recP (hI := hI) x.1 (hS x.1 x.2)) := fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_attach S, ← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_le_sum fun p _ => ?_
  have hS' : ∀ x ∈ (S.attach.filter (fun y => recP (hI := hI) y.1 (hS y.1 y.2) = p)).map
      (Function.Embedding.subtype _), ∃ h : rowL x.1 = rowL x.2, hI.eP u u' p = pairOf x h := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    refine ⟨hS y.1 y.2, ?_⟩
    rw [← (Finset.mem_filter.1 hy).2]
    exact eP_recP _ _
  have := fibre_le T hJ hW hC p _ hS'
  rwa [Finset.sum_map] at this

end Cmp

section Classes

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} {hI : SIso D.s (sOf hF)}

open Formalism.MainNotions.BridgeLemma in

theorem ampSum_le_of_rows (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y)
    {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1) (Q : D.s.Pair u u' → Prop) (B : ℝ)
    (hB : RowBound T L Q B) (Q' : Set (TT Y u u' × TT Y u u'))
    (hQ : ∀ x ∈ Q', ∃ h : rowL x.1 = rowL x.2, Q (recP (hI := hI) x h)) :
    Formalism.L2.SG.RowsOther.ampSum (Y.tO u u') Q' ≤ massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u * B := by
  classical
  unfold Formalism.L2.SG.RowsOther.ampSum
  refine Real.tsum_le_of_sum_le (fun p => ?_) (fun s => ?_)
  · exact Set.indicator_nonneg (fun p _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) p
  · have hS : ∀ x ∈ s.filter (· ∈ Q'), rowL x.1 = rowL x.2 := fun x hx => (hQ x (Finset.mem_filter.1 hx).2).choose
    refine le_trans (le_of_eq ?_) (le_trans (finSum_le T hJ hW hC _ hS) (hB _ ?_))
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i ∈ Q' <;> simp [hi]
    · intro p hp
      obtain ⟨⟨x, hx⟩, -, rfl⟩ := Finset.mem_image.1 hp
      exact (hQ x (Finset.mem_filter.1 hx).2).choose_spec

open Formalism.MainNotions.BridgeLemma in

theorem rowBound_or (T : TermTie D) {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1)
    {Q₁ Q₂ : D.s.Pair u u' → Prop} {B₁ B₂ : ℝ} (h₁ : RowBound T L Q₁ B₁) (h₂ : RowBound T L Q₂ B₂) :
    RowBound T L (fun p => Q₁ p ∨ Q₂ p) (B₁ + B₂) := by
  intro S hS
  classical
  rw [← Finset.sum_filter_add_sum_filter_not S Q₁, mul_add]
  refine add_le_add (h₁ _ fun p hp => (Finset.mem_filter.1 hp).2) (h₂ _ fun p hp => ?_)
  obtain ⟨hpS, hn⟩ := Finset.mem_filter.1 hp
  exact (hS p hpS).resolve_left hn

theorem pfst_recP {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) :
    hI.eT u u' (D.s.pfst (recP (hI := hI) x h)) = x.1.toTerm := by
  rw [hI.pfst, eP_recP]
  rfl

theorem psnd_recP {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) :
    hI.eT u u' (D.s.psnd (recP (hI := hI) x h)) = x.2.toTerm := by
  rw [hI.psnd, eP_recP]
  rfl

theorem gterm_ne {u u' : D.what₂.Word} (t : D.s.Term u u') (s : TT Y u u') (e : hI.eT u u' t = s.toTerm)
    (hs : s.G ≠ 0) : D.s.Gterm t ≠ 0 := by
  rw [hI.Gterm, e]
  intro h0
  apply hs
  have := congrArg Subtype.val h0
  exact this

theorem generic_of {u u' : D.what₂.Word} (t : D.s.Term u u') (s : TT Y u u') (e : hI.eT u u' t = s.toTerm)
    (hs : s.generic) : D.s.generic t := by
  rw [hI.generic, e]
  exact hs

theorem corank_of_pair {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) :
    D.s.s0 (recP (hI := hI) x h) = Formalism.L2.SG.TermOp.s0T x.1 x.2 := by
  rw [hI.s0, eP_recP]
  exact (hF.pairIndep u u' _ _ x.1 x.2 (pairOf x h).2.choose.2 (pairOf x h).2.choose_spec.choose.2
    (pairOf x h).2.choose_spec.choose_spec h).1

theorem scal_recP {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) :
    D.s.scalarPair (recP (hI := hI) x h) ↔ liftScalar x.1 x.2 := by
  rw [hI.scalarPair, eP_recP]
  exact (hF.pairIndep u u' _ _ x.1 x.2 (pairOf x h).2.choose.2 (pairOf x h).2.choose_spec.choose.2
    (pairOf x h).2.choose_spec.choose_spec h).2

theorem G_ne_of_Gt {u u' : D.what₂.Word} (s : TT Y u u') (h : (Y.tO u u').G s ≠ 0) : s.G ≠ 0 := by
  intro h0
  apply h
  show (if s.G = 0 then (0 : ℝ) else 1) = 0
  rw [if_pos h0]

theorem bigS_cls (T : TermTie D) {u u' : D.what₂.Word} (s : ℕ) :
    ∀ x ∈ LoopsCut.bigS (Y.tO u u') s, ∃ h : rowL x.1 = rowL x.2,
      (fun p => Formalism.MainNotions.BridgeLemma.clsND T s p ∨ Formalism.MainNotions.BridgeLemma.clsDeg T s p) (recP (hI := hI) x h) := by
  intro x hx
  obtain ⟨⟨h1, h2, h⟩, hs⟩ := hx
  refine ⟨h, ?_⟩
  have g1 := gterm_ne (hI := hI) _ x.1 (pfst_recP x h) (G_ne_of_Gt x.1 h1)
  have g2 := gterm_ne (hI := hI) _ x.2 (psnd_recP x h) (G_ne_of_Gt x.2 h2)
  have e0 : D.s.s0 (recP (hI := hI) x h) = s := (corank_of_pair x h).trans hs
  by_cases hn : Formalism.MainNotions.BridgeLemma.ndP T (recP (hI := hI) x h)
  · exact Or.inl ⟨g1, g2, e0, hn⟩
  · exact Or.inr ⟨g1, g2, e0, hn⟩

theorem nsc_cls {u u' : D.what₂.Word} :
    ∀ x ∈ (Y.tO u u').nsc (Y.tO u u').genSet, ∃ h : rowL x.1 = rowL x.2,
      Formalism.MainNotions.BridgeLemma.clsOne (recP (hI := hI) x h) := by
  intro x hx
  obtain ⟨⟨h1, h2, h⟩, hs, hns⟩ := hx
  refine ⟨h, gterm_ne (hI := hI) _ x.1 (pfst_recP x h) (G_ne_of_Gt x.1 h1.1),
    gterm_ne (hI := hI) _ x.2 (psnd_recP x h) (G_ne_of_Gt x.2 h2.1),
    generic_of (hI := hI) _ x.1 (pfst_recP x h) h1.2, generic_of (hI := hI) _ x.2 (psnd_recP x h) h2.2,
    (corank_of_pair x h).trans hs, ?_⟩
  intro hc
  apply hns
  have hsc := (scal_recP x h).1 hc
  have hl := lam_eq_of_row h
  show Formalism.L2.SG.TermOp.scalT x.1 x.2
  unfold Formalism.L2.SG.TermOp.scalT
  have hs' : Formalism.L2.SG.TermOp.s0T x.1 x.2 = 1 := hs
  unfold Formalism.L2.SG.TermOp.s0T at hs'
  rw [if_pos hl] at hs'
  exact ⟨hl, hs', hsc⟩

theorem classS_le (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y)
    {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1) (C : ℝ)
    (hn : Formalism.MainNotions.BridgeLemma.RowsND T L C) (hd : Formalism.MainNotions.BridgeLemma.RowsDeg T L C) (s : ℕ) (h2 : 2 ≤ s) (hk : s ≤ D.R.k) :
    Formalism.L2.SG.RowsOther.ampSum (Y.tO u u') (LoopsCut.bigS (Y.tO u u') s) ≤
      massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u *
        (LatticeSumBounds.ndRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) *
                         Formalism.MainNotions.BridgeLemma.rDD D u' +
          LatticeSumBounds.degRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C)) := by
  exact ampSum_le_of_rows T hJ hW hC L _ _ (rowBound_or T L (hn s h2 hk) (hd s h2 hk)) _ (bigS_cls T s)

theorem classOne_le (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y)
    {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1) (C : ℝ)
    (h1 : Formalism.MainNotions.BridgeLemma.RowsOne T L C) :
    Formalism.L2.SG.RowsOther.ampSum (Y.tO u u') ((Y.tO u u').nsc (Y.tO u u').genSet) ≤
      massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u * (Formalism.MainNotions.BridgeLemma.oneB D large₂ C * Formalism.MainNotions.BridgeLemma.rDD D u') := by
  exact ampSum_le_of_rows T hJ hW hC L _ _ h1 _ nsc_cls

end Classes

section Cut

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} {hI : SIso D.s (sOf hF)}

theorem gam_mul_le (hG : GamPin Y) {large₂ : SizeData₂ D} {T : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ}
    (L : LoopTie D large₂ T u u' C1) (hFo : UnitaryVolumeMass.FormAt D u) {a B : ℝ}
    (h : a ≤ massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u * B) :
    (Y.tO u u').Gam1 * a ≤ (D.duS u : ℝ) * B := by
  rw [hG u u', ← hFo L.F0 L.flag_e_eq_hyperbolic L.formsAtZero L.what₂ L.isRows]
  calc gaG D * a ≤ gaG D * (massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u * B) :=
        mul_le_mul_of_nonneg_left h (Formalism.MainNotions.BridgeLemma.gaG_nonneg D)
    _ = gaG D * massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u * B := by ring

theorem ddC_eq (hCT : Formalism.L2.SG.RowsConc.ConcTie X Y) (u u' : D.what₂.Word) :
    Formalism.L2.SG.RowsConc.ddC X Y u u' = (D.duS u : ℝ) * Formalism.MainNotions.BridgeLemma.rDD D u' := by
  obtain ⟨-, -, h3, h4, -⟩ := hCT
  unfold Formalism.L2.SG.RowsConc.ddC Formalism.MainNotions.BridgeLemma.rDD
  rw [h3, h3, h4]
  ring

theorem window {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C' Cl Cg cb Cw cT CT C0 A : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A) :
    1 ≤ C0 ∧ 1 ≤ C0 * Formalism.MainNotions.BridgeLemma.rDD D u' * GamS D large₂ ^ 2 := by
  unfold Cnt.Hyp Cnt.Hyp0 at hH
  obtain ⟨⟨-, hD, hC0⟩, -⟩ := hH
  refine ⟨hC0, ?_⟩
  unfold StandingNumericalData at hD
  have hw := (hD.2.2.2.2.2.2.2.2.2.1 u').1
  rw [Formalism.MainNotions.BridgeLemma.d_GamP_eq (D := D) (large₂ := large₂) u'] at hw
  have hDs : 0 < D.what₂.Dstar := Formalism.MainNotions.BridgeLemma.Dstar_pos D
  have hG : 0 < GamS D large₂ := Real.exp_pos _
  have hC0p : 0 < C0 := by linarith
  rw [zpow_neg, zpow_ofNat, div_le_iff₀ hC0p] at hw
  unfold Formalism.MainNotions.BridgeLemma.rDD
  rw [show C0 * ((D.duS u' : ℝ) / D.what₂.Dstar) * GamS D large₂ ^ 2 =
      ((D.duS u' : ℝ) * C0 * GamS D large₂ ^ 2) / D.what₂.Dstar by ring, le_div_iff₀ hDs, one_mul]
  have h2 : D.what₂.Dstar = (GamS D large₂ ^ 2)⁻¹ * D.what₂.Dstar * GamS D large₂ ^ 2 := by field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)

theorem rowsSC_at (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y) (hG : GamPin Y)
    {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1) (hFo : UnitaryVolumeMass.FormAt D u)
    (hCT : Formalism.L2.SG.RowsConc.ConcTie X Y) {C' Cl Cg cb Cw cT CT C0 A : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A) (C : ℝ)
    (hn : Formalism.MainNotions.BridgeLemma.RowsND T L C) (hd : Formalism.MainNotions.BridgeLemma.RowsDeg T L C) (s : ℕ) (h2 : 2 ≤ s) (hk : s ≤ D.R.k)
    (hnd0 : 0 ≤ LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
      (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C))
    (hdg0 : 0 ≤ LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
      (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C)) :
    LoopsCut.ClassLe (Y.tO u u') (LoopsCut.bigS (Y.tO u u') s)
      (max 1 C0 * LoopsCut.rowS C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
        (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) * Formalism.L2.SG.RowsConc.ddC X Y u u') := by
  have hwin := window hH
  have hw := hwin.2
  have hH' := hH
  unfold Cnt.Hyp Cnt.Hyp0 at hH'
  obtain ⟨⟨-, hD, -⟩, -⟩ := hH'
  unfold StandingNumericalData at hD
  have hwu := (hD.2.2.2.2.2.2.2.2.2.1 u).1
  rw [Formalism.MainNotions.BridgeLemma.d_GamP_eq (D := D) (large₂ := large₂) u] at hwu
  have hDs : 0 < D.what₂.Dstar := Formalism.MainNotions.BridgeLemma.Dstar_pos D
  have hGs : 0 < GamS D large₂ := Real.exp_pos _
  have hC0p : 0 < C0 := by linarith [hwin.1]
  have hdu0 : 0 ≤ (D.duS u : ℝ) := le_trans (div_pos (mul_pos (zpow_pos hGs _) hDs) hC0p).le hwu
  have hR : 0 ≤ Formalism.MainNotions.BridgeLemma.rDD D u' := by
    by_contra hneg
    push_neg at hneg
    have : C0 * Formalism.MainNotions.BridgeLemma.rDD D u' * GamS D large₂ ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hC0p hneg) (pow_pos hGs 2)
    linarith
  have hgg : gg D = (X.B.g : ℝ) := by
    rw [X.g_eq]
    push_cast
    rfl
  have hcl := gam_mul_le hG L hFo (classS_le T hJ hW hC L C hn hd s h2 hk)
  rw [Formalism.MainNotions.BridgeLemma.d_m_eq (D := D), hgg] at hcl
  unfold LoopsCut.ClassLe
  rw [ddC_eq hCT]
  unfold LoopsCut.rowS
  set N := LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) with hN
  set E := LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) with hE
  have hM1 : 1 ≤ max 1 C0 := le_max_left _ _
  have hMC : C0 ≤ max 1 C0 := le_max_right _ _
  have e1 : (D.duS u : ℝ) * N * Formalism.MainNotions.BridgeLemma.rDD D u' ≤
      max 1 C0 * ((D.duS u : ℝ) * N * Formalism.MainNotions.BridgeLemma.rDD D u') :=
    le_mul_of_one_le_left (mul_nonneg (mul_nonneg hdu0 hnd0) hR) hM1
  have e2 : (D.duS u : ℝ) * E ≤ (max 1 C0 * Formalism.MainNotions.BridgeLemma.rDD D u' * GamS D large₂ ^ 2) * ((D.duS u : ℝ) * E) :=
    le_mul_of_one_le_left (mul_nonneg hdu0 hdg0)
      (le_trans hw (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMC hR) (sq_nonneg _)))
  have e3 : max 1 C0 * (N + GamS D large₂ ^ 2 * E) * ((D.duS u : ℝ) * Formalism.MainNotions.BridgeLemma.rDD D u') =
      max 1 C0 * ((D.duS u : ℝ) * N * Formalism.MainNotions.BridgeLemma.rDD D u') +
        (max 1 C0 * Formalism.MainNotions.BridgeLemma.rDD D u' * GamS D large₂ ^ 2) * ((D.duS u : ℝ) * E) := by ring
  have e4 : (D.duS u : ℝ) * (N * Formalism.MainNotions.BridgeLemma.rDD D u' + E) =
      (D.duS u : ℝ) * N * Formalism.MainNotions.BridgeLemma.rDD D u' + (D.duS u : ℝ) * E := by ring
  rw [e3]
  linarith

theorem oneB_eq {large₂ : SizeData₂ D} (C : ℝ) :
    Formalism.MainNotions.BridgeLemma.oneB D large₂ C = LoopsCut.oneT C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (GamS D large₂) := by
  have hg : gg D = (X.B.g : ℝ) := by
    rw [X.g_eq]
    push_cast
    rfl
  unfold Formalism.MainNotions.BridgeLemma.oneB LoopsCut.oneT
  rw [hg]

theorem oneSC_at (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y) (hG : GamPin Y)
    {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1) (hFo : UnitaryVolumeMass.FormAt D u)
    (hCT : Formalism.L2.SG.RowsConc.ConcTie X Y) (C0 C : ℝ) (hC0' : 0 ≤ C)
    (h1 : Formalism.MainNotions.BridgeLemma.RowsOne T L C) :
    LoopsCut.ClassLe (Y.tO u u') ((Y.tO u u').nsc (Y.tO u u').genSet)
      (max 1 C0 * LoopsCut.oneT C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (GamS D large₂) *
        Formalism.L2.SG.RowsConc.ddC X Y u u') := by
  unfold LoopsCut.ClassLe
  rw [← oneB_eq (X := X) C, ddC_eq hCT]
  have hcl := gam_mul_le hG L hFo (classOne_le T hJ hW hC L C h1)
  have hA : 0 ≤ Formalism.L2.SG.RowsOther.ampSum (Y.tO u u') ((Y.tO u u').nsc (Y.tO u u').genSet) := by
    unfold Formalism.L2.SG.RowsOther.ampSum
    exact tsum_nonneg fun p => Set.indicator_nonneg (fun p _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) p
  have hg0 : 0 ≤ (Y.tO u u').Gam1 := by
    rw [hG u u']
    exact Formalism.MainNotions.BridgeLemma.gaG_nonneg D
  have hq : 0 ≤ (D.duS u : ℝ) * (Formalism.MainNotions.BridgeLemma.oneB D large₂ C * Formalism.MainNotions.BridgeLemma.rDD D u') :=
    le_trans (mul_nonneg hg0 hA) hcl
  have hM1 : 1 ≤ max 1 C0 := le_max_left _ _
  calc _ ≤ _ := hcl
    _ ≤ max 1 C0 * ((D.duS u : ℝ) * (Formalism.MainNotions.BridgeLemma.oneB D large₂ C * Formalism.MainNotions.BridgeLemma.rDD D u')) :=
      le_mul_of_one_le_left hq hM1
    _ = _ := by ring

end Cut

section Fam

structure ConcAt (D : D7) (T : TermTie D) where
  X : HidaSetting D
  Y : Full X
  hF : FinX Y
  hI : SIso D.s (sOf hF)
  jt : JtPin hF hI T
  wr : WRowPin hF hI T
  fc : FibreCount Y
  gam : GamPin Y

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
  (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt (Fm.D x i) (At x hx i))

def RowLoopsF : Prop :=
  ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A →
      (∀ s, 2 ≤ s → s ≤ (Fm.D x i).R.k →
        ((Cc x hx i).Y.tO u u').Gam1 *
            Formalism.L2.SG.RowsOther.ampSum ((Cc x hx i).Y.tO u u') (LoopsCut.bigS ((Cc x hx i).Y.tO u u') s) ≤
          ((Fm.D x i).duS u : ℝ) *
            (LatticeSumBounds.ndRow C (Fm.D x i).R.k (Fm.D x i).R.m (Fm.D x i).R.f s (Fm.L x i).sc.b (gg (Fm.D x i))
                             (Fm.D x i).host.v (GamS (Fm.D x i) (Fm.L x i)) (Formalism.MainNotions.BridgeLemma.XiB (Fm.D x i) (Fm.L x i) u C) *
                             Formalism.MainNotions.BridgeLemma.rDD (Fm.D x i) u' +
              LatticeSumBounds.degRow C (Fm.D x i).R.k (Fm.D x i).R.m (Fm.D x i).R.f s (Fm.L x i).sc.b (gg (Fm.D x i))
                (Fm.D x i).host.v (GamS (Fm.D x i) (Fm.L x i)) (Formalism.MainNotions.BridgeLemma.XiB (Fm.D x i) (Fm.L x i) u C))) ∧
      ((Cc x hx i).Y.tO u u').Gam1 *
          Formalism.L2.SG.RowsOther.ampSum ((Cc x hx i).Y.tO u u')
            (((Cc x hx i).Y.tO u u').nsc ((Cc x hx i).Y.tO u u').genSet) ≤
        ((Fm.D x i).duS u : ℝ) *
          (Formalism.MainNotions.BridgeLemma.oneB (Fm.D x i) (Fm.L x i) C * Formalism.MainNotions.BridgeLemma.rDD (Fm.D x i) u')

theorem rowLoopsF_of (hFo : ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, UnitaryVolumeMass.FormAt (Fm.D x i) u)
    (hR : Formalism.MainNotions.BridgeLemma.RowsF Fm C1 At Yt) : RowLoopsF Fm At Cc := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨C₀, hC₀⟩ := hR Cg cb Cu cT CT C0 A
  refine ⟨C₀, fun C hC => ?_⟩
  obtain ⟨x0, hx0⟩ := hC₀ C hC
  refine ⟨x0, fun x hx i => ?_⟩
  intro hx1 u u' hH
  obtain ⟨hn, hd, h1⟩ := hx0 x hx i hx1 u u' hH
  refine ⟨fun s h2 hk => ?_, ?_⟩
  · exact gam_mul_le (Cc x hx1 i).gam (Yt x hx1 i u u') (hFo x hx1 i u)
      (classS_le (At x hx1 i) (Cc x hx1 i).jt (Cc x hx1 i).wr (Cc x hx1 i).fc (Yt x hx1 i u u') C hn hd s h2 hk)
  · exact gam_mul_le (Cc x hx1 i).gam (Yt x hx1 i u u') (hFo x hx1 i u)
      (classOne_le (At x hx1 i) (Cc x hx1 i).jt (Cc x hx1 i).wr (Cc x hx1 i).fc (Yt x hx1 i u u') C h1)

end Fam

section Parts

open MeasureTheory

structure LoopRowsDat (D : D7) (T : TermTie D) (u u' : D.what₂.Word) where
  F0 : FlagG (VS D) D.R.rS (Tu D u : D.host.E)
  flag_e_eq_hyperbolic : F0.e = D.sp.hypE
  formsAtZero : F0.z = D.zmOf u
  what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)
  isRows : IsRowReps D F0 what₂
  fl_eq : ∀ t : D.s.Term u u', T.fl t = lf D F0
  Lam_mem : ∀ t : D.s.Term u u', T.abelian₂ t ∈ what₂
  frame_ok : ∀ t : D.s.Term u u', FrameOK D (T.abelian₂ t) (T.fl' t)
  wRow_eq : ∀ p : D.s.Pair u u', T.wRow p = wRow D F0 (T.abelian₂ (D.s.pfst p))
  pair_inj : ∀ p q : D.s.Pair u u', T.abelian₂ (D.s.pfst p) = T.abelian₂ (D.s.pfst q) →
    (∃ n' ∈ NLam (T.abelian₂ (D.s.pfst p)) (lf D F0), ∃ n'' ∈ NLam (T.abelian₂ (D.s.pfst p)) (lf D F0),
      FrameEqv D n' (T.fl' (D.s.pfst p)) (T.fl' (D.s.pfst q)) ∧
      FrameEqv D n'' (T.fl' (D.s.psnd p)) (T.fl' (D.s.psnd q)) ∧
      ∀ x ∈ orth (hS D) (Xsp (T.fl' (D.s.pfst q))),
        T.beta q x - n'' (T.beta p (n'.symm x)) ∈ Xsp (T.fl' (D.s.psnd q))) → p = q

structure LoopLocDat (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C1 : ℝ) : Type 1 where
  θ : ℝ
  θ_win : normWin D large₂ C1 θ
  W : D.what₂.Tau → LocW D.R.k D.R.rS
  goodW : ∀ τ, GoodW D τ u u' θ (W τ)
  A : ∀ τ, LocS (W τ)
  goodS : ∀ τ, GoodS D (lamD D τ) (A τ)
  deg_eq : ∀ τ, (A τ).deg = D.dsig τ

structure LoopTermDat (D : D7) (large₂ : SizeData₂ D) (T : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (B : LoopLocDat D large₂ u u' C1) : Type 1 where
  γ : D.s.Term u u' → D.what₂.Tau → MatKR D.R.k D.R.rS
  pt : D.s.Term u u' → D.what₂.Tau → Point ℂ (D.R.rS + 1)
  θR : D.s.Term u u' → D.what₂.Tau → ℝ
  νR : D.s.Term u u' → D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
  volR : D.s.Term u u' → ℝ
  volR_pos : ∀ t, 0 < volR t
  gram : ∀ (t : D.s.Term u u') τ a b, Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (B.W τ).z (B.W τ).z' (γ t τ) a b =
    ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (ZhatL (T.fl t) (T.fl' t) a b)
  rel : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    RelPt D (B.W τ).z (B.W τ).z' (γ t τ) (pt t τ) ∧ normWin D large₂ C1 (θR t τ) ∧
      RMeas D (B.W τ) (γ t τ) (θR t τ) (νR t τ)
  J_irr : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → ¬ D.s.relevant t → T.Jt t = 0
  J_norm : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    hsNormSq (T.Jt t) = volR t ^ 2 * ∏ τ, hsNormSq ((B.A τ).J (νR t τ) (γ t τ))

def loopTieOfParts {D : D7} {large₂ : SizeData₂ D} {T : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ}
    (R : LoopRowsDat D T u u') (B : LoopLocDat D large₂ u u' C1) (M : LoopTermDat D large₂ T u u' C1 B) :
    LoopTie D large₂ T u u' C1 where
  F0 := R.F0
  flag_e_eq_hyperbolic := R.flag_e_eq_hyperbolic
  formsAtZero := R.formsAtZero
  what₂ := R.what₂
  isRows := R.isRows
  fl_eq := R.fl_eq
  Lam_mem := R.Lam_mem
  frame_ok := R.frame_ok
  wRow_eq := R.wRow_eq
  pair_inj := R.pair_inj
  θ := B.θ
  θ_win := B.θ_win
  W := B.W
  goodW := B.goodW
  A := B.A
  goodS := B.goodS
  deg_eq := B.deg_eq
  γ := M.γ
  pt := M.pt
  θR := M.θR
  νR := M.νR
  volR := M.volR
  volR_pos := M.volR_pos
  gram := M.gram
  rel := M.rel
  J_irr := M.J_irr
  J_norm := M.J_norm

theorem loopTie_parts {D : D7} {large₂ : SizeData₂ D} {T : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ}
    (L : LoopTie D large₂ T u u' C1) :
    ∃ (R : LoopRowsDat D T u u') (B : LoopLocDat D large₂ u u' C1) (M : LoopTermDat D large₂ T u u' C1 B),
      loopTieOfParts R B M = L := by
  exact ⟨⟨L.F0, L.flag_e_eq_hyperbolic, L.formsAtZero, L.what₂, L.isRows, L.fl_eq, L.Lam_mem, L.frame_ok, L.wRow_eq, L.pair_inj⟩,
    ⟨L.θ, L.θ_win, L.W, L.goodW, L.A, L.goodS, L.deg_eq⟩,
    ⟨L.γ, L.pt, L.θR, L.νR, L.volR, L.volR_pos, L.gram, L.rel, L.J_irr, L.J_norm⟩, rfl⟩

variable {D : D7} {X : HidaSetting D} {Y : Full X}

def VolRPin (hF : FinX Y) (hI : SIso D.s (sOf hF)) {large₂ : SizeData₂ D} {T : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ}
    {B : LoopLocDat D large₂ u u' C1} (M : LoopTermDat D large₂ T u u' C1 B) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → D.s.generic t →
    ∃ (w : Point D.host.E (D.R.rS + 1)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep (hI.eT u u' t) w F' L U ∧
      M.volR t = Formalism.L2.SG.PairVal.volIdx D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M (hI.eT u u' t) w F' L

def VolRBound {large₂ : SizeData₂ D} {T : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} {B : LoopLocDat D large₂ u u' C1}
    (M : LoopTermDat D large₂ T u u' C1 B) : Prop :=
  ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ Cf : ℝ → ℝ, ∀ C' Cl : ℝ, Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
    ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
      M.volR t ≤ HHZ D large₂.sc.b (Cf Cl) (ZhatL (T.fl t) (T.fl' t)) ^ (Cf Cl * (D.R.rS : ℝ) ^ 2)

end Parts

end Formalism.L2.SG.LoopTieOf
