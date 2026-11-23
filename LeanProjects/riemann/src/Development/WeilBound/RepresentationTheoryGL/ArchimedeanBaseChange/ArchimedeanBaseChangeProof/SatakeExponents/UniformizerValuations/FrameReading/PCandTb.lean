import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandOut
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FactorActionAlgebra
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocOk
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.LocOp3
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BaseChangeWeyl.ContinuousRingHom

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Tr pairSpace)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.PCandTb

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

set_option linter.unusedSectionVars false

theorem isLev_of {a b : ℕ} (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (Q : Finset (Pl E))
    (h : ∀ w, LocOk.IsLv (U w)) (hout : ∀ w ∉ Q, U w = K2 a b w) : IsLev U := by
  refine ⟨fun w => ?_, Filter.eventually_cofinite.2 (Q.finite_toSet.subset fun w hw => ?_)⟩
  · obtain ⟨K₁, K₂, h₁, h₂, he⟩ := h w
    rw [he]
    exact LocOk.prod_open_le h₁ h₂
  · by_contra hq
    exact hw (hout w hq)

variable {n : ℕ} (d : LocData E n) {a : ℕ}

theorem isLev_lev (hd : d.Ok) (ha : a ≤ n) : IsLev (d.lev a) :=
  isLev_of _ (d.T ∪ d.S₀ ∪ d.Bad) (LocOk.lev_lv d hd ha) fun _ hw =>
    LocOk.lev_out d (LocOk.out3 d hw).1 (LocOk.out3 d hw).2

theorem isLev_lev₂ (hd : d.Ok) (ha : a ≤ n) : IsLev (d.lev₂ a) :=
  isLev_of _ (d.T ∪ d.S₀ ∪ d.Bad) (LocOk.lev₂_lv d hd ha) fun _ hw => LocOk.lev₂_out d (LocOk.out3 d hw).2

theorem betaL_H (hd : d.Ok) (ha : a ≤ n) {u : Pl E} (hu : u ∈ d.P) (x y : d.kap u) :
    IsHecke (d.lev a u) ((d.betaL a ha).m u x y) := by
  show IsHecke _ (if u ∈ d.T then d.diag (fun x => d.qT a u x.1.1) x y else d.mac a ha u (d.e u) x.1.2 y.1.2)
  split_ifs with hT
  · rw [LocOk.level_eq_iwahori_pair_at_bad_places d hT]
    exact LocOk.diagH d _ (fun z => LocOk.qT_H d u z.1.1) x y
  · have hS : u ∈ d.S₀ := by
      simp only [LocData.P, Finset.mem_union] at hu
      tauto
    rw [LocOk.lev_S d hT (Finset.mem_union_left _ hS)]
    exact LocOk.mac_H d PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha hS (LocOk.kap_X d hT hS x) (LocOk.kap_X d hT hS y)

theorem gap_restr {m : ℕ} {x : Fin n → ℤ} (hx : x ∈ coneGL n 2) (S : Finset (Fin n)) (h : S.card = m) :
    Gap (PositivityTheory.Rg.Bc.ArchbcB.B.restr x S h) := by
  intro p q hpq
  have := hx _ _ ((S.orderEmbOfFin h).strictMono hpq)
  show x _ + 1 ≤ x _
  omega

theorem unrAt_pow {μ : HChar E} {w : Pl E} (h : μ.UnrAt w) (k : ℕ) : (μ ^ k).UnrAt w := by
  induction k with
  | zero => intro x _; rw [pow_zero]; rfl
  | succ k ih =>
    intro x hx
    rw [pow_succ]
    show (μ ^ k).loc w x * μ.loc w x = 1
    rw [ih x hx, h x hx, one_mul]

end PositivityTheory.Rg.BcB.F.PCandTb

namespace PositivityTheory.Rg.BcB.F

open PCandTb

theorem candT_of (h1 : Tail.ReadT) (h2 : Tail.ExpRead) (h3 : RS.JoinSat) : CandT := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne w hwT hunr hns
  have hd := F.ok
  have hwd : w ∈ F.d.T := F.T_le w hwT hunr hns
  have hwSec : w ∈ F₀.Sec := (F.T_in w hwd).1
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := by
    intro u hu
    rcases Finset.mem_union.1 hu with h | h
    · exact (F.T_in u h).1
    · rw [F.same.1] at h
      exact (F₀.S₀ u h).1
  have hwP : w ∈ F.d.P := Finset.mem_union_left _ hwd
  obtain ⟨α, x, hx⟩ := FA.fmPow_of intHint slots BlockFiniteConvolution.finConv' BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i)
    (Equiv.refl _) F₀.hSec hP (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (F.d.betaL _ (F₀.C.le i)) A G F.m
    (isLev_lev F.d hd (F₀.C.le i)) (isLev_lev₂ F.d hd (F₀.C.le i))
    (locOk idemAlg PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 E n F.d hd _ (F₀.C.le i)).2.1 (fun _ => rfl) (fun _ => rfl)
    (fun u hu x y k hk g => (betaL_H F.d hd (F₀.C.le i) hu x y).2 k hk g) hl hne ⟨w, hwP⟩
  have hm : (F.d.betaL _ (F₀.C.le i)).m w = fun x y => if x = y then F.d.qT (F₀.C.a i) w x.1.1 else 0 := by
    funext x y
    show (if w ∈ F.d.T then _ else _) = _
    rw [if_pos hwd]
    rfl
  let G' : F.d.kap w → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ := fun y => G (α, Function.update x ⟨w, hwP⟩ y)
  change (locM w ((F.d.betaL _ (F₀.C.le i)).m w))^[F.m] G' ≠ 0 at hx
  rw [hm] at hx
  have hfix : ∀ y, G' y ∈ fixed (pairRt (F₀.C.a i) (n - F₀.C.a i) w) (I2 (F₀.C.a i) (n - F₀.C.a i) w) := fun y => by
    have h := ((hl (α, Function.update x ⟨w, hwP⟩ y)).2 w hwSec).1
    rwa [LocOk.level_eq_iwahori_pair_at_bad_places F.d hwd] at h
  have hIo : IsOpen (I2 (F₀.C.a i) (n - F₀.C.a i) w : Set (GLw (F₀.C.a i) w × GLw (n - F₀.C.a i) w)) := by
    have h := ((isLev_lev F.d hd (F₀.C.le i)).1 w).1
    rwa [LocOk.level_eq_iwahori_pair_at_bad_places F.d hwd] at h
  obtain ⟨s, hs⟩ := (locPow_holds E _ _ w _ _ G' F.m hIo hfix).2 (fun x => F.d.qT (F₀.C.a i) w x.1.1) (by convert hx)
  by_cases hadm : LocData.admitted n (F₀.C.a i) s.1.1
  swap
  · exfalso
    have h0 : F.d.qT (F₀.C.a i) w s.1.1 = 0 := by
      funext y
      simp only [LocData.qT, dif_neg hadm]
      rfl
    obtain ⟨k, hk⟩ : ∃ k, F.m = k + 1 := ⟨F.m - 1, by have := F.m_pos; omega⟩
    rw [h0, hk, Function.iterate_succ_apply', Psmall.actP_zero] at hs
    exact hs rfl
  have hq : F.d.qT (F₀.C.a i) w s.1.1 = fun g => ∑ j : (F.d.c w).support,
      (F.d.c w j * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf (j : Fin n → ℤ)) s.1.1) *
        (((I2 (F₀.C.a i) (n - F₀.C.a i) w).relIndex (K2 (F₀.C.a i) (n - F₀.C.a i) w) : ℕ) : ℂ)) *
      dc2 w (F.d.ϖ w) (restr (j : Fin n → ℤ) _ hadm.2.1) (restr (j : Fin n → ℤ) _ hadm.2.2) g := by
    funext g
    simp only [LocData.qT, dif_pos hadm, Finsupp.sum]
    rw [← Finset.sum_coe_sort]
  rw [hq] at hs
  obtain ⟨ξa, ξb, hJ, hsum⟩ := h1 E n (F₀.C.a i) (n - F₀.C.a i) F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F.d.ϖ w)
    (F.d.c w).support _ (fun j => restr (j : Fin n → ℤ) _ hadm.2.1) (fun j => restr (j : Fin n → ℤ) _ hadm.2.2) F.m (G' s)
    (hd.unif w)
    (fun j => ⟨gap_restr (hd.cone w hwd (Finset.mem_coe.2 j.2)) _ _, gap_restr (hd.cone w hwd (Finset.mem_coe.2 j.2)) _ _⟩)
    ((F.choiceM i s₁ s₂ Pa Pb D hc).2 w hwd) (hG _) (hfix s) hs
  have hsum' : ((F.d.c w).sum fun x t => t * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf x) s.1.1) *
      ev2 w ξa ξb (restr x _ hadm.2.1) (restr x _ hadm.2.2)) ≠ 0 := by
    intro h0
    rw [Finsupp.sum, ← Finset.sum_coe_sort] at h0
    apply hsum
    rw [show (0 : ℂ) = (((I2 (F₀.C.a i) (n - F₀.C.a i) w).relIndex (K2 (F₀.C.a i) (n - F₀.C.a i) w) : ℕ) : ℂ) * 0 by ring,
      ← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hJ' : JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb := by
    rw [← F.same.2.2.2.1]
    exact hJ
  obtain ⟨hma, hmb, hbc⟩ := F.choiceT i s₁ s₂ Pa Pb D hc w hwd s.1.1 hadm ξa ξb hJ' hsum'
  obtain ⟨hSa, hSb⟩ := h2 E (F₀.C.a i) (n - F₀.C.a i) Pa Pb w (F.d.ϖ w) ξa ξb (hd.unif w) hma hmb hJ
  have hS0 : w ∉ F₀.d₀.S₀ := by
    rw [← F.same.1]
    exact Finset.disjoint_left.1 hd.disj.1 hwd
  have hBad : w ∉ F₀.d₀.Bad := by
    rw [← F.same.2.1]
    exact Finset.disjoint_left.1 hd.disj.2.1 hwd
  have hμ := (F₀.good w hwSec hS0 hBad).2
  have hDs := h3 E n (F₀.C.a i) (n - F₀.C.a i) (F₀.μ ^ (n - F₀.C.a i)) (F₀.μ ^ F₀.C.a i) Pa Pb D w _ _ hc.ctx.join
    (unrAt_pow hμ _) (unrAt_pow hμ _) hSa hSb
  refine ⟨_, hDs, fun s' ϖ q hs' hq' α' hα' => ?_⟩
  have e := LemB.cjEq E w hns s' hs'
  subst e
  exact hbc ϖ q hq' α' hα'

end PositivityTheory.Rg.BcB.F

end
