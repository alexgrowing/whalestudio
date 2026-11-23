import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopPairSourceCharProdLocalIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

open scoped TensorProduct

namespace GlobalTheory.FlatPlace

theorem finComp_eq_toAd {D : D7} (z : AE D) :
    GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E z = GlobalTheory.StdFrames.toAd D (Formalism.IndefR.Datum.toEAf D z) := by
  have key : ∀ y : Af D.host.F ⊗[D.host.F] D.host.E,
      GlobalTheory.LFun.toFinAd D.host.F D.host.E y = GlobalTheory.StdFrames.toAd D (Formalism.IndefR.Lev.swapAE D y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      rw [GlobalTheory.LFun.toFinAd_tmul, mul_comm]
      exact (GlobalTheory.StdFrames.toAd_spec D x a).symm
    | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]
  exact key _

theorem iota_add_eq_locIdele {D : D7} {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) (x : (Kw w)ˣ) :
    p.ι x + (1 - p.e) = (GlobalTheory.LFun.locIdele D.host.F w x : AE D) := by
  classical
  have e_ι : ∀ y, p.e * p.ι y = p.ι y := fun y => by rw [← p.ι_π, p.π_ι]
  have he1 : p.e = atPl w 1 := by
    rw [← hp.2.2 1]
    have := p.ι_π 1
    rw [map_one, mul_one] at this
    exact this.symm
  have hfc : ∀ z Q, GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E z Q = GlobalTheory.StdFrames.cpt Q (Formalism.IndefR.Datum.toEAf D z) :=
    fun z Q => by rw [finComp_eq_toAd]; rfl
  have hδ : GlobalTheory.CMPrimeIdele.IsDelta (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) w p.e := by
    refine ⟨by rw [he1]; exact (atPl_spec w 1).1, by rw [hfc, he1, (atPl_spec w 1).2, Pi.single_eq_same], fun Q hQ => ?_⟩
    rw [hfc, he1, (atPl_spec w 1).2, Pi.single_eq_of_ne hQ]
  have := GlobalTheory.LFun.EulerTie.glue_eq_locIdele hδ (a := p.ι x) (u := x)
    (by rw [hfc, hp.2.2, (atPl_spec w _).2, Pi.single_eq_same])
  rwa [e_ι] at this

theorem isComp_attChr {D : D7} {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) (c η : (AE D)ˣ →* Circle)
    (μ e : (Kw w)ˣ →* ℂˣ) (hc : ∀ y, ((c (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) = ((μ y : ℂˣ) : ℂ))
    (he : ∀ y, ((η (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) = ((e y : ℂˣ) : ℂ)) (n k : ℕ)
    (hk : (k + 1) % 2 = if Odd n then 1 else 0) :
    p.IsComp (Formalism.IndefR.Lift.attChr c η n) (μ / e ^ ((k + 1) % 2)) := by
  intro x a ha
  have ha' : a = GlobalTheory.LFun.locIdele D.host.F w x := Units.ext (ha.trans (iota_add_eq_locIdele hp x))
  subst ha'
  rw [hk]
  unfold Formalism.IndefR.Lift.attChr
  split_ifs with h
  · simp only [pow_one, MonoidHom.div_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_div_eq_div_val,
      Circle.coe_mul, Circle.coe_inv, hc, he, div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  · simp only [pow_zero, div_one, hc]

end GlobalTheory.FlatPlace

namespace GlobalTheory.FlatPlace

theorem chrP_big : Big fun ch => ChrP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t w hw p hp
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  refine ⟨fun x => ?_, (((Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw).square 0 hm 0 hm).cond, fun j hj => ?_⟩
  · rw [hp.2.2 x]
    rfl
  have hE : ChrEq (R.toLevCh.mu t (j + 1)) (muBase R.toLevCh (j + 1) * R.toLevCh.xiH t) := by
    have h1 : muBase R.toLevCh (j + 1) = R.toLevCh.C.mu0 ⟨j, hj⟩ := dif_pos hj
    rw [h1]
    exact GlobalTheory.TowerCharRead.chrEq_mul (hL.mu0 ⟨j, hj⟩) (hL.xi t)
  have hmu : ∀ y, ((R.toLevCh.mu t (j + 1) (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((locGrid ch.G t w).mu (j + 1) y : ℂˣ) : ℂ) :=
    fun y => congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w)
  have heta : ∀ y, ((R.toLevCh.eta (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((locGrid ch.G t w).eta y : ℂˣ) : ℂ) :=
    fun y => congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hL.eta w)
  have r0 := (rank_vertex ch.G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩).symm
  have r1 := (rank_vertex ch.G t w (X := (D.R.m, j + 1)) ⟨le_rfl, hj⟩).symm
  have hstep : (locGrid ch.G t w).rank (D.R.m, j + 1) = (locGrid ch.G t w).rank (D.R.m, j) + D.R.t := by
    show D.R.r + (j + 1) * D.R.t + D.R.m * sLen D = D.R.r + j * D.R.t + D.R.m * sLen D + D.R.t
    ring
  obtain ⟨c, hc'⟩ := D.R.t_odd
  refine ⟨?_, ?_⟩
  · refine isComp_attChr hp _ _ _ _ hmu heta _ _ ?_
    rw [r0, hstep, hc']
    split_ifs with h
    · obtain ⟨d, hd⟩ := h; omega
    · rw [Nat.not_odd_iff_even] at h; obtain ⟨d, hd⟩ := h; omega
  · refine isComp_attChr hp _ _ _ _ hmu heta _ _ ?_
    rw [r1, hstep, hc']
    split_ifs with h
    · obtain ⟨d, hd⟩ := h; omega
    · rw [Nat.not_odd_iff_even] at h; obtain ⟨d, hd⟩ := h; omega

end GlobalTheory.FlatPlace
