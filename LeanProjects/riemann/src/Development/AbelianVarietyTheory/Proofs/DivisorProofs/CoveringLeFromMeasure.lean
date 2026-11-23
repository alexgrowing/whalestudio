import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisationStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CoreSlope

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

set_option maxHeartbeats 1000000 in

theorem coreAt_of (C : ℝ) (hg : GramAt p i) (hm : MeasAt p i C) (hr : RatAt p i) : CoreAt p i (2 * C) := by
  obtain ⟨ι, hι, hli, himg⟩ := GlobalTheory.T.exists_semilinear_emb_supLattice_onto_realisation _ _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  have hTC : IsTotallyComplex p.T.Q.c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := p.T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hc : ∀ σ x, nrmK p.fw i ((starRingEnd ℂ).comp σ) x = nrmK p.fw i σ x := fun σ x => by
    simp only [nrmK]
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hfg : (latTypeK p.fw p.F.lv2 i).FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ hg.2.2.2.2.1
    exact Submodule.FG.of_le_of_isNoetherian (T := latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n)) inf_le_left
  have hN : ∀ σ' x, nrmR p.R.toRealDat i σ' (ι x) ≤ Real.exp (C * unitE p) * nrmK p.fw i (σ'.comp (algebraMap p.T.Q.c.F D.what₂.LL)) x := by
    intro σ' x
    obtain ⟨c, hc0, hcl, hcf⟩ := hm σ'
    obtain ⟨h, hx⟩ := hι x
    rw [hx, hcf ⟨x, h⟩]
    have hce : c ≤ Real.exp (C * unitE p) := by
      calc c = Real.exp (Real.log c) := (Real.exp_log hc0).symm
        _ ≤ Real.exp (C * unitE p) := Real.exp_le_exp.2 ((le_abs_self _).trans hcl)
    exact mul_le_mul_of_nonneg_right hce (petAt_nonneg _ _ _ _ _ _ _)
  have hS : latType p.R.toRealDat p.F.lv2 i =
      Submodule.span (𝓞 D.what₂.LL) (ι '' (latTypeK p.fw p.F.lv2 i : Set (VK p.fw i))) := by
    rw [hr]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hy1, hy2⟩
      have hy1' : y ∈ (ι '' (latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n) : Set (VK p.fw i))) := by
        rw [himg]; exact hy1
      obtain ⟨x, hx, rfl⟩ := hy1'
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      show (x : p.T.R _) ∈ Submodule.span _ (typeK p.fw p.F.lv2 i)
      obtain ⟨h, hx'⟩ := hι x
      exact Submodule.subset_span ⟨h, hx' ▸ hy2⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨(show ι x ∈ ((p.R.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) by rw [← himg]; exact ⟨x, hx1, rfl⟩), ?_⟩
      have hsp : Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i) ≤
          ((spType p.R.toRealDat p.F.lv2 i).comap ι).map (VK p.fw i).subtype := by
        rw [Submodule.span_le]
        rintro f ⟨h, hf⟩
        have hfV : f ∈ VK p.fw i := by rw [VK, cuspW_wtZ]; exact h
        refine ⟨⟨f, hfV⟩, ?_, rfl⟩
        obtain ⟨h', e⟩ := hι ⟨f, hfV⟩
        show ι ⟨f, hfV⟩ ∈ spType p.R.toRealDat p.F.lv2 i
        rw [e]
        exact hf
      obtain ⟨z, hz, hzx⟩ := hsp hx2
      have : z = x := Subtype.ext hzx
      subst this
      exact hz
  have h0 : latTypeK p.fw p.F.lv2 i ≠ ⊥ := by
    intro h0
    apply hg.2.2.1
    rw [eq_bot_iff]
    refine (latGood_le _ _ _).trans ?_
    rw [hS, h0]
    simp
  have key := GlobalTheory.SlopeExt.slope_sq_sub_le_slope_sq_span p.T.Q.c.F D.what₂.LL (VK p.fw i) (Fin (p.R.toRealDat.nW i) → D.what₂.LL)
    (nrmK p.fw i) (nrmR p.R.toRealDat i) ι (latTypeK p.fw p.F.lv2 i) (C * unitE p) hg.2.2.2.1 hg.1 hc hli hfg h0 hN
  unfold CoreAt muCore
  rw [hS]
  linarith

theorem coreLe_of_gram_meas_rat : Gram → Meas → GlobalTheory.CovTop.Rat → CoreLe := by
  intro hg hm hr
  unfold Gram Meas GlobalTheory.CovTop.Rat CoreLe Lifts at *
  refine Closed.imp (Closed.and (Closed.and hg hm) hr) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, hg'⟩, ⟨C, hC, hm'⟩⟩, ⟨C3, -, hr'⟩⟩
  refine ⟨2 * C, by linarith, ?_⟩
  obtain ⟨x0, h⟩ := (hg'.and hm').and hr'
  exact ⟨x0, fun x hx hle ι p hp i =>
    coreAt_of p i C ((h x hx hle ι p hp).1.1 i) ((h x hx hle ι p hp).1.2 i) ((h x hx hle ι p hp).2 i)⟩

example : Gram → Meas → GlobalTheory.CovTop.Rat → CoreLe := coreLe_of_gram_meas_rat

end GlobalTheory.CoreSlope
