import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulPowLeRpow
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

open Matrix GlobalTheory.GradedNorm GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.HodgeLogBd

theorem grSq_le_of_quad {m : ℕ} {M M₀ : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosDef) (hM₀ : M₀.PosDef) {t : ℝ}
    (h : ∀ v : Fin m → ℂ, (star v ⬝ᵥ M *ᵥ v).re ≤ t * (star v ⬝ᵥ M₀ *ᵥ v).re) (i : Fin m) :
    grSq M i ≤ t * grSq M₀ i := by
  obtain ⟨⟨v, h1, h2, e⟩, -⟩ := isLeast_grSq hM₀ i
  rw [e]
  exact ((isLeast_grSq hM i).2 ⟨v, h1, h2, rfl⟩).trans (h v)

theorem abs_log_grSq_sub_le {m : ℕ} {M M₀ : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosDef) (hM₀ : M₀.PosDef) {r C : ℝ}
    (hr : 0 < r) (h₁ : ∀ v : Fin m → ℂ, r ^ (-C) * (star v ⬝ᵥ M₀ *ᵥ v).re ≤ (star v ⬝ᵥ M *ᵥ v).re)
    (h₂ : ∀ v : Fin m → ℂ, (star v ⬝ᵥ M *ᵥ v).re ≤ r ^ C * (star v ⬝ᵥ M₀ *ᵥ v).re) (i : Fin m) :
    |Real.log (grSq M i) - Real.log (grSq M₀ i)| ≤ C * Real.log r := by
  have hp : 0 < r ^ C := Real.rpow_pos_of_pos hr C
  have e : r ^ C * r ^ (-C) = 1 := by rw [← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero]
  have a := grSq_le_of_quad hM hM₀ h₂ i
  have b := grSq_le_of_quad hM₀ hM (t := r ^ C) (fun v => by
    have := mul_le_mul_of_nonneg_left (h₁ v) hp.le
    rwa [← mul_assoc, e, one_mul] at this) i
  have g := grSq_pos hM i
  have g₀ := grSq_pos hM₀ i
  have la := Real.log_le_log g a
  have lb := Real.log_le_log g₀ b
  rw [Real.log_mul hp.ne' g₀.ne', Real.log_rpow hr] at la
  rw [Real.log_mul hp.ne' g.ne', Real.log_rpow hr] at lb
  rw [abs_sub_le_iff]
  constructor <;> linarith

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {σ : F →+* ℂ}

theorem lnRatio_met (G G₀ : EigMet Z (embOf e σ)) (n : Pad.Letter Dw → ℤ) (p : Y.Y.pts σ) :
    ∃ g : Y.FrameAt p, lnRatio (C := cxSt F) (Y.met G n) (Y.met G₀ n) p =
      (∑ z : Pad.Letter Dw, (n z : ℝ) * (Real.log (grSq (G.gram _ g z.1) z.2) - Real.log (grSq (G₀.gram _ g z.1) z.2))) / 2 := by
  obtain ⟨q, h1, h2⟩ := Y.exists_adapted p
  refine ⟨q.2, ?_⟩
  have hmem := FlagCpt.prodPow_mem n h1
  have k1 := FlagCpt.met_h G n h2
  have k2 := FlagCpt.met_h G₀ n h2
  have hone : ‖((prodPow (1 : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℂˣ) n : ℂˣ) : ℂ)‖ ^ 2 = 1 := by simp [prodPow]
  rw [hone, div_one] at k1 k2
  have e1 : (cxSt F).pn Y.Y σ _ (Y.met G n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p =
      ‖Var.fval (prodPow q.1 n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p‖ ^ 2 * Y.genSq G n q.2 := by
    rw [← k1]; exact Var.pn_eq hmem
  have e2 : (cxSt F).pn Y.Y σ _ (Y.met G₀ n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p =
      ‖Var.fval (prodPow q.1 n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p‖ ^ 2 * Y.genSq G₀ n q.2 := by
    rw [← k2]; exact Var.pn_eq hmem
  have hP : PosAt (C := cxSt F) (Y.met G n) p := posAt_of_posSet (FlagCpt.posSet_met _ _) p
  have hg := Y.genSq_pos G n q.2
  have hg₀ := Y.genSq_pos G₀ n q.2
  have hK : 0 < ‖Var.fval (prodPow q.1 n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p‖ ^ 2 := by
    have : 0 < (cxSt F).pn Y.Y σ _ (Y.met G n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p := hP
    rw [e1] at this
    exact pos_of_mul_pos_left this hg.le
  simp only [lnRatio, lnN]
  rw [e1, e2, Real.log_mul hK.ne' hg.ne', Real.log_mul hK.ne' hg₀.ne']
  have lg : ∀ G' : EigMet Z (embOf e σ), Real.log (Y.genSq G' n q.2) =
      ∑ z : Pad.Letter Dw, (n z : ℝ) * Real.log (grSq (G'.gram _ q.2 z.1) z.2) := fun G' => by
    rw [FlagCpt.genSq, Real.log_prod (fun z _ => (zpow_pos (grSq_pos (G'.pos _ _ _) _) _).ne')]
    exact Finset.sum_congr rfl fun z _ => Real.log_zpow _ _
  rw [lg G, lg G₀]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end Flag

section FinalTheorems

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag)

theorem abs_lnRatio_le {C : ℝ} (hC : x.IsMuExp C) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ)
    (p : Pts (Φ.C k).Y σ) (hp : (Φ.C k).π (under p) ∉ genBd s.T.Z) :
    |lnRatio (metsOf x Φ k none σ n) (refMet x Φ k σ n) p| ≤
      (∑ z : Pad.Letter S.Dw, |(n z : ℝ)|) / 2 * (C * Real.log (rFlag x Φ k σ p)) := by
  obtain ⟨g, hg⟩ := lnRatio_met (Φ.C k) (x.hodge (embOf κ.e σ)) (x.eigMet (embOf κ.e σ)) n p
  have hb : ¬ LiesIn ((Φ.C k).down p) (genBd s.T.Z) := hp
  have hr : 0 < rFlag x Φ k σ p := (Real.exp_pos 1).trans_le exp_le_rFlag
  have key : ∀ z : Pad.Letter S.Dw, |Real.log (grSq ((x.hodge (embOf κ.e σ)).gram _ g z.1) z.2) -
      Real.log (grSq (OddPrimesWithRootsOfUnity.gram x ((Φ.C k).down p) g z.1) z.2)| ≤ C * Real.log (rFlag x Φ k σ p) := fun z => by
    have h1 := fun v => (hC.2 _ _ hb g z.1 v).1
    have h2 := fun v => (hC.2 _ _ hb g z.1 v).2
    exact abs_log_grSq_sub_le (M := (x.hodge (embOf κ.e σ)).gram ((Φ.C k).down p) g z.1)
      (M₀ := OddPrimesWithRootsOfUnity.gram x ((Φ.C k).down p) g z.1) (r := rFlag x Φ k σ p) (C := C)
      (EigMet.pos _ _ _ _) (OddPrimesWithRootsOfUnity.gram_posDef x g z.1) hr h1 h2 z.2
  rw [OddPrimesWithRootsOfUnity.eigMet_gram] at hg
  have e : lnRatio (metsOf x Φ k none σ n) (refMet x Φ k σ n) p =
      lnRatio (C := cxSt D.what₂.LL) ((Φ.C k).met (x.hodge (embOf κ.e σ)) n)
        ((Φ.C k).met (OddPrimesWithRootsOfUnity.eigMet x (embOf κ.e σ)) n) p := rfl
  rw [e, hg]
  have hs : |∑ z : Pad.Letter S.Dw, (n z : ℝ) * (Real.log (grSq ((x.hodge (embOf κ.e σ)).gram ((Φ.C k).down p) g z.1) z.2) -
      Real.log (grSq (OddPrimesWithRootsOfUnity.gram x ((Φ.C k).down p) g z.1) z.2))| ≤
      (∑ z : Pad.Letter S.Dw, |(n z : ℝ)|) * (C * Real.log (rFlag x Φ k σ p)) := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (key z) (abs_nonneg _)
  rw [abs_div, abs_two, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hs zero_le_two

end FinalTheorems

open GlobalTheory.Mean4O in

theorem abs_ph_le_log : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c, ∃ C : ℝ, ∀ u σ x, x ∉ (T.M c).Z σ →
    |(T.F c).ph u σ x| ≤ C * ‖u‖ * Real.log ((T.M c).r σ x) := by
  intro _ _ D O hO _ A T H h c
  obtain ⟨xa, P, hc⟩ := hO
  have an := h.an c
  obtain ⟨C₀, hC⟩ := xa.exists_isMuExp
  refine ⟨(∑ y : DV.Rt D.what₂.Tau O.N, (∑ z : Pad.Letter O.S.Dw, |(O.ex y z : ℝ)|) / 2) * C₀, fun u σ z hz => ?_⟩
  have hz' := (an.Z σ z).not.1 hz
  rw [an.ph u σ z hz, an.r σ z hz]
  generalize (h.man c).pt σ z = p at hz' ⊢
  have hr : 0 ≤ Real.log (O.met.r c ((h.man c).ε σ) p) :=
    Real.log_nonneg ((Real.add_one_le_exp 1).trans' (by norm_num) |>.trans (hc.r_eq ▸ exp_le_rFlag))
  have hL : ∀ y : DV.Rt D.what₂.Tau O.N, |lnRatio (O.met.hm c none ((h.man c).ε σ) (O.ex y)) (O.met.h0 c ((h.man c).ε σ) (O.ex y)) p| ≤
      (∑ z : Pad.Letter O.S.Dw, |(O.ex y z : ℝ)|) / 2 * (C₀ * Real.log (O.met.r c ((h.man c).ε σ) p)) := fun y => by
    rw [hc.hm_eq, hc.h0_eq, hc.r_eq]
    exact abs_lnRatio_le xa O.Φ hC c ((h.man c).ε σ) (O.ex y) p hz'
  have hu : ∀ y : DV.Rt D.what₂.Tau O.N, |u y.1 y.2| ≤ ‖u‖ := fun y => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (u y.1) y.2).trans (norm_le_pi_norm u y.1)
  have hK : ∀ y : DV.Rt D.what₂.Tau O.N, 0 ≤ (∑ z : Pad.Letter O.S.Dw, |(O.ex y z : ℝ)|) / 2 * (C₀ * Real.log (O.met.r c ((h.man c).ε σ) p)) :=
    fun y => mul_nonneg (div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) zero_le_two) (mul_nonneg hC.1 hr)
  unfold Setup.chg
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ y : DV.Rt D.what₂.Tau O.N, |u y.1 y.2 * lnRatio (O.met.hm c none ((h.man c).ε σ) (O.ex y)) (O.met.h0 c ((h.man c).ε σ) (O.ex y)) p|
      ≤ ∑ y : DV.Rt D.what₂.Tau O.N, ‖u‖ * ((∑ z : Pad.Letter O.S.Dw, |(O.ex y z : ℝ)|) / 2 * (C₀ * Real.log (O.met.r c ((h.man c).ε σ) p))) :=
        Finset.sum_le_sum fun y _ => by
          rw [abs_mul]
          exact mul_le_mul (hu y) (hL y) (abs_nonneg _) (norm_nonneg _)
    _ = (∑ y : DV.Rt D.what₂.Tau O.N, (∑ z : Pad.Letter O.S.Dw, |(O.ex y z : ℝ)|) / 2) * C₀ * ‖u‖ *
          Real.log (O.met.r c ((h.man c).ε σ) p) := by
        rw [← Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring

end GlobalTheory.HodgeLogBd
