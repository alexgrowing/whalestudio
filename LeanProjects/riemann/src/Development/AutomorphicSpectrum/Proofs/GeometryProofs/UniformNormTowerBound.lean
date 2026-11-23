import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AevalMemWeightZeroSections
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentNormConstantModelsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZeroStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginComponentSectionsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodEmbeddingComponentSectionsStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnReadingIntegerExponentSection
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealRpowNegLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.Arch

section Pt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_comp_hom (ψ : Ω →+* ℂ) (y : (Σ k, ι k) → Ω) (g : MRing ι) :
    aeval (fun p => ψ (y p)) g = ψ (aeval y g) :=
  (DFunLike.congr_fun (comp_aeval y ψ.toIntAlgHom) g).symm

theorem eq_of_hasVal {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {ψ : Ω →+* ℂ} {w : ℂ}
    (h : Small.HasVal y a s (fun p => ψ (y p)) w) : w = ψ s := by
  obtain ⟨dg, dh, g, hh, -, -, -, e1, e2, e3⟩ := h
  rw [aeval_comp_hom] at e2 e3
  rw [aeval_comp_hom, e1, map_mul] at e3
  exact (mul_right_cancel₀ e2 e3).symm

theorem aeval_ne_zero (y : (Σ k, ι k) → Ω) {u : MRing ι} (h : Small.IsFormOff (mCoordIdeal y) u) (ψ : Ω →+* ℂ) :
    aeval (fun p => ψ (y p)) u ≠ 0 := by
  obtain ⟨⟨d, hd⟩, hu⟩ := h
  rw [aeval_comp_hom]
  intro h0
  refine hu ?_
  show mConeMap y u = 0
  rw [GlobalTheory.CompanionTheory.Ar.Plug.Test.cone_form y hd, (map_eq_zero ψ).1 h0, map_zero, mul_zero]

theorem mem_mcPts (y : (Σ k, ι k) → Ω) (hr : IsRelevant (mCoordIdeal y)) (ψ : Ω →+* ℂ) :
    (fun p => ψ (y p)) ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hr k
    refine ⟨i, fun h0 => hi ?_⟩
    have : y ⟨k, i⟩ = 0 := (map_eq_zero ψ).1 h0
    simp [mCoordIdeal, RingHom.mem_ker, mConeMap, this]
  · rw [eval_map]
    exact (aeval_comp_hom ψ y f).trans (by rw [GlobalTheory.CompanionTheory.Ar.Plug.Test.aeval_of_mem y hf, map_zero])

theorem hasVal_hom (y : (Σ k, ι k) → Ω) (hb : Birational y) (hr : IsRelevant (mCoordIdeal y)) (a : K → ℤ) (s : Ω)
    (ψ : Ω →+* ℂ) : Small.HasVal y a s (fun p => ψ (y p)) (ψ s) := by
  classical
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hr k
    refine ⟨i, fun h0 => hi ?_⟩
    simp [mCoordIdeal, RingHom.mem_ker, mConeMap, h0]
  choose ci hci using hy
  have hm : ∀ e : K → ℕ, aeval y (xpow ci e) ≠ 0 := fun e => by
    simp only [xpow, map_prod, map_pow, aeval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hci k)
  set ep : K → ℕ := fun k => (a k).toNat with hep
  set em : K → ℕ := fun k => (-a k).toNat with hem
  obtain ⟨d, g, h, hg, hh, h0, h1⟩ := hb (s * aeval y (xpow ci em) / aeval y (xpow ci ep))
  have hG := isMultiHomog_mul hg (isMultiHomog_xpow ci ep)
  have hH := isMultiHomog_mul hh (isMultiHomog_xpow ci em)
  have hHy : aeval y (h * xpow ci em) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero h0 (hm em)
  have e1 : aeval y (g * xpow ci ep) = s * aeval y (h * xpow ci em) := by
    rw [map_mul, map_mul, h1]
    have := hm ep
    field_simp
  refine ⟨d + ep, d + em, g * xpow ci ep, h * xpow ci em, hG, hH, fun k => ?_, e1, ?_, ?_⟩
  · simp only [Pi.add_apply, hep, hem]
    push_cast
    have h2 := Int.toNat_sub_toNat_neg (a k)
    omega
  · rw [aeval_comp_hom]; exact (map_ne_zero ψ).2 hHy
  · rw [aeval_comp_hom, aeval_comp_hom, e1, map_mul]

end Pt

end GlobalTheory.CompanionTheory.Ar.Plug.Arch

namespace GlobalTheory.CompanionTheory.Ar.Plug.Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

omit [NumberField E] [IsCMField E] in
theorem even_nsmul' {G : WTZ E} (hG : Even G.2) (n : ℕ) : Even (n • G).2 := by
  rw [Prod.smul_snd, nsmul_eq_mul]; exact hG.mul_left n

theorem homN_pow_mul' {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (x : ℝ) {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2)
    (θ f : Rul Xo c) {z : Σ k, Frame (V.X k).Ψ r} (hz : z.2 ∈ (V.X z.1).dom) (n : ℕ) :
    GlobalTheory.AllWt.homN V x (n • G + G') (θ ^ n * f) z = GlobalTheory.AllWt.homN V x G θ z ^ n * GlobalTheory.AllWt.homN V x G' f z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul', add_assoc, pow_succ', mul_assoc,
      GlobalTheory.AllWt.homN_mul V x hG ((even_nsmul' hG n).add hG') _ _ z hz, ih]
    ring

theorem homN_nat_eq {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (hσ : GoodEmb c σ) (hV : IsUnf V) (x : ℝ)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n) {g : Rul Xo c} (hg : g ∈ sec Xo c a n) {G : WTZ E}
    (hG : exZ Dw (wtZ a n) = exZ Dw G) {k : V.Comp} {x₁ : Frame (V.X k).Ψ r} (hx₁ : x₁ ∈ (V.X k).dom)
    {γ : GL (Fin r) E} (hγ : γ ∈ (V.X k).Γ) {b : Frame (V.X k).Ψ r} (hb : b ∈ Bor (V.X k).Ψ r) :
    GlobalTheory.AllWt.homN V x G g ⟨k, rmul (lact γ x₁) b⟩ = GlobalTheory.AllWt.homN V x G g ⟨k, x₁⟩ := by
  have hsec := hV.2.2.2.2.1 a n hd g hg k
  have hm : GlobalTheory.AllWt.modelWt V G k = laU V a n k := by
    rw [← GlobalTheory.AllWt.modelWt_congr V hσ hV hG, GlobalTheory.AllWt.modelWt_wtZ]
  have hl : lact γ x₁ ∈ (V.X k).dom := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact _ hγ hx₁
  show _ * (V.X k).pnorm _ _ _ = _ * (V.X k).pnorm _ _ _
  rw [hm, GlobalTheory.Up.DivMetricPf.pnorm_rmul ReciprocityTheory.ChartRestriction.G.AR.Inst.normFactor_rightBorel_holds hsec hl hb,
    GlobalTheory.Up.DivMetricPf.pnorm_lact ReciprocityTheory.ChartRestriction.G.AR.Inst.normFactor_leftAction_holds hsec hγ hx₁]

theorem homN_eq_of_frBor {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q)
    (x : ℝ) (u : GlobalTheory.AllWt.Weight Dw) {f : Rul Xo c}
    (hf : f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0)) (k : U.Comp) (x₁ x₂ : (U.X k).dom)
    (t : Ix Dw → (CAt σ)ˣ) (hb : FrBor t (U.un k x₁) (U.un k x₂)) :
    GlobalTheory.AllWt.homN U x (GlobalTheory.AllWt.wtOf Dw u 0) f ⟨k, x₂.1⟩ = GlobalTheory.AllWt.homN U x (GlobalTheory.AllWt.wtOf Dw u 0) f ⟨k, x₁.1⟩ := by
  have hnone : GlobalTheory.AllWt.exOf Dw u 0 none = 0 := by
    show (GlobalTheory.AllWt.wtOf Dw u 0).2 = 0
    rw [GlobalTheory.AllWt.wtOf_snd, mul_zero]
  by_cases hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j →
      GlobalTheory.AllWt.exOf Dw u 0 (some ⟨τ, j⟩) ≤ GlobalTheory.AllWt.exOf Dw u 0 (some ⟨τ, i⟩)
  · obtain ⟨γ, hγ, b, hb', e⟩ := (hU.2.2.2.1 k k x₁ x₂).1 ⟨t, hb⟩
    have e' : x₂.1 = rmul (lact γ x₁.1) b := eq_of_heq (Sigma.mk.inj_iff.1 e).2
    have hx₂ : rmul (lact γ x₁.1) b ∈ (U.X k).dom := e' ▸ x₂.2
    obtain ⟨n, hn, g, hg, hg0⟩ := GlobalTheory.TrueCx.FlatConst.exists_sec_four hpq (U.un k x₁)
    set e₀ := GlobalTheory.AllWt.exOf Dw u 0 with he₀
    set M : ℕ := ∑ i : Ix Dw, (e₀ i).natAbs with hMdef
    have hM : ∀ i, -(4 * ((M + 1 : ℕ) : ℤ)) ≤ e₀ i := fun i => by
      have h1 : (e₀ i).natAbs ≤ M := Finset.single_le_sum (f := fun i => (e₀ i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
      have h2 : -((e₀ i).natAbs : ℤ) ≤ e₀ i := by
        have := Int.natAbs_abs (e₀ i); rw [← Int.abs_eq_natAbs]; exact neg_abs_le _
      have h3 : ((e₀ i).natAbs : ℤ) ≤ M := by exact_mod_cast h1
      push_cast; linarith
    let a : (E →+* ℂ) × ℕ → ℕ := fun p =>
      if h : p.2 < Dw.mult p.1 then (4 * ((M + 1 : ℕ) : ℤ) + e₀ (some ⟨p.1, ⟨p.2, h⟩⟩)).toNat else 0
    have hdom : Dom a ((M + 1) * n) := by
      refine ⟨fun τ i j hij => ?_, hn.mul_left _⟩
      show a (τ, j) ≤ a (τ, i)
      simp only [a]
      by_cases hj : j < Dw.mult τ
      · have hi : i < Dw.mult τ := lt_of_le_of_lt hij hj
        rw [dif_pos hj, dif_pos hi]
        exact Int.toNat_le_toNat (by linarith [hanti τ ⟨i, hi⟩ ⟨j, hj⟩ hij])
      · rw [dif_neg hj]; exact Nat.zero_le _
    have hgp := GlobalTheory.ReadCont.pow_succ_mem_secZ (Xo := Xo) (c := c) (by rw [GlobalTheory.AllWt.secZ_nat]; exact hg) M
    have hex : (fun i => (ex Dw a ((M + 1) * n) i : ℤ)) =
        (M + 1) • (fun i => (ex Dw (fun _ => 4) n i : ℤ)) + e₀ := by
      funext i
      rcases i with _ | ⟨τ, i⟩
      · simp [ex, hnone]
      · have hi := i.2
        rw [Pi.add_apply, Pi.smul_apply]
        simp only [ex, a, dif_pos hi, nsmul_eq_mul]
        rw [Int.toNat_of_nonneg (by linarith [hM (some ⟨τ, i⟩)])]
        push_cast
        ring
    have hgf : g ^ (M + 1) * f ∈ sec Xo c a ((M + 1) * n) := by
      rw [← GlobalTheory.AllWt.secZ_nat, hex]
      exact GlobalTheory.AllWt.mul_mem_secZ hgp hf
    set Gg : WTZ E := wtZ (fun _ => 4) n with hGg
    have hEg : Even Gg.2 := by simpa [hGg, wtZ] using hn
    have hEG := GlobalTheory.AllWt.even_wtOf (Dw := Dw) u 0
    have hexG : exZ Dw (wtZ a ((M + 1) * n)) = exZ Dw ((M + 1) • Gg + GlobalTheory.AllWt.wtOf Dw u 0) := by
      rw [GlobalTheory.AllWt.exZ_wtZ, hex]
      funext i
      rw [Formalism.L2.Pj.exZ_add, Pi.add_apply]
      congr 1
      rcases i with _ | ⟨τ, i⟩ <;> simp [Formalism.L2.Pj.exZ, hGg, wtZ, ex]
    have h1 := homN_nat_eq (x := x) U hσ hU hdom hgf hexG x₁.2 hγ hb'
    have h2 := homN_nat_eq (x := x) U hσ hU (a := fun _ => 4) (n := n) ⟨fun _ _ _ _ => le_rfl, hn⟩ hg
      (G := Gg) rfl x₁.2 hγ hb'
    rw [homN_pow_mul' U x hEg hEG g f (z := ⟨k, rmul (lact γ x₁.1) b⟩) hx₂,
      homN_pow_mul' U x hEg hEG g f (z := ⟨k, x₁.1⟩) x₁.2, h2] at h1
    have hA : 0 < GlobalTheory.AllWt.homN U x Gg g ⟨k, x₁.1⟩ := by
      have hr : rdU U g k x₁.1 ≠ 0 := by
        have : rdU U g k x₁.1 = toC (evR Xo c g (U.un k x₁)) := dif_pos x₁.2
        rwa [this]
      show 0 < _ * (‖rdU U g k x₁.1‖ * _)
      exact mul_pos (GlobalTheory.AllWt.lieFacZ_pos _ _) (mul_pos (norm_pos_iff.2 hr) (ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.nfac_pos _ x₁.2 _))
    rw [e']
    exact mul_left_cancel₀ (pow_pos hA _).ne' h1
  · push_neg at hanti
    obtain ⟨τ, i, j, hij, hlt⟩ := hanti
    have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
    have h0 := GlobalTheory.T.integerExponentSection_eq_zero_of_increasing_flag E H Dw l Xo c _ τ i j hij' hlt f hf
    subst h0
    simp [GlobalTheory.AllWt.homN, GlobalTheory.AllWt.ptN, Data.pnorm]

theorem continuousOn_homN {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q)
    (x : ℝ) (u : GlobalTheory.AllWt.Weight Dw) {f : Rul Xo c}
    (hf : f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0)) (k : U.Comp) :
    ContinuousOn (fun y => GlobalTheory.AllWt.homN U x (GlobalTheory.AllWt.wtOf Dw u 0) f ⟨k, y⟩) (U.X k).dom := by
  have hnone : GlobalTheory.AllWt.exOf Dw u 0 none = 0 := by
    show (GlobalTheory.AllWt.wtOf Dw u 0).2 = 0
    rw [GlobalTheory.AllWt.wtOf_snd, mul_zero]
  have hc : ContinuousOn (rdU U f k) (U.X k).dom := by
    by_cases hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j →
        GlobalTheory.AllWt.exOf Dw u 0 (some ⟨τ, j⟩) ≤ GlobalTheory.AllWt.exOf Dw u 0 (some ⟨τ, i⟩)
    · exact (GlobalTheory.ReadCont.differentiableOn_rdU_of_antitone hU hpq hnone hanti hf k).continuousOn
    · push_neg at hanti
      obtain ⟨τ, i, j, hij, hlt⟩ := hanti
      have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
      rw [GlobalTheory.T.integerExponentSection_eq_zero_of_increasing_flag E H Dw l Xo c _ τ i j hij' hlt f hf, map_zero]
      exact continuousOn_const
  have h2 : ContinuousOn (fun y => GlobalTheory.AllWt.lieFacZ Dw x (GlobalTheory.AllWt.wtOf Dw u 0) * (‖rdU U f k y‖ *
      (U.X k).nfac (GlobalTheory.AllWt.modelWt U (GlobalTheory.AllWt.wtOf Dw u 0) k) y)) (U.X k).dom :=
    continuousOn_const.mul (hc.norm.mul (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.nfac_contOn _ _))
  exact h2

end GlobalTheory.CompanionTheory.Ar.Plug.Arch

namespace GlobalTheory.CompanionTheory.Ar.Plug.Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def nA (Dw : Datum H) (a : WZ E) : Option (RootIx Dw) → ℤ
  | some ρ => -(if (ρ.2 : ℕ) < Dw.p then a (ρ.1.1, ρ.2) else -a (conjEmb ρ.1.1, Dw.p + Dw.q - 1 - ρ.2))
  | none => 0

theorem nA_coef (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (a : WZ E) (j : Option (RootIx Dw)) :
    (nA Dw a j : ℝ) = RM.coef (towerWt Dw a) 0 j := by
  rcases j with _ | ρ
  · simp [nA, Top.RootModel.coef]
  · simp only [nA, Top.RootModel.coef, towerWt]
    split_ifs <;> simp

theorem modelWt_eq_laZ {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (u : GlobalTheory.AllWt.Weight Dw) (k : V.Comp) :
    GlobalTheory.AllWt.modelWt V (GlobalTheory.AllWt.wtOf Dw u 0) k = laZ V (GlobalTheory.AllWt.wtOf Dw u 0).1 k := by
  funext τ j
  simp only [GlobalTheory.AllWt.modelWt, laZ, GlobalTheory.AllWt.wtOf_snd]
  split_ifs <;> simp

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c}
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {SS : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y SS RM Fx}

theorem exists_frame_of_hom [DecidableEq (CMType H)] (hG : Top.Given) (hL : CompLaws U h e) (x : ℝ)
    (hx : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x)
    (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw) {f : Rul Xo c}
    (hf : f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0)) :
    ∃ uu : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) uu ∧ ∀ {σ : c.F →+* ℂ}, GoodEmb c σ → ∀ k, Over (U σ) (e Z) k →
      ∀ ψ : RM.Ω →+* ℂ, (∀ t, ψ (Or.𝔐.cst t) = σ t) → ∃ y' ∈ ((U σ).X k).dom,
        (∀ a : WZ E, ∃ w : ℂ, w ≠ 0 ∧ ∀ g ∈ Rec.secZ Xo c a, rdU (U σ) g k y' = w * ψ (Rd.φ (evC h Z g))) ∧
        (∏ ρ, (Or.sing ρ).h (fun p => ψ (RM.y p)) ^ nOf u (some ρ)) *
            GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f ⟨k, y'⟩ =
          ‖ψ (gauge Rd u)‖ * ‖ψ (Rd.φ (evC h Z f))‖ := by
  obtain ⟨uu, huu, hread⟩ := GlobalTheory.T.component_norm_constant_models hG E H Dw l Xo c r U h e hL x hx O β Y SS RM Sys Fx Or Fr Z Rd
  refine ⟨uu, huu, fun {σ} hσ k hk ψ hψ => ?_⟩
  have hz := mem_mcPts RM.y RM.arith.2.1.2.2 ψ
  have hv : ∀ t, Small.HasVal RM.y 0 (Or.𝔐.cst t) (fun p => ψ (RM.y p)) (σ t) := fun t => by
    rw [← hψ]
    exact hasVal_hom RM.y RM.birational RM.arith.2.1.2.2 0 _ ψ
  have h0 := hread σ _ hz hv (aeval_ne_zero RM.y huu ψ)
  rw [show goodOf c σ = σ from if_pos hσ] at h0
  obtain ⟨k', hk', y', hy', hall⟩ := h0
  obtain rfl : k' = k := GlobalTheory.CompanionTheory.Ar.Plug.ArchimedeanSections.over_unique hL hσ hk' hk
  have hpos : ∀ n' : Option (RootIx Dw) → ℤ, 0 < ∏ ρ, (Or.sing ρ).h (fun p => ψ (RM.y p)) ^ n' (some ρ) := fun n' =>
    Finset.prod_pos fun ρ _ => zpow_pos ((Or.sing ρ).pos _ hz.1) _
  have hnf : ∀ la, ((U σ).X k').pnorm la (fun _ => 1) y' = ((U σ).X k').nfac la y' := fun la => by
    show ‖(1 : ℂ)‖ * _ = _
    rw [norm_one, one_mul]
    rfl
  refine ⟨y', hy', fun a => ?_, ?_⟩
  · obtain ⟨θ, hθ, hθf⟩ := hall a (nA Dw a) (nA_coef RM a)
    have hθ0 : θ ≠ 0 := by
      rw [← norm_pos_iff, hθ, hnf]
      exact mul_pos (mul_pos (hpos _) (Real.exp_pos _)) (ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.nfac_pos _ hy' _)
    have hT : ((∏ i, Rd.t i ^ Rec.exZ Dw a i : (RM.Ω)ˣ) : RM.Ω) * ∏ ρ, Or.e ρ ^ (-nA Dw a (some ρ)) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Finset.prod_ne_zero_iff.2 fun ρ _ => zpow_ne_zero _ (Or.lines ρ).1)
    refine ⟨ψ (((∏ i, Rd.t i ^ Rec.exZ Dw a i : (RM.Ω)ˣ) : RM.Ω) * ∏ ρ, Or.e ρ ^ (-nA Dw a (some ρ))) / θ,
      div_ne_zero ((map_ne_zero ψ).2 hT) hθ0, fun g hg => ?_⟩
    have e1 := eq_of_hasVal ((hθf g hg).1 hσ)
    rw [Rd.rd_eq a g hg] at e1
    rw [div_mul_eq_mul_div, eq_div_iff hθ0, mul_comm (rdU (U σ) g k' y'), e1, map_mul, map_mul, map_mul]
    ring
  · obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c RM u
    obtain ⟨θ, hθ, hθf⟩ := hall (GlobalTheory.AllWt.wtOf Dw u 0).1 (nOf u) (fun j => by rw [h1]; exact h4 j)
    have hf' : f ∈ Rec.secZ Xo c (GlobalTheory.AllWt.wtOf Dw u 0).1 := GlobalTheory.CompanionTheory.Ar.Plug.Test.secZ_eq u ▸ hf
    have e1 := eq_of_hasVal ((hθf f hf').1 hσ)
    rw [← GlobalTheory.CompanionTheory.Ar.Plug.Test.gauge_mul Rd u hf, map_mul] at e1
    have e2 := congrArg norm e1
    rw [norm_mul, norm_mul, hθ, hnf] at e2
    rw [← e2]
    show _ * (GlobalTheory.AllWt.lieFacZ Dw x (GlobalTheory.AllWt.wtOf Dw u 0) * (‖rdU (U σ) f k' y'‖ *
      ((U σ).X k').nfac (GlobalTheory.AllWt.modelWt (U σ) (GlobalTheory.AllWt.wtOf Dw u 0) k') y')) = _
    rw [modelWt_eq_laZ]
    show _ = _ * Rec.lieFacZ Dw x (GlobalTheory.AllWt.wtOf Dw u 0).1 * _ * _
    have : GlobalTheory.AllWt.lieFacZ Dw x (GlobalTheory.AllWt.wtOf Dw u 0) = Rec.lieFacZ Dw x (GlobalTheory.AllWt.wtOf Dw u 0).1 := rfl
    rw [this]
    ring

end GlobalTheory.CompanionTheory.Ar.Plug.Arch

namespace GlobalTheory.CompanionTheory.Ar.Plug.Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c}
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {SS : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y SS RM Fx}

theorem bound_at_frame [DecidableEq (CMType H)] (hG : Top.Given) (hL : CompLaws U h e) (x : ℝ)
    (hx : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) (hpq : 1 ≤ Dw.p + Dw.q)
    (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw) (s : RM.Ω) (R : ℝ)
    (hR : 0 ≤ R) (hH : HodgeLe Or u s R) {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0))
    (hev : evC h Z f = trOf Rd u s) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {k : (U σ).Comp} (hk : Over (U σ) (e Z) k)
    (x₀ : ((U σ).X k).dom) (φ : Om Z →ₐ[c.F] CAt σ)
    (hsep : ∀ y : ((U σ).X k).dom, (∀ a : WZ E, ∃ w : ℂ, w ≠ 0 ∧ ∀ g ∈ Rec.secZ Xo c a,
      rdU (U σ) g k y.1 = w * toC (φ (evC h Z g))) → ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t ((U σ).un k x₀) ((U σ).un k y)) :
    GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f ⟨k, x₀.1⟩ ≤ Or.Fl.deg * R := by
  obtain ⟨uu, huu, hfr⟩ := exists_frame_of_hom hG hL x hx Fr Z Rd u hf
  obtain ⟨w, hw, hle⟩ := hH
  letI := Rd.φ.toAlgebra
  let φc : Om Z →+* ℂ := φ.toRingHom
  letI : Algebra (Om Z) ℂ := φc.toAlgebra
  haveI : CharZero (Om Z) := (RingHom.charZero_iff φc.injective).2 inferInstance
  have hdpos := GlobalTheory.CompanionTheory.Ar.Plug.Test.deg_pos Or
  haveI : Module.Finite (Om Z) RM.Ω := Module.finite_of_finrank_pos (by
    have := Rd.deg
    omega)
  set N := GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f ⟨k, x₀.1⟩ with hN
  set A := ‖φc (evC h Z f)‖ with hA
  have hN0 : 0 ≤ N := GlobalTheory.AllWt.homN_nonneg _ _ _ _ _
  have hmain : ∀ ψ : RM.Ω →ₐ[Om Z] ℂ, N * ‖ψ (s / gauge Rd u)‖ ≤ R * A ∧ (A = 0 → N = 0) := by
    intro ψ
    let ψr : RM.Ω →+* ℂ := ψ.toRingHom
    have hcomp : ∀ a, ψr (Rd.φ a) = φc a := fun a => ψ.commutes a
    have hcst : ∀ t, ψr (Or.𝔐.cst t) = σ t := fun t => by
      rw [← Rd.φ_cst t, hcomp]
      exact φ.commutes t
    obtain ⟨y', hy', hpr, heq⟩ := hfr hσ k hk ψr hcst
    obtain ⟨t, ht⟩ := hsep ⟨y', hy'⟩ fun a => by
      obtain ⟨w', hw', hg⟩ := hpr a
      exact ⟨w', hw', fun g hg' => (hg g hg').trans (by rw [hcomp]; rfl)⟩
    have hNy := homN_eq_of_frBor (U σ) hσ (hL.unf σ hσ) hpq x u hf k x₀ ⟨y', hy'⟩ t ht
    rw [hNy, hcomp, ← hN, ← hA] at heq
    have hz := mem_mcPts RM.y RM.arith.2.1.2.2 ψr
    have hHp : 0 < ∏ ρ, (Or.sing ρ).h (fun p => ψr (RM.y p)) ^ nOf u (some ρ) :=
      Finset.prod_pos fun ρ _ => zpow_pos ((Or.sing ρ).pos _ hz.1) _
    have hs := hle _ hz (aeval_ne_zero RM.y hw ψr) (ψr s)
      (hasVal_hom RM.y RM.birational RM.arith.2.1.2.2 _ s ψr)
    have hg0 : ψr (gauge Rd u) ≠ 0 := (map_ne_zero ψr).2 (GlobalTheory.CompanionTheory.Ar.Plug.Test.gauge_ne_zero Rd u)
    have hgp : 0 < ‖ψr (gauge Rd u)‖ := norm_pos_iff.2 hg0
    generalize (∏ ρ, (Or.sing ρ).h (fun p => ψr (RM.y p)) ^ nOf u (some ρ)) = Hp at *
    refine ⟨?_, fun hA0 => ?_⟩
    · have e1 : ‖ψ (s / gauge Rd u)‖ = ‖ψr s‖ / ‖ψr (gauge Rd u)‖ := by
        rw [← norm_div, ← map_div₀]
        rfl
      rw [e1, mul_div_assoc', div_le_iff₀ hgp]
      calc N * ‖ψr s‖ ≤ N * (R * Hp) := mul_le_mul_of_nonneg_left hs hN0
        _ = R * (Hp * N) := by ring
        _ = R * A * ‖ψr (gauge Rd u)‖ := by rw [heq]; ring
    · rw [hA0, mul_zero] at heq
      exact (mul_eq_zero.1 heq).resolve_left hHp.ne'
  have htr : φc (evC h Z f) = ∑ ψ : RM.Ω →ₐ[Om Z] ℂ, ψ (s / gauge Rd u) := by
    rw [hev]
    exact trace_eq_sum_embeddings ℂ
  have hcard : Fintype.card (RM.Ω →ₐ[Om Z] ℂ) = Or.Fl.deg := (AlgHom.card (Om Z) RM.Ω ℂ).trans Rd.deg
  have hsum : N * A ≤ Or.Fl.deg * R * A := by
    calc N * A ≤ N * ∑ ψ : RM.Ω →ₐ[Om Z] ℂ, ‖ψ (s / gauge Rd u)‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hN0
          rw [hA, htr]
          exact norm_sum_le _ _
      _ = ∑ ψ : RM.Ω →ₐ[Om Z] ℂ, N * ‖ψ (s / gauge Rd u)‖ := Finset.mul_sum _ _ _
      _ ≤ ∑ _ψ : RM.Ω →ₐ[Om Z] ℂ, R * A := Finset.sum_le_sum fun ψ _ => (hmain ψ).1
      _ = Or.Fl.deg * R * A := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
          ring
  rcases (norm_nonneg (φc (evC h Z f))).eq_or_lt with h0 | h0
  · have hne : Nonempty (RM.Ω →ₐ[Om Z] ℂ) := Fintype.card_pos_iff.1 (hcard ▸ hdpos)
    obtain ⟨ψ⟩ := hne
    rw [(hmain ψ).2 h0.symm]
    positivity
  · exact le_of_mul_le_mul_right hsum h0

end GlobalTheory.CompanionTheory.Ar.Plug.Arch

namespace GlobalTheory.CompanionTheory.Ar.Plug

open GlobalTheory.CompanionTheory.Ar.Plug.Arch in

theorem vs_arch : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw) (s : (T.M B b).Ω) (R : ℝ), 0 ≤ R → HodgeLe (o.toTowerOrigin.Or B b) u s R → ∀ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), evC h Z f = trOf Rd u s → ∀ σ, GoodEmb c σ → ∀ z ∈ GlobalTheory.AllWt.framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f z ≤ (o.toTowerOrigin.Or B b).Fl.deg * R := by
  intro hG E _ _ _ H Dw l Xo c r U h e hL x hx Y _ T o B b Fr Z Rd u s R hR hH f hf hev σ hσ z hz
  obtain ⟨k, y₀⟩ := z
  have hy₀ : y₀ ∈ ((U σ).X k).dom := hz.1
  have hk : Over (U σ) (e Z) k :=
    ((GlobalTheory.T.all_weight_sections_compat E H Dw l Xo c r U h e hL 0 Z).2.2.2.2 σ hσ k y₀ hy₀).1 hz
  have hU := hL.unf σ hσ
  have hpq : 1 ≤ Dw.p + Dw.q := by
    have h1 := T.j_pos
    have h2 := o.toTowerOrigin.j_eq
    omega
  obtain ⟨Z', S, hS, hg⟩ := GlobalTheory.GenericFrames.exists_comp_generic_off_meagre E H Dw l Xo c σ r (U σ) hσ hU h k
  have hd : Dense (⋂ n, (S n)ᶜ) :=
    dense_iInter_of_isOpen (fun n => (hS n).1.isOpen_compl) fun n => interior_eq_empty_iff_dense_compl.1 (hS n).2
  have ho : IsOpen ((U σ).X k).dom := FourierCoefficientDomain.isOpen_dom _
  have hbd : ∀ y ∈ ((U σ).X k).dom ∩ ⋂ n, (S n)ᶜ,
      GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f ⟨k, y⟩ ≤ (o.toTowerOrigin.Or B b).Fl.deg * R := by
    rintro y ⟨hy, hyS⟩
    obtain ⟨φ, y₁, t, hm, hb⟩ := hg ⟨y, hy⟩ fun n hn => Set.mem_iInter.1 hyS n hn
    obtain rfl : Z' = Z := by
      by_contra hne
      obtain ⟨w, hw0, hw⟩ := GlobalTheory.CompanionTheory.Ar.Plug.ArchimedeanSections.rdU_eq_of_reads' (U σ) h k Z' ⟨y, hy⟩ φ y₁ t hm hb 0 0
      have h1 := hw (e Z) (hL.e_sec Z)
      rw [hk y hy, (hL.e_val Z).2 Z' hne, map_zero, mul_one] at h1
      exact hw0 h1
    obtain ⟨a, N, g, hgs, hgb⟩ := GlobalTheory.T.good_origin_component_sections hG E H Dw l Xo c r U h e hL Y T o Z'
    exact bound_at_frame hG hL x hx hpq Fr Z' Rd u s R hR hH hf hev hσ hk ⟨y, hy⟩ φ fun y' hy' => by
      obtain ⟨w, hw, hwg⟩ := hy' a
      exact GlobalTheory.T.good_embedding_component_sections E H Dw l Xo c r U h e hL σ hσ Z' k hk a N g hgs hgb φ ⟨y, hy⟩ y' y₁ t hm hb w hw fun j => hwg _ (hgs j)
  have hcl : y₀ ∈ closure (((U σ).X k).dom ∩ ⋂ n, (S n)ᶜ) := hd.open_subset_closure_inter ho hy₀
  have hct : ContinuousAt (fun y => GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f ⟨k, y⟩) y₀ :=
    (continuousOn_homN (U σ) hU hpq x u hf k).continuousAt (ho.mem_nhds hy₀)
  haveI := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact le_of_tendsto (hct.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall hbd)

end GlobalTheory.CompanionTheory.Ar.Plug
