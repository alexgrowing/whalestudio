import Development.WeilBound.ThetaLifts.LatticeBasics.CuspLift
import Development.WeilBound.ThetaLifts.LatticeBasics.ConvOfCpt
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConst

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThKEnd (unipU IsCusp Perp)

structure OrthIn : Prop where
  sw : SWFull
  box : BoxSec
  dbl : DblW
  hgt : HgtEx
  int : HgtInt
  cpt : Stab2Cpt
  eis : EisContinues
  off : OffOpen
  emb : HtEmb
  unip : PositivityTheory.ThKEnd.Grp.UnipUGood
  line : PositivityTheory.ThKEnd.Grp.UnipLine
  all : CptAll
  top : PositivityTheory.ThKEst.GrpTop
  eps : PositivityTheory.ThKEst.EpsOf
  vol : PositivityTheory.ThKEst.FinVolU
  basic : ThetaBasic
  arch : PositivityTheory.ThKF.ArchOp
  conj : PositivityTheory.ThKF.CartanConj
  move : PositivityTheory.ThKF.CartanMove
  levi : LeviEx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χ χ' : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
private lemma exists_poly_height_bound_theta_of_min_eq_zero (I : OrthIn) (p : IsPair B M χ χ' om r s r' s') (h0 : min r s = 0) {Φ : Fn F n d}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ g h, ‖theta om Φ g h‖ ≤ C * (ht h : ℝ) ^ k := by
  obtain ⟨-, hinv, C, k, hb⟩ := (I.basic F E σ B n d X W M χ χ' om r s r' s' p).1 Φ hΦ
  have hcpt : Cpt σ X.J := I.all F E σ B n X r s p.base (Or.inl p.herm) h0
  obtain ⟨Ω, hΩ, hcov⟩ := hcpt.cov
  have hepsX := (I.eps F E σ B p.base n X r s (Or.inl p.herm)).1
  obtain ⟨C₀, hC₀⟩ := (I.top F E σ p.base.cm n X.J hepsX).2.2.2.2.2.2.2 Ω hΩ
  refine ⟨|C| * (C₀ : ℝ) ^ k, k, by positivity, fun g h => ?_⟩
  obtain ⟨γ, hγ, hγΩ⟩ := hcov g
  have e1 : theta om Φ g h = theta om Φ (γ * g) h := by
    have h3 := hinv γ hγ 1 (one_mem _) g h
    rw [one_mul] at h3
    exact h3.symm
  have h4 : (ht (γ * g) : ℝ) ≤ C₀ := by exact_mod_cast hC₀ _ hγΩ
  rw [e1]
  calc ‖theta om Φ (γ * g) h‖ ≤ C * ((ht (γ * g) : ℝ) * (ht h : ℝ)) ^ k := hb _ _
    _ ≤ |C| * ((ht (γ * g) : ℝ) * (ht h : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((C₀ : ℝ) * (ht h : ℝ)) ^ k := by gcongr
    _ = |C| * (C₀ : ℝ) ^ k * (ht h : ℝ) ^ k := by rw [mul_pow, mul_assoc]

private lemma integral_integral_swap_of_bounded_continuous [SecondCountableTopology (UA σ W.J)] [SecondCountableTopology (UA σ X.J)]
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hfin : μ D < ⊤) (hfin2 : M.μ M.dom < ⊤)
    {f : UA σ W.J → UA σ X.J → ℂ} (hf : Continuous (Function.uncurry f)) {C : ℝ}
    (hC : ∀ h g, ‖f h g‖ ≤ C) :
    ∫ h in D, ∫ g in M.dom, f h g ∂M.μ ∂μ = ∫ g in M.dom, ∫ h in D, f h g ∂μ ∂M.μ := by
  have : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin2⟩
  have : SFinite (μ.restrict D) := GlobalTheory.ThK.Dbl.sfin _
  have : SFinite (M.μ.restrict M.dom) := GlobalTheory.ThK.Dbl.sfin _
  apply MeasureTheory.integral_integral_swap
  exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => hC q.1 q.2)

theorem cusp_lift (I : OrthIn) (p : IsPair B M χ χ' om r s r' s') (h0 : min r s = 0) (hn : 1 ≤ n) (hd : 1 ≤ d)
    {φ : UA σ W.J → ℂ} (hφ : IsRapid φ) (hc : IsCusp W φ) {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ W.J) D μ) {Φ₂ : Fn F n d} (h2 : Φ₂ ∈ PolData B M)
    (hth : ∀ g, th om μ D φ Φ₂ g = th om μ D φ Φ₂ 1) (hne : ∫ h in D, M.I om Φ₂ h * starRingEnd ℂ (φ h) ∂μ ≠ 0)
    {Φ₁ : Fn F n d} (h1 : Φ₁ ∈ PolData B M) : IsCusp W (M.I om Φ₁) := by
  have hB := p.base
  have hskew := p.skew
  have hepsW := (I.eps F E σ B hB d W r' s' (Or.inr hskew)).1
  have htopW := I.top F E σ hB.cm d W.J hepsW
  have : LocallyCompactSpace (UA σ W.J) := htopW.1
  have : SecondCountableTopology (UA σ W.J) := htopW.2.1
  have : T2Space (UA σ W.J) := htopW.2.2.1
  have hepsX := (I.eps F E σ B hB n X r s (Or.inl p.herm)).1
  have htopX := I.top F E σ hB.cm n X.J hepsX
  have : SecondCountableTopology (UA σ X.J) := htopX.2.1
  have hcpt : Cpt σ X.J := I.all F E σ B n X r s hB (Or.inl p.herm) h0
  have hfinD : μ D < ⊤ := I.vol F E σ hB.cm d W.J hepsW μ D hμ hD
  have hfinX : M.μ M.dom < ⊤ := hcpt.fin M.μ M.dom p.good.haar p.good.dom
  obtain ⟨⟨K, a, hS, ha, ca, a0⟩, e, ce, he⟩ := I.hgt F E σ B d W r' s' hB (Or.inr hskew)
  obtain ⟨t₀, hi⟩ := I.int F E σ B d W r' s' hB (Or.inr hskew) K a e hS ha he μ hμ
  have hK := I.cpt F E σ B d W r' s' hB (Or.inr hskew) K hS
  obtain ⟨-, -, -, ht1⟩ := I.emb F E σ d W
  obtain ⟨dd, om₂, S, l, hdbl, hbox, hcoord, -⟩ := I.dbl F E σ B n d X W M χ χ' om r s r' s' p
  have hsch1 := GlobalTheory.ThK.Dbl.pol_sch p.good h1
  have hsch2 := GlobalTheory.ThK.Dbl.pol_sch p.good h2
  obtain ⟨U, Ê, hEis, hs₀, hval⟩ := I.sw F E σ B n d X W M r s r' s' hB hn hd p.herm h0 hskew p.good χ p.hX
    p.resX dd om₂ S l hcoord hdbl K a hS ha Φ₁ h1 Φ₂ h2
  have hsec := I.box F E σ B n d X W M r s r' s' hB hn hd p.herm h0 hskew p.good χ p.hX p.resX dd om₂ S l
    hcoord hdbl K a hS ha Φ₁ h1 Φ₂ h2
  have hcE := GlobalTheory.ThK.Dbl.ct_zero I.off I.unip I.eis I.emb hB hd hskew hepsW.2 htopW.2.2.2.2.2.2.2 p.hX he ce
    hS hK ha ca a0 hsec.cont hsec.law hEis hμ hD hfinD hi hφ hc _ hs₀
  obtain ⟨C₁, k₁, hC₁0, hb₁⟩ := exists_poly_height_bound_theta_of_min_eq_zero I p h0 hsch1
  obtain ⟨C₂, k₂, hC₂0, hb₂⟩ := exists_poly_height_bound_theta_of_min_eq_zero I p h0 hsch2
  obtain ⟨Mφ, hMφ0, hMφ⟩ := hφ.bound ht1 k₂
  have hbasic1 := (I.basic F E σ B n d X W M χ χ' om r s r' s' p).1 Φ₁ hsch1
  have hbasic2 := (I.basic F E σ B n d X W M χ χ' om r s r' s' p).1 Φ₂ hsch2
  have hθφ : ∀ g h', ‖theta om Φ₂ g h'‖ * ‖φ h'‖ ≤ C₂ * Mφ := fun g h' =>
    hMφ (fun h' => theta om Φ₂ g h') C₂ hC₂0 (fun γ hγ h'' => by
      have h3 := hbasic2.2.1 1 (one_mem _) γ hγ g h''
      rw [one_mul] at h3
      exact h3) (fun h'' => hb₂ g h'') h'
  have hc2 : ∀ g, ∫ h in D, theta om Φ₂ g h * starRingEnd ℂ (φ h) ∂μ
      = starRingEnd ℂ (th om μ D φ Φ₂ 1) := by
    intro g
    rw [← hth g]
    unfold GlobalTheory.ThK.Dbl.th GlobalTheory.ThK.Dbl.pet
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    beta_reduce
    rw [map_mul, starRingEnd_apply (star _), star_star, mul_comm]
  have hcont2 : Continuous (Function.uncurry fun (h : UA σ W.J) (g : UA σ X.J) =>
      theta om Φ₂ g h * starRingEnd ℂ (φ h)) := by
    show Continuous fun q : UA σ W.J × UA σ X.J => theta om Φ₂ q.2 q.1 * starRingEnd ℂ (φ q.1)
    exact (hbasic2.1.comp continuous_swap).mul (Complex.continuous_conj.comp (hφ.1.comp continuous_fst))
  have hbd2 : ∀ (h : UA σ W.J) (g : UA σ X.J), ‖theta om Φ₂ g h * starRingEnd ℂ (φ h)‖ ≤ C₂ * Mφ :=
    fun h g => by
      rw [norm_mul, RCLike.norm_conj]
      exact hθφ g h
  have hne' : ∫ h in D, M.I om Φ₂ h * starRingEnd ℂ (φ h) ∂μ
      = ((M.μ M.dom).toReal : ℂ) * starRingEnd ℂ (th om μ D φ Φ₂ 1) := by
    have e2 : ∀ h, M.I om Φ₂ h * starRingEnd ℂ (φ h)
        = ∫ g in M.dom, theta om Φ₂ g h * starRingEnd ℂ (φ h) ∂M.μ := fun h => by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.I
      rw [integral_mul_const]
    simp_rw [e2]
    rw [integral_integral_swap_of_bounded_continuous hfinD hfinX hcont2 hbd2]
    simp_rw [hc2]
    rw [setIntegral_const, Complex.real_smul]
    rfl
  have hv_th : ((M.μ M.dom).toReal : ℂ) ≠ 0 ∧ th om μ D φ Φ₂ 1 ≠ 0 := by
    have h5 := hne
    rw [hne'] at h5
    exact ⟨left_ne_zero_of_mul h5, fun h0' => h5 (by rw [h0', map_zero, mul_zero])⟩
  have hmain : ∀ h, ∫ h' in D, Ê ((↑n - ↑d) / 2) (e (h, h')) * detInv χ h' * φ h' ∂μ
      = (if d < n then (1 : ℂ) else 2) * ((M.μ M.dom).toReal : ℂ)⁻¹ * th om μ D φ Φ₂ 1 * M.I om Φ₁ h := by
    intro h
    have hpt : ∀ h' g, GlobalTheory.WeilM.thetaSum F ((om₂ (e (h, h'))) ((S g) (GlobalTheory.WeilM.boxFun Φ₁ (star Φ₂))))
        * detInv χ h' = theta om Φ₁ g h * star (theta om Φ₂ g h') := fun h' g => by
      rw [mul_comm]
      exact ((hbox Φ₁ hsch1 Φ₂ hsch2).2 g h h' _ (he h h')).1
    have e1 : ∀ h', Ê ((↑n - ↑d) / 2) (e (h, h')) * detInv χ h' * φ h'
        = (if d < n then (1 : ℂ) else 2) * ((M.μ M.dom).toReal : ℂ)⁻¹
          * ∫ g in M.dom, theta om Φ₁ g h * star (theta om Φ₂ g h') * φ h' ∂M.μ := by
      intro h'
      have e3 : ∫ g in M.dom, theta om Φ₁ g h * star (theta om Φ₂ g h') * φ h' ∂M.μ
          = (∫ g in M.dom, GlobalTheory.WeilM.thetaSum F ((om₂ (e (h, h'))) ((S g) (GlobalTheory.WeilM.boxFun Φ₁ (star Φ₂))))
            ∂M.μ) * detInv χ h' * φ h' := by
        rw [← integral_mul_const, ← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        beta_reduce
        rw [hpt h' g]
      have hr : M.μ.real M.dom = (M.μ M.dom).toReal := rfl
      rw [hval, MeasureTheory.setAverage_eq, Complex.real_smul, e3]
      try rw [hr]
      push_cast
      ring
    have hcont1 : Continuous (Function.uncurry fun (h' : UA σ W.J) (g : UA σ X.J) =>
        theta om Φ₁ g h * star (theta om Φ₂ g h') * φ h') := by
      show Continuous fun q : UA σ W.J × UA σ X.J => theta om Φ₁ q.2 h * star (theta om Φ₂ q.2 q.1) * φ q.1
      exact ((hbasic1.1.comp (continuous_snd.prodMk continuous_const)).mul
        ((hbasic2.1.comp continuous_swap).star)).mul (hφ.1.comp continuous_fst)
    have hbd1 : ∀ (h' : UA σ W.J) (g : UA σ X.J),
        ‖theta om Φ₁ g h * star (theta om Φ₂ g h') * φ h'‖ ≤ C₁ * (ht h : ℝ) ^ k₁ * (C₂ * Mφ) := by
      intro h' g
      rw [mul_assoc, norm_mul, norm_mul, norm_star]
      exact mul_le_mul (hb₁ g h) (hθφ g h') (by positivity) (mul_nonneg hC₁0 (by positivity))
    simp_rw [e1]
    rw [integral_const_mul, integral_integral_swap_of_bounded_continuous hfinD hfinX hcont1 hbd1]
    have e4 : ∀ g, ∫ h' in D, theta om Φ₁ g h * star (theta om Φ₂ g h') * φ h' ∂μ
        = theta om Φ₁ g h * th om μ D φ Φ₂ 1 := by
      intro g
      rw [← hth g]
      simp_rw [mul_assoc]
      rw [integral_const_mul]
      congr 1
      unfold GlobalTheory.ThK.Dbl.th GlobalTheory.ThK.Dbl.pet
      simp_rw [mul_comm (star _)]
    simp_rw [e4]
    rw [integral_mul_const]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.I
    ring
  have hκ : (if d < n then (1 : ℂ) else 2) * ((M.μ M.dom).toReal : ℂ)⁻¹ * th om μ D φ Φ₂ 1 ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (inv_ne_zero hv_th.1)) hv_th.2
    split_ifs <;> norm_num
  intro U' hU' hiso μ' 𝓕 hμ' h𝓕 h''
  have h7 := hcE U' hU' hiso μ' 𝓕 hμ' h𝓕 h''
  simp only [hmain] at h7
  rw [integral_const_mul] at h7
  exact (mul_eq_zero.mp h7).resolve_left hκ
private lemma evFin_eq_zero_of_At_evI {κ : Type} (z : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z) (v : Pl F) (i : κ) :
    GlobalTheory.AdelicU.evFin F v (z i) = 0 := by
  have h1 := hz ((0, 1) : NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (by
      show (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : NumberField.InfiniteAdeleRing F) = 0
      exact map_zero _)
  have h3 : (z i).2 = 0 := by
    have h4 : ((0, 1) : NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F).2 * (z i).2
        = 0 := congrArg Prod.snd (congrFun h1 i)
    simpa using h4
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i).2 = 0
  rw [h3]
  exact map_zero _

theorem cusp_re (I : OrthIn) (p : IsPair B M χ χ' om r s r' s') (h0 : min r s = 0) (X₂ : Spc F E n) (W₂ : Spc F E d)
    (p₂ : IsPair B (X := reS X X₂) (W := reS W W₂) ⟨M.co, M.vac, M.μ, M.dom⟩ χ χ' om r s r' s')
    (hc : ∀ Φ ∈ PolData B M, IsCusp W (M.I om Φ)) {Φ : Fn F n d}
    (hΦ : Φ ∈ PolData B (σ := σ) (X := reS X X₂) (W := reS W W₂) ⟨M.co, M.vac, M.μ, M.dom⟩) : IsCusp W (M.I om Φ) := by
  obtain ⟨h, hh, hθ⟩ := I.conj F E σ B d W W₂ r' s' p.base p.skew p₂.skew
  obtain ⟨g, hg, -, hT⟩ := I.move F E σ B n d X W M χ χ' om r s r' s' p X₂ W₂ ⟨M.co, M.vac, M.μ, M.dom⟩ rfl p₂
    h hh hθ
  obtain ⟨T, hTa, -⟩ := I.arch F E σ B n d X W M χ χ' om r s r' s' p g hg h hh
  have hmapT := hT T hTa
  have hsch : ∀ Ψ ∈ PolData B (σ := σ) (X := reS X X₂) (W := reS W W₂) ⟨M.co, M.vac, M.μ, M.dom⟩,
      Ψ ∈ schA F (Fin n × Fin d) := fun Ψ hΨ => GlobalTheory.ThK.Dbl.pol_sch p₂.good hΨ
  have hgen : ∀ Ψ ∈ PolData B (σ := σ) (X := reS X X₂) (W := reS W W₂) ⟨M.co, M.vac, M.μ, M.dom⟩,
      (om (g, h)) Ψ ∈ PolData B M := by
    intro Ψ hΨ
    unfold GlobalTheory.ThK.PolData at hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      have hxs := hsch x (Submodule.subset_span hx)
      obtain ⟨f, hf, φ, hφ, hv, rfl⟩ := hx
      have hrest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑f)
          (fun x => ∏ᶠ v, φ v fun i => GlobalTheory.AdelicU.evFin F v (x i)) := by
        refine ⟨fun x z hz => ?_, hxs⟩
        simp only [Pi.add_apply, map_add, evFin_eq_zero_of_At_evI z hz, add_zero]
      have h2 : (om (g, h)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) φ := hTa.2 f _ hrest
      rw [h2]
      exact Submodule.subset_span ⟨T f, by rw [← hmapT]; exact Submodule.mem_map_of_mem hf, φ, hφ, hv, rfl⟩
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ a hx
  have hΦs := hsch Φ hΦ
  have hΨ := hc _ (hgen Φ hΦ)
  have hcpt : GlobalTheory.ThK.Dbl.Cpt σ X.J := I.all F E σ B n X r s p.base (Or.inl p.herm) h0
  have hI : M.I om ((om (g, h)) Φ) = fun h' => M.I om Φ (h' * h) := by
    have e1 : (g, h) = ((1 : UA σ X.J), h) * (g, 1) := by simp
    funext h'
    rw [e1, map_mul, Module.End.mul_apply, ← GlobalTheory.ThK.Dbl.I_act I.basic p hcpt hΦs g]
    have e2 : ∀ g' : UA σ X.J, (om (g', h')) ((om (1, h)) ((om (g, 1)) Φ)) = (om (g', h' * h)) ((om (g, 1)) Φ) :=
      fun g' => by rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.I, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, e2]
  have key : IsCusp W (fun h' => M.I om Φ (h' * h)) := by
    rw [← hI]
    exact hΨ
  intro U hU hiso μ 𝓕 hμ h𝓕 h''
  have h9 := key U hU hiso μ 𝓕 hμ h𝓕 (h'' * h⁻¹)
  simpa [mul_assoc] using h9

theorem isCT_of_cusp (I : OrthIn) (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) {d₁ i₀ i₁ : ℕ} {W₁ : Spc F E d₁} (hW₁ : W₁.IsSkew σ B r' s')
    {H : Plane E d d₁} (hH : H.IsAdapted σ B W W₁ i₀ i₁) {f : UA σ W.J → ℂ} (hf : IsCusp W f) : IsCT H f 0 := by
  have hW₁d : W₁.J.det ≠ 0 := (I.eps F E σ B hB d₁ W₁ r' s' (Or.inr hW₁)).1.2
  have hP : PositivityTheory.ThKEnd.IsPlane σ H W W₁ := ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, hW₁d⟩
  have hEq := I.line F E σ hB.cm d d₁ W W₁ H (Or.inr hW.skew) hP
  have hx : H.x ≠ 0 := by
    intro hx
    have h1 := hH.xy
    rw [hx] at h1
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form] at h1
  have hU : (E ∙ H.x) ≠ ⊥ := by
    rwa [Ne, Submodule.span_singleton_eq_bot]
  have hiso : ∀ u ∈ (E ∙ H.x), ∀ u' ∈ (E ∙ H.x), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ W.J u u' = 0 := by
    intro u hu u' hu'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hu'
    have h0 := hH.xx
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form] at h0 ⊢
    have hs : (fun i => σ ((b • H.x) i)) = σ b • fun i => σ (H.x i) := by
      ext i
      simp [map_mul]
    rw [hs, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, h0]
    simp
  unfold GlobalTheory.ThK.IsCT
  rw [hEq]
  intro μ 𝓕 hμ h𝓕 _ h
  rw [Pi.zero_apply]
  exact (hf _ hU hiso μ 𝓕 hμ h𝓕 h).symm
private lemma isHecke_div_and_resEtaPow_div (α β : Chr F E) (m m' : ℕ) (K : Subgroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)ˣ)
    (hα : GlobalTheory.LFun.IsHecke F E α) (hβ : GlobalTheory.LFun.IsHecke F E β)
    (rα : GlobalTheory.WeilM.ResEtaPow K α m') (rβ : GlobalTheory.WeilM.ResEtaPow K β m) :
    GlobalTheory.LFun.IsHecke F E (β / α) ∧ GlobalTheory.WeilM.ResEtaPow K (β / α) (m + m') := by
  refine ⟨⟨hβ.1.div' hα.1, fun x => ?_⟩, fun u => ?_⟩
  · rw [MonoidHom.div_apply, hα.2 x, hβ.2 x, div_one]
  · rw [MonoidHom.div_apply, Circle.coe_div, rα u, rβ u]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

private lemma isPair_and_isPair_of_isTriple {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (T : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) ∧
      IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) := by
  obtain ⟨base, geo, chars, weil, weil'⟩ := T
  have h1 := isHecke_div_and_resEtaPow_div X.α X.β a a' _ chars.heckeα chars.heckeβ chars.resα chars.resβ
  have h2 := isHecke_div_and_resEtaPow_div X.β X.α a' a _ chars.heckeβ chars.heckeα chars.resβ chars.resα
  refine ⟨⟨base, geo.hV, geo.hW, geo.hM, chars.heckeβ, h1.1, chars.resβ, h1.2, weil⟩,
    ⟨base, geo.hV', geo.hW, geo.hM', chars.heckeα, h2.1, chars.resα, ?_, weil'⟩⟩
  rw [Nat.add_comm]
  exact h2.2

private lemma exists_trace_zero_generator_of_isCMExt (I : OrthIn) (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) {d₁ i₀ i₁ : ℕ} {W₁ : Spc F E d₁}
    (hW₁ : W₁.IsSkew σ B r' s') {H : Plane E d d₁} (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    {f c c' : UA σ W.J → ℂ} (hc : IsCT H f c) (hc' : IsCT H f c') : c = c' := by
  have hW₁d : W₁.J.det ≠ 0 := (I.eps F E σ B hB d₁ W₁ r' s' (Or.inr hW₁)).1.2
  have hWd : W.J.det ≠ 0 := (I.eps F E σ B hB d W r s (Or.inr hW)).1.2
  have hP : PositivityTheory.ThKEnd.IsPlane σ H W W₁ := ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, hW₁d⟩
  have hEq := I.line F E σ hB.cm d d₁ W W₁ H (Or.inr hW.skew) hP
  obtain ⟨μ, 𝓕, h1, h2, h3⟩ := (I.unip F E σ hB.cm d W (Or.inr hW.skew) hWd (E ∙ H.x)).1.ex
  unfold GlobalTheory.ThK.IsCT at hc hc'
  rw [hEq] at hc hc'
  funext h
  rw [hc μ 𝓕 h1 h2 h3 h, hc' μ 𝓕 h1 h2 h3 h]

theorem orthAn_of (I : OrthIn) (hR : PositivityTheory.ThKEnd.Orth.SigRapid) (hT : PositivityTheory.ThKEnd.Orth.SigThConst) (hN : NonZeroAn)
    (hA : TowerA) (hB : TowerB) (hE : EvZero) (hC : CTBigZero) (hC' : CTSmallZero) : PositivityTheory.ThKEnd.OrthAn := by
  intro F E _ _ _ _ _ σ B a a' G X om om' T f hf hc
  have hpair := isPair_and_isPair_of_isTriple T
  have hr := hR F E σ B a a' G X om om' T f hf hc
  have hG := T.geo
  refine ⟨fun hp hq Φ hΦ => ?_, fun hq hp Φ' hΦ' => ?_⟩
  · intro μ 𝓕 hμ h𝓕
    by_contra hne
    have hth := (hT F E σ B a a' G X om om' T f hf hr μ 𝓕 hμ h𝓕).1 Φ (GlobalTheory.ThK.Dbl.pol_sch hG.hM hΦ)
    have hcusp : ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, IsCusp G.W (G.M.I om Φ₁) := fun Φ₁ hΦ₁ =>
      cusp_lift I hpair.1 (by simp [hp]) (by have := hG.lt; omega) (by have := hG.lt; omega) hr hc hμ h𝓕
        hΦ hth hne hΦ₁
    obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by have := hG.aBig; omega⟩
    obtain ⟨V, V', W, T', G₁, H, H', cfg, om₁, om₁', T₁⟩ := hB F E σ B a b G X om om' T hq
    have hpair' := isPair_and_isPair_of_isTriple T'
    have hcR : ∀ Ψ ∈ GlobalTheory.ThK.PolData B (GlobalTheory.ThK.reG G V V' W).M,
        IsCusp (GlobalTheory.ThK.reG G V V' W).W ((GlobalTheory.ThK.reG G V V' W).M.I om Ψ) := fun Ψ hΨ =>
      cusp_re I hpair.1 (by simp [hp]) V W hpair'.1 hcusp hΨ
    obtain ⟨⟨e, hev⟩, hmap⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hpair'.1 _ _ _ H' _ _ G₁.M cfg.eV cfg.hH'
      T₁.geo.hM
    obtain ⟨C, hC0, hCT⟩ := hC F E σ B a b _ G₁ H H' cfg e hev
    obtain ⟨Φ₁, hΦ₁, hne₁⟩ := (hN F E σ B a b G₁ X om₁ om₁' T₁).1 (by rw [cfg.ep]; exact hp)
    rw [← hmap e hev] at hΦ₁
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.mp hΦ₁
    apply hne₁
    funext h₁
    obtain ⟨m, hm⟩ := I.levi F E σ B _ _ _ _ H' _ _ _ _ T.base T'.geo.hW cfg.hH' h₁
    have hct0 : IsCT H' ((GlobalTheory.ThK.reG G V V' W).M.I om Ψ) 0 :=
      isCT_of_cusp I T.base T'.geo.hW T₁.geo.hW cfg.hH' (hcR Ψ hΨ)
    have hsplit : GlobalTheory.ThK.Split2 G₁.W H' X ((GlobalTheory.ThK.reG G V V' W).M.I om Ψ) 0 0 :=
      ⟨by rw [add_zero]; exact hct0, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩
    have h5 := hCT X om om' om₁ om₁' T' T₁ Ψ hΨ 0 0 hsplit h₁ m hm 1
    rw [Prod.mk_one_one] at h5
    have h7 : ((om : Rep σ (GlobalTheory.ThK.reG G V V' W).V (GlobalTheory.ThK.reG G V V' W).W) 1) Ψ = Ψ := by
      rw [map_one]
      rfl
    have h8 := (mul_eq_zero.mp (h5.symm.trans (Pi.zero_apply _))).resolve_left hC0
    rw [Pi.zero_apply]
    exact (congrArg (fun t => G₁.M.I om₁ (e t) h₁) h7.symm).trans h8
  · intro μ 𝓕 hμ h𝓕
    by_contra hne
    have hΦ'p := (Submodule.mem_inf.mp hΦ').1
    have hth := (hT F E σ B a a' G X om om' T f hf hr μ 𝓕 hμ h𝓕).2 Φ' (GlobalTheory.ThK.Dbl.pol_sch hG.hM' hΦ'p)
    have hcusp : ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M', IsCusp G.W (G.M'.I om' Φ₁) := fun Φ₁ hΦ₁ =>
      cusp_lift I hpair.2 (by simp [hq]) (by have := hG.aBig; omega) (by have := hG.aBig; omega) hr hc hμ
        h𝓕 hΦ'p hth hne hΦ₁
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by have := hG.aBig; have := hG.lt; omega⟩
    obtain ⟨V, V', W, T', G₁, H, H', cfg, om₁, om₁', T₁⟩ := hA F E σ B b a' G X om om' T hq hp
    have hpair' := isPair_and_isPair_of_isTriple T'
    have hcR : ∀ Ψ ∈ GlobalTheory.ThK.PolData B (GlobalTheory.ThK.reG G V V' W).M',
        IsCusp (GlobalTheory.ThK.reG G V V' W).W ((GlobalTheory.ThK.reG G V V' W).M'.I om' Ψ) := fun Ψ hΨ =>
      cusp_re I hpair.2 (by simp [hq]) V' W hpair'.2 hcusp hΨ
    obtain ⟨⟨e, hev⟩, hmap⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hpair'.2 _ _ _ H' _ _ G₁.M' cfg.eV cfg.hH'
      T₁.geo.hM'
    obtain ⟨C, hC0, hCT⟩ := hC' F E σ B b a' _ G₁ H H' cfg e hev
    obtain ⟨Φ₁, hΦ₁, hne₁⟩ := (hN F E σ B b a' G₁ X om₁ om₁' T₁).2 cfg.q1
    have hΦ₁p := (Submodule.mem_inf.mp hΦ₁).1
    rw [← hmap e hev] at hΦ₁p
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.mp hΦ₁p
    apply hne₁
    funext h₁
    obtain ⟨m, hm⟩ := I.levi F E σ B _ _ _ _ H' _ _ _ _ T.base T'.geo.hW cfg.hH' h₁
    have hct0 : IsCT H' ((GlobalTheory.ThK.reG G V V' W).M'.I om' Ψ) 0 :=
      isCT_of_cusp I T.base T'.geo.hW T₁.geo.hW cfg.hH' (hcR Ψ hΨ)
    obtain ⟨fa, hsp, hlaw⟩ := hCT X om om' om₁ om₁' T' T₁ Ψ hΨ
    have hfa : fa = 0 := by
      have h6 := exists_trace_zero_generator_of_isCMExt I T.base T'.geo.hW T₁.geo.hW cfg.hH' hsp.1 hct0
      simpa using h6
    have h5 := hlaw h₁ m hm 1
    rw [hfa, Prod.mk_one_one] at h5
    have h7 : ((om' : Rep σ (GlobalTheory.ThK.reG G V V' W).V' (GlobalTheory.ThK.reG G V V' W).W) 1) Ψ = Ψ := by
      rw [map_one]
      rfl
    have h8 := (mul_eq_zero.mp (h5.symm.trans (Pi.zero_apply _))).resolve_left hC0
    rw [Pi.zero_apply]
    exact (congrArg (fun t => G₁.M'.I om₁' (e t) h₁) h7.symm).trans h8

end GlobalTheory.ThK.Dbl

end
