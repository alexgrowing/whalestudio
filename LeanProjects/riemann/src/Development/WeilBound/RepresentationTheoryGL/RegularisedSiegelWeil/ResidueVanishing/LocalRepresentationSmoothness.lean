import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Leaves

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Eis
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw
open Filter Topology Set Metric

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.Kplug.FormalGroupLawNegation

theorem lim_eq {f F : ℂ → ℂ} {W : Set ℂ} {c w : ℂ} (hW : IsOpen W) (hw : w ∈ W) (hF : ContinuousOn F W)
    (he : ∀ u ∈ W, u ≠ c → f u = F u) : limUnder (𝓝[≠] w) f = F w := by
  have h1 : Tendsto F (𝓝[≠] w) (𝓝 (F w)) :=
    ((hF.continuousAt (hW.mem_nhds hw)).tendsto).mono_left nhdsWithin_le_nhds
  have h2 : ∀ᶠ u in 𝓝[≠] w, u ≠ c := by
    rcases eq_or_ne w c with rfl | h
    · exact self_mem_nhdsWithin
    · exact eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds h)
  have h3 : F =ᶠ[𝓝[≠] w] f := by
    filter_upwards [h2, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hw)] with u hu hu'
    exact (he u hu' hu).symm
  exact (h1.congr' h3).limUnder_eq

variable {D : D7} (V : HSp D) (Φ : ℂ → GA D (dblSp V) → ℂ) (d : Polynomial ℂ)

def Ek (z : ℂ) (g : GA D (dblSp V)) : ℂ := limUnder (𝓝[≠] z) fun u => d.eval u * eisCont V Φ u g

def LocRep (z : ℂ) : Prop :=
  ∃ (W : Set ℂ) (F : ℂ → GA D (dblSp V) → ℂ) (c : ℂ), IsOpen W ∧ z ∈ W ∧ (∀ g, DifferentiableOn ℂ (F · g) W) ∧
    ContinuousOn (fun y : ℂ × GA D (dblSp V) => F y.1 y.2) (W ×ˢ univ) ∧
    ∀ u ∈ W, u ≠ c → ∀ g, F u g = d.eval u * eisCont V Φ u g

variable {V Φ d}

theorem LocRep.eq {z : ℂ} (h : LocRep V Φ d z) : ∃ (W : Set ℂ) (F : ℂ → GA D (dblSp V) → ℂ), IsOpen W ∧ z ∈ W ∧
    (∀ g, DifferentiableOn ℂ (F · g) W) ∧ ContinuousOn (fun y : ℂ × GA D (dblSp V) => F y.1 y.2) (W ×ˢ univ) ∧
    ∀ u ∈ W, ∀ g, Ek V Φ d u g = F u g := by
  obtain ⟨W, F, c, hW, hz, hd, hc, he⟩ := h
  exact ⟨W, F, hW, hz, hd, hc, fun u hu g => lim_eq (f := fun u => d.eval u * eisCont V Φ u g) (F := fun u => F u g)
    (c := c) hW hu (hd g).continuousOn fun u' hu' hne => (he u' hu' hne g).symm⟩

theorem LocRep.diff {z : ℂ} (h : LocRep V Φ d z) (g : GA D (dblSp V)) : DifferentiableAt ℂ (Ek V Φ d · g) z := by
  obtain ⟨W, F, hW, hz, hd, -, e⟩ := h.eq
  exact ((hd g).differentiableAt (hW.mem_nhds hz)).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hW.mem_nhds hz) fun u hu => e u hu g)

theorem LocRep.cont {z : ℂ} (h : LocRep V Φ d z) (g : GA D (dblSp V)) :
    ContinuousAt (fun y : ℂ × GA D (dblSp V) => Ek V Φ d y.1 y.2) (z, g) := by
  obtain ⟨W, F, hW, hz, -, hc, e⟩ := h.eq
  have hN : W ×ˢ (univ : Set (GA D (dblSp V))) ∈ 𝓝 (z, g) := (hW.prod isOpen_univ).mem_nhds ⟨hz, trivial⟩
  exact (hc.continuousAt hN).congr (Filter.eventually_of_mem hN fun y hy => (e y.1 hy.1 y.2).symm)

end PositivityTheory.Rg.Rsw.Kplug.FormalGroupLawNegation

namespace PositivityTheory.Rg.Rsw.Kplug

open FormalGroupLawNegation

theorem local_representation_smoothness : PositivityTheory.Rg.Rsw.Kplug.K1 := by
  intro D V Φ hE hReg ha s₀
  have ha' : ∀ g, AnalyticOnNhd ℂ (eisSer V Φ g) (rightOf ((V.rank : ℝ) / 2)) := ha
  set a : ℝ := (V.rank : ℝ) / 2 with ha_def
  choose k hk using hReg
  have hk' : ∀ s, ∃ (r : ℝ) (H : ℂ → GA D (dblSp V) → ℂ), 0 < r ∧
      (∀ s' ∈ ball s r, s' ≠ s → ∀ g, H s' g = (s' - s) ^ k s * eisCont V Φ s' g) ∧
      (∀ g, DifferentiableOn ℂ (H · g) (ball s r)) ∧
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball s r ×ˢ univ) := fun s => by
    obtain ⟨r, H, h1, h2, h3, h4, -⟩ := hk s
    exact ⟨r, H, h1, h2, h3, h4⟩
  choose r H hr hH hHd hHc using hk'
  set T : ℝ := |a - s₀.re| + 2 with hT_def
  set K : Set ℂ := (fun t : ℝ => s₀ + t) '' Icc 0 T with hK_def
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover (fun x => ball x (r x)) fun x _ => ball_mem_nhds x (hr x)
  set B : Set ℂ := ⋃ x ∈ t, ball x (r x) with hB_def
  have hB : IsOpen B := isOpen_biUnion fun x _ => isOpen_ball
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_thickening_subset_open hB hKt
  set W₀ : Set ℂ := B ∪ rightOf a with hW₀_def
  set A : Set ℂ := {z | ∀ τ : ℝ, 0 ≤ τ → z + τ ∈ W₀} with hA_def
  set U : Set ℂ := interior A with hU_def
  set d : Polynomial ℂ := ∏ x ∈ t, (Polynomial.X - Polynomial.C x) ^ k x with hd_def

  have hUW : U ⊆ W₀ := fun z hz => by simpa using interior_subset hz 0 le_rfl
  have hs₀ : s₀ ∈ U := by
    refine mem_interior.2 ⟨ball s₀ (min δ 1), fun z hz τ hτ => ?_, isOpen_ball, mem_ball_self (lt_min hδ one_pos)⟩
    have hz' : dist z s₀ < min δ 1 := hz
    rcases le_or_gt τ T with hτT | hτT
    · refine mem_union_left _ (hδK ?_)
      rw [Metric.mem_thickening_iff]
      refine ⟨s₀ + τ, ⟨τ, ⟨hτ, hτT⟩, rfl⟩, ?_⟩
      rw [dist_add_right]
      exact hz'.trans_le (min_le_left _ _)
    · refine mem_union_right _ ?_
      show a < (z + τ).re
      have h1 : |(z - s₀).re| ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
      have h2 : ‖z - s₀‖ < 1 := by rw [← dist_eq_norm]; exact hz'.trans_le (min_le_right _ _)
      have h3 : a - s₀.re ≤ |a - s₀.re| := le_abs_self _
      have h4 := neg_abs_le (z - s₀).re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.sub_re] at h1 h4 ⊢
      linarith
  have hRD : IsRightDomain U := by
    refine ⟨⟨a, interior_maximal (fun z hz τ hτ => mem_union_right _ ?_) (isOpen_rightOf a)⟩, fun z hz τ hτ => ?_⟩
    · show a < (z + τ).re
      have : a < z.re := hz
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    · have hopen : IsOpen ((fun w : ℂ => w - τ) ⁻¹' U) := isOpen_interior.preimage (by fun_prop)
      have hsub : (fun w : ℂ => w - τ) ⁻¹' U ⊆ A := fun w hw τ' hτ' => by
        have h1 := interior_subset hw (τ + τ') (by positivity)
        have e : w - (τ : ℂ) + ((τ + τ' : ℝ) : ℂ) = w + τ' := by push_cast; ring
        rw [e] at h1
        exact h1
      refine interior_maximal hsub hopen ?_
      show z + (τ : ℂ) - τ ∈ U
      rw [add_sub_cancel_right]
      exact hz

  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)

  have hloc : ∀ z ∈ U, LocRep V Φ d z := by
    intro z hz
    rcases hUW hz with hzB | hzR
    · obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 hzB
      set q : Polynomial ℂ := ∏ y ∈ t.erase x, (Polynomial.X - Polynomial.C y) ^ k y with hq_def
      have hdq : d = (Polynomial.X - Polynomial.C x) ^ k x * q := (Finset.mul_prod_erase t _ hxt).symm
      refine ⟨ball x (r x), fun u g => q.eval u * H x u g, x, isOpen_ball, hzx,
        fun g => q.differentiable.differentiableOn.mul (hHd x g),
        (q.continuous.comp continuous_fst).continuousOn.mul (hHc x), fun u hu hne g => ?_⟩
      simp only
      rw [hH x u hu hne g, hdq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      ring
    · have hv := hE.1.eisValueAt ha' hzR
      obtain ⟨r', hr', hd', hc', -⟩ := (hk z).of_eisValueAt hv
      exact ⟨ball z r', fun u g => d.eval u * eisCont V Φ u g, z, isOpen_ball, mem_ball_self hr',
        fun g => d.differentiable.differentiableOn.mul (hd' g),
        (d.continuous.comp continuous_fst).continuousOn.mul hc', fun u _ _ g => rfl⟩

  have hZ : {z : ℂ | d.IsRoot z}.Finite := Polynomial.finite_setOfPred_isRoot hd0
  have hO : IsOpen (U ∩ ({z : ℂ | d.IsRoot z} \ {s₀})ᶜ) :=
    isOpen_interior.inter (hZ.subset fun x hx => hx.1).isClosed.isOpen_compl
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.1 hO s₀ ⟨hs₀, fun h => h.2 rfl⟩
  have hcb : closedBall s₀ (ε₁ / 2) ⊆ ball s₀ ε₁ := closedBall_subset_ball (half_lt_self hε₁)
  refine ⟨U, d, Ek V Φ d, ε₁ / 2, isOpen_interior, hRD, hs₀, hd0, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun g z hz => ((hloc z hz).diff g).differentiableWithinAt
  · exact fun y hy => ((hloc y.1 hy.1).cont y.2).continuousWithinAt
  · intro z _ γ hγ g
    unfold Ek
    congr 1
    funext u
    congr 1
    exact hE.1.leftInv_eisLaurent u 0 γ hγ g
  · intro z hz g
    exact lim_eq (f := fun u => d.eval u * eisCont V Φ u g) (F := fun u => d.eval u * eisSer V Φ g u) (c := z)
      (isOpen_rightOf a) hz (d.continuous.continuousOn.mul (ha' g).continuousOn) fun u hu _ => by
        show d.eval u * cont (eisSer V Φ g) u = d.eval u * eisSer V Φ g u
        rw [eqOn_cont (ha' g) hu]
  · exact ⟨half_pos hε₁, fun z hz => (hball (hcb hz)).1, fun z hz hne h0 => (hball (hcb hz)).2 ⟨h0, hne⟩⟩

end PositivityTheory.Rg.Rsw.Kplug

end
