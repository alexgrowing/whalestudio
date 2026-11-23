import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelForRootMetricsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedOfPositiveNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedAdelicMetricIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularMetricConjugationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSizeAndRangeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentMetricFromSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBoundedLocallyIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerPotentialLocallyIntegrableBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedPluriharmonicExtendsSmoothlyStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ApproxModel

open GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CoverNorm GlobalTheory.Cartier

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem mono_j (M : TrueGeo.Model Y) : Mono M.j := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 F) F)) := IsLocalization.epi (nonZeroDivisors (𝓞 F)) F
  have : Mono (spMap (algebraMap (𝓞 F) F)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  exact (MorphismProperty.monomorphisms _).of_isPullback M.pb.flip this

theorem exists_fun_model (M : TrueGeo.Model Y) (g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (hg : ∀ σ y, CInfAt (g σ) y)
    (hc : ∀ σ σ' (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → g σ' y' = g σ y) :
    ∃ u : ∀ σ : 𝓞 F →+* ℂ, CxPts M.p σ → ℝ, (∀ σ y, CInfAt (u σ) y) ∧
      (∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) ∧
      ∀ σ (y : Pts Y σ) σ₀ (y' : CxPts M.p σ₀), y'.1 = y.1 ≫ M.j → u σ₀ y' = g σ y := by
  have := mono_j M
  have hτ (σ : 𝓞 F →+* ℂ) : ∃ τ : F →+* ℂ, τ.comp (algebraMap (𝓞 F) F) = σ := by
    have hi : Function.Injective σ := (RingHom.injective_iff_ker_eq_bot _).2
      (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))
    exact ⟨IsFractionRing.lift (K := F) hi, RingHom.ext fun x => by
        rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  choose τ hτ using hτ
  have e (σ : 𝓞 F →+* ℂ) : spMap σ = spMap (τ σ) ≫ spMap (algebraMap (𝓞 F) F) :=
    (congrArg spMap (hτ σ).symm).trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _))
  let s (σ : 𝓞 F →+* ℂ) (z : CxPts M.p σ) : Pts Y (τ σ) :=
    ⟨M.pb.lift z.1 (spMap (τ σ)) (z.2.trans (e σ)), M.pb.lift_snd _ _ _⟩
  have hs (σ) (z : CxPts M.p σ) : (s σ z).1 ≫ M.j = z.1 := M.pb.lift_fst _ _ _
  have hext (σ σ') (y : Pts Y σ) (y' : Pts Y σ') (h : y.1 = y'.1) : g σ y = g σ' y' := by
    have h₁ : spMap σ = spMap σ' := by rw [← y.2, ← y'.2, h]
    obtain rfl : σ = σ' := congrArg CommRingCat.Hom.hom (Spec.map_injective h₁)
    rw [Subtype.ext h]
  have key (σ) (y : Pts Y σ) (σ₀) (y' : CxPts M.p σ₀) (h : y'.1 = y.1 ≫ M.j) : g _ (s σ₀ y') = g σ y :=
    hext _ _ _ _ ((cancel_mono M.j).1 ((hs _ _).trans h))
  refine ⟨fun σ z => g _ (s σ z), fun σ z => ?_, fun σ σ' _ y y' h _ => ?_, key⟩
  · let m : Pts Y (τ σ) → CxPts M.p σ := fun w => ⟨w.1 ≫ M.j, by
      rw [Category.assoc, M.pb.w, ← Category.assoc, w.2, ← e]⟩
    have hz : m (s σ z) = z := Subtype.ext (hs σ z)
    rw [← hz]
    exact OnModelCInf.baseChange_cInfAt F M.X Y.X M.p Y.str M.j M.pb _ σ m (fun _ => rfl) _ _
      ((hg _ _).congr (.of_forall fun w => key _ w _ _ rfl))
  · refine hc _ _ _ _ ((cancel_mono M.j).1 ?_)
    rw [Category.assoc, hs, hs, h]

theorem induced_of_isComb {ι : Type} [Fintype ι] {A : Adl (cxSt F) Y} {ρ : ι → Adl (cxSt F) Y} {t : ι → ℝ}
    {g : ∀ σ, Pts Y σ → ℝ} (h : IsComb A ρ t g) (hg : ∀ σ y, CInfAt (g σ) y)
    (hc : ∀ σ σ' (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → g σ' y' = g σ y)
    (M : TrueGeo.Model Y) (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) (L : ι → HermLB M.p) (m : ℕ+)
    (hL : ∀ i, (ρ i).Induced M (L i) m 0) : ∃ (L' : HermLB M.p) (k : ℕ+), A.Induced M L' k 0 := by
  obtain ⟨q, b, hq, -, h₁, h₂, h₃⟩ := h
  obtain ⟨u, hu, huc, hug⟩ := exists_fun_model M (fun σ y => 2 * g σ y) (fun σ y => (hg σ y).const_mul 2)
    fun σ σ' y y' e => by rw [hc σ σ' y y' e]
  have H := GlobalTheory.T.combined_adelic_metric_identity F Y (Cover.ofModel M hM) A ι ρ g q b hq h₁ h₂ h₃ m (fun _ => ((m : ℕ) : ℤ)) b
    (fun i => mul_comm _ _) L (fun i => (norms_of_induces (Cover.induces_ofModel hM (hL i))).congr
      (fun x => (zpow_natCast _ _).symm) (fun _ _ => by simp) fun _ _ _ => by simp) u hu huc
    fun σ z y y' e₁ e₂ => hug σ y _ y' (by
      rw [e₁, e₂]
      exact congrArg (· ≫ M.j) (Category.comp_id _).symm)
  exact ⟨_, ⟨m * q, Nat.mul_pos m.pos hq⟩, GlobalTheory.T.induced_of_positive_norms F _ Y A M hM _ _ (fun σ z => (h₂ σ z).1) H⟩

end Model

section Man

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {Z : Set X} {r : X → ℝ} {Om : LocPot X}

theorem dense_compl (h : IsBd A Z r Om) : Dense Zᶜ := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  obtain ⟨j, hj⟩ := A.cover x
  by_contra h0
  have hs : (A.chart j).target ∩ (A.chart j).symm ⁻¹' U ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Z :=
    fun y hy => ⟨hy.1, by_contra fun hz => h0 ⟨_, hy.2, hz⟩⟩
  exact (((A.chart j).isOpen_inter_preimage_symm hU).measure_pos _ ⟨A.chart j x, (A.chart j).map_source hj,
    by simpa [(A.chart j).left_inv hj] using hx⟩).ne' (MeasureTheory.measure_mono_null hs (h.2.1 j))

theorem leviAt_eq_zero {Θ Θ' : LocPot X} {p p' : X → ℝ} (hZ : IsClosed Z) (hΘ : ReciprocityTheory.AnForm.M.IsPotential A Θ)
    (hΘ' : ReciprocityTheory.AnForm.M.IsPotential A Θ') (hp : A.SmoothOn Zᶜ p) (hp' : ∀ x, x ∉ Z → p' x = -p x)
    (hl : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, Mean4O.leviAt A Θ' j y w = -Mean4O.leviAt A Θ j y w)
    (h : PshOff A Z (Θ + LocPot.ofFun p)) (h' : PshOff A Z (Θ' + LocPot.ofFun p')) :
    ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w, Mean4O.leviAt A (Θ + LocPot.ofFun p) j y w = 0 := by
  intro j y hy hyZ w
  have hn : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl).mem_nhds ⟨hy, hyZ⟩
  have h2 : ContDiffAt ℝ 2 (p ∘ (A.chart j).symm) y := ((hp j).contDiffAt hn).of_le (WithTop.coe_le_coe.2 le_top)
  have e₁ := levi_add_smul 1 (GlobalTheory.LeviOnly.pot_two hΘ ((A.chart j).symm y) j hy (Θ.mem_U _)) h2 w
  have e₂ := levi_add_smul (-1) (GlobalTheory.LeviOnly.pot_two hΘ' ((A.chart j).symm y) j hy (Θ'.mem_U _)) h2 w
  have a : Mean4O.leviAt A (Θ + LocPot.ofFun p) j y w =
      Mean4O.leviAt A Θ j y w + levi (p ∘ (A.chart j).symm) y w := by
    simp only [one_mul] at e₁
    exact e₁
  have b : Mean4O.leviAt A (Θ' + LocPot.ofFun p') j y w =
      Mean4O.leviAt A Θ' j y w + -1 * levi (p ∘ (A.chart j).symm) y w := by
    refine (levi_congr (Filter.eventually_of_mem hn fun v hv => ?_) w).trans e₂
    show Θ'.φ _ _ + p' _ = Θ'.φ _ _ + -1 * p _
    rw [hp' _ hv.2, neg_one_mul]
  have c₁ := h j y hy hyZ w
  have c₂ := h' j y hy hyZ w
  have c₃ := hl j y hy w
  linarith

end Man

section Var

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y)

omit [NumberField F] in

theorem exists_chart_locallyIntegrableOn (he : e = Y.dim) (a : Fin (M.n + 1)) {ψ : Pts Y (I.ε a) → ℝ} {u : M.X a → ℝ} {C : ℝ}
    (hu : (M.A a).SmoothOn (M.Z a)ᶜ u) (hb : ∀ x, x ∉ M.Z a → |u x| ≤ C * Real.log (M.r a x))
    (hψ : ∀ x, x ∉ M.Z a → ψ (I.pt a x) = 2 * u x) (y : Pts Y (I.ε a)) :
    ∃ c : AlgChart Y.str (I.ε a) Y.dim, y ∈ c.e.source ∧
      MeasureTheory.LocallyIntegrableOn (ψ ∘ c.finChart.symm) c.finChart.target MeasureTheory.volume := by
  subst he
  obtain ⟨j, hj⟩ := (M.A a).cover ((I.pt a).symm y)
  obtain ⟨c, hc⟩ := I.alg a j
  have H := GlobalTheory.T.log_bounded_locally_integrable _ _ _ _ _ _ (M.bd a) (fun x => ψ (I.pt a x)) (2 * C)
    (fun k => (contDiffOn_const.mul (hu k)).congr fun v hv => hψ _ hv.2) (fun x hx => by
      rw [hψ x hx, abs_mul, abs_two, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hb x hx) zero_le_two) j
  rw [hc, Homeomorph.transOpenPartialHomeomorph_symm_apply, Homeomorph.transOpenPartialHomeomorph_target] at H
  rw [hc, Homeomorph.transOpenPartialHomeomorph_source] at hj
  exact ⟨c, by simpa using hj, by simpa [Function.comp_def] using H⟩

end Var

theorem cInfAt_sum {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {ι : Type} (s : Finset ι)
    {f : ι → CxPts p σ → ℝ} {y : CxPts p σ} (h : ∀ i, CInfAt (f i) y) : CInfAt (fun z => ∑ i ∈ s, f i z) y := by
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (0 : ℝ) y
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

section Obj

variable {D : D7} {O : Setup D} {x : ToroidalCompactificationData O.s} {P : PolOf x O.Φ} {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y}

theorem exists_smooth_ext (c : O.s.Comp) (hS : (T.F c).Size) (hM : (T.M c).FromSec) {u : Wt O.Y} (hu : Dom u)
    (hu' : Dom (-u)) : ∃ g : (T.M c).Fun, (T.M c).Smooth g ∧ ∀ a z, z ∉ (T.M c).Z a → g a z = (T.F c).ph u a z := by
  obtain ⟨h₁, h₂, h₃, C, h₄⟩ := hS
  have key (a) := GlobalTheory.T.bounded_pluriharmonic_extends_smoothly _ (T.M c) hM a ((T.F c).th u a) ((T.F c).ph u a) (C * ‖u‖) (T.th_pot c u a) (h₂ u a)
    (leviAt_eq_zero ((T.M c).bd a).1 (T.th_pot c u a) (T.th_pot c (-u) a) (h₂ u a)
      (fun z hz => (h₁ a z hz).map_neg u) (fun j y hy w => by
        rw [← T.c1_L 0 c _ a j y hy, ← T.c1_L 0 c _ a j y hy, map_neg, ← neg_one_smul ℝ,
          (T.K 0 c).firstChern_smul_leviEq _ _ a j y hy, Deg.leviAt_rsmul, neg_one_mul]) (h₃ u hu a) (h₃ _ hu' a))
    fun z hz => (h₄ u a z hz).1
  choose g hg hg' using key
  exact ⟨g, hg, hg'⟩

theorem eventually_cInfAt_regFund (hc : O.CoreWith x P) (h : O.Reads A T H) (c : O.s.Comp) (hS : (T.F c).Size)
    (hM : (T.M c).FromSec) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin O.N) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y, CInfAt (P.regFund c σ τ i t) y := by
  obtain ⟨a, rfl⟩ := (h.man c).ε.surjective σ
  have hψ (z) (hz : z ∉ (T.M c).Z a) : phW (metsOf x O.Φ) (refMet x O.Φ) c _ (fund τ i) ((h.man c).pt a z) =
      2 * (T.F c).ph (fund τ i) a z :=
    (hc.two_mul_chg c _ _ _).symm.trans (congrArg (2 * ·) ((h.an c).ph _ a z hz).symm)
  by_cases hi : (i : ℕ) + 1 < O.N
  · obtain ⟨-, h₂, -, C, h₄⟩ := hS
    have he : dimY O.Y = (O.var c).dim := by
      rw [O.dim_eq c]
      rfl
    obtain ⟨δ, hδ, H⟩ := GlobalTheory.T.kaehler_potential_locally_integrable_bound _ _ _ _ _ _ _ _ _ (P.om_kaehler c _) (P.exph_is c _)
      (exists_chart_locallyIntegrableOn (h.man c) he a (h₂ _ a) (fun z hz => (h₄ _ a z hz).1) hψ)
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht y
    refine ((H t ht.1 ht.2 y).add (cInfAt_const (P.K * t ^ 2) y)).congr (.of_forall fun z => ?_)
    exact if_pos hi
  · have hf (τ' : D.what₂.Tau) (b b' : Fin O.N) : fund τ i τ' b = fund τ i τ' b' := by
      have e (b : Fin O.N) : b ≤ i := by
        have := b.2
        exact Fin.le_def.2 (by omega)
      simp [fund, e]
    obtain ⟨g, hg, hg'⟩ := exists_smooth_ext c hS hM (u := fund τ i) (fun τ' b b' _ => (hf τ' b' b).le)
      fun τ' b b' _ => neg_le_neg (hf τ' b b').le
    have hG := fun y => (OnModelCInf.cInfAt_of_manIs (h.man c) hg a y).const_mul 2
    have hoff : offBd O.Φ c ((h.man c).ε a) = ((h.man c).pt a).symm ⁻¹' ((T.M c).Z a)ᶜ := by
      ext w
      rw [Set.mem_preimage, Set.mem_compl_iff, (h.an c).Z, Homeomorph.apply_symm_apply]
      rfl
    have hon (w) (hw : w ∈ offBd O.Φ c ((h.man c).ε a)) :
        phW (metsOf x O.Φ) (refMet x O.Φ) c _ (fund τ i) w = 2 * g a (((h.man c).pt a).symm w) := by
      rw [hoff] at hw
      rw [hg' a _ hw, ← hψ _ hw, Homeomorph.apply_symm_apply]
    refine .of_forall fun t y => (hG y).congr (.of_forall fun w => (if_neg hi).trans ?_)
    unfold extBd
    split_ifs with hw
    · exact hon w hw
    · have hd : Dense (offBd O.Φ c ((h.man c).ε a)) := by
        rw [hoff]
        exact (dense_compl ((T.M c).bd a)).preimage ((h.man c).pt a).symm.isOpenMap
      have := mem_closure_iff_nhdsWithin_neBot.1 (hd w)
      exact (((hG w).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_of_forall fun v hv => (hon v hv).symm)).limsup_eq

theorem exists_cInfAt_reg (hC : O.Core) (h : O.Reads A T H) (hS : ∀ c, (T.F c).Size) (hM : ∀ c, (T.M c).FromSec) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → ∀ c σ u y, CInfAt (O.met.reg c σ u t) y := by
  obtain ⟨x, P, hc⟩ := hC
  have : Finite O.s.Comp := inferInstanceAs (Finite O.Y.Comp)
  have H : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ c σ τ i y, CInfAt (P.regFund c σ τ i t) y :=
    eventually_all.2 fun c => eventually_all.2 fun σ => eventually_all.2 fun τ => eventually_all.2 fun i =>
      eventually_cInfAt_regFund hc h c (hS c) (hM c) σ τ i
  obtain ⟨δ, hδ, H⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 H
  refine ⟨δ, hδ, fun t h₀ h₁ c σ u y => ?_⟩
  rw [hc.reg_eq]
  exact cInfAt_sum _ fun τ => cInfAt_sum _ fun i => (H ⟨h₀, h₁⟩ c σ τ i y).const_mul _

end Obj

theorem approx_induced : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H → ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ L ∈ approx A s₀, ∀ c : O.s.Comp,
      ∃ (M : TrueGeo.Model (O.var c)) (L' : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
        (L c).Induced M L' k cf := by
  intro hP hH D O hC hf A T H h
  obtain ⟨δ, hδ, hreg⟩ := exists_cInfAt_reg hC h (fun c => (GlobalTheory.T.fibre_size_and_range_bound hP hH D O hC hf A T H h c).1)
    (GlobalTheory.T.component_metric_from_section D O hC A T H h)
  refine ⟨min 1 (δ / 2), lt_min one_pos (half_pos hδ), ?_⟩
  rintro _ ⟨B, u, s, hB, hu, hs, hss, hd, rfl⟩ c
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have e₁ : A.sh u s = fun τ i => u τ i - (s : ℝ) * O.met.dir τ i := by
    funext τ i
    simp [SlopeTestRemainingChoices.sh, h.aux.dir]
  have ht : Real.exp (-((s : ℝ) ^ 2)⁻¹) < δ := by
    have a := hss.trans (min_le_left _ _)
    have b := hss.trans (min_le_right _ _)
    have c₁ : ((s : ℝ) ^ 2)⁻¹ ≤ Real.exp ((s : ℝ) ^ 2)⁻¹ := by linarith [Real.add_one_le_exp ((s : ℝ) ^ 2)⁻¹]
    have c₂ : Real.exp (-((s : ℝ) ^ 2)⁻¹) ≤ (s : ℝ) ^ 2 := by
      rw [Real.exp_neg]
      exact (inv_anti₀ (by positivity) c₁).trans_eq (inv_inv _)
    nlinarith
  obtain ⟨M, hM, L, m, hL⟩ := GlobalTheory.T.normal_model_for_root_metrics D O hC B hB c
  obtain ⟨L', k, hI⟩ := induced_of_isComb (hC.mbIs B hB u s hu hs _ e₁ (e₁ ▸ hd) c)
    (fun σ y => ((hreg _ (Real.exp_pos _) ht c σ _ y).const_mul 2⁻¹).congr (.of_forall fun z => div_eq_inv_mul _ _))
    (fun σ σ' y y' e => congrArg (· / 2) (GlobalTheory.T.regular_metric_conjugation_invariant D O hC c σ σ' _ _ y y' e)) M hM L m hL
  exact ⟨M, L', k, 0, hI⟩

end GlobalTheory.ApproxModel
