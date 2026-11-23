import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerOriginComponentBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZeroStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionHeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFrameComponentBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelSmallSectionsMulStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompLawsTowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormTowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightZeroSectionMembershipStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.IndependentCountBound

open scoped ENNReal

theorem card_le_of_intIndep {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] {d n : ℕ}
    (g : Fin n → Fin d → V) (hg : LinearIndependent ℤ g) :
    (n : ℕ∞) ≤ ((Module.finrank ℚ F * d : ℕ) : ℕ∞) * Cardinal.toENat (Module.rank F V) := by
  classical
  by_cases hfin : Module.Finite F V
  · letI : Module ℚ V := Module.compHom V (algebraMap ℚ F)
    haveI : IsScalarTower ℚ F V := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    haveI : Module.Finite ℚ V := Module.Finite.trans F V
    have hq : LinearIndependent ℚ g := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hg
    have hn := hq.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_pi_fintype] at hn
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hn
    rw [← Module.finrank_mul_finrank ℚ F V] at hn
    rw [← Module.finrank_eq_rank F V, Cardinal.toENat_nat]
    have : n ≤ Module.finrank ℚ F * d * Module.finrank F V := by
      calc n ≤ _ := hn
        _ = _ := by ring
    exact_mod_cast this
  · have htop : Cardinal.toENat (Module.rank F V) = ⊤ := by
      rw [Cardinal.toENat_eq_top]
      exact not_lt.1 fun h => hfin (Module.rank_lt_aleph0_iff.1 h)
    rw [htop]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have : n = 0 := by
        by_contra hn
        have hn' : 0 < n := Nat.pos_of_ne_zero hn
        exact hg.ne_zero ⟨0, hn'⟩ (Subsingleton.elim _ _)
      simp [this]
    · have hF : 0 < Module.finrank ℚ F := Module.finrank_pos
      have : ((Module.finrank ℚ F * d : ℕ) : ℕ∞) ≠ 0 := by
        exact_mod_cast (Nat.mul_pos hF hd).ne'
      rw [ENat.mul_top this]
      exact le_top

theorem le_growth_of_frequently {D δ k₀ : ℕ} (hδ : 0 < δ) (a : ℝ) (rk : ℕ → ℕ∞)
    (H : ∀ ε : ℝ, 0 < ε → ∃ᶠ τ : ℕ in atTop, ∃ n : ℕ, ((δ : ℝ) * a - ε) * (τ : ℝ) ^ D ≤ (D.factorial : ℝ) * n ∧
      (n : ℕ∞) ≤ (δ : ℕ∞) * rk (τ + k₀)) :
    ENNReal.ofReal a ≤ GlobalTheory.CompHt.growth D rk := by
  by_contra hlt
  obtain ⟨c, h1, h2⟩ := exists_between (not_le.1 hlt)
  have hctop : c ≠ ⊤ := ne_top_of_lt h2
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hcc : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal hctop
  have hca : c.toReal < a := (ENNReal.lt_ofReal_iff_toReal_lt hctop).1 h2
  set c' := c.toReal with hc'
  set b := (c' + a) / 2 with hb
  have hb1 : c' < b := by rw [hb]; linarith
  have hb2 : b < a := by rw [hb]; linarith
  have hbpos : 0 < b := lt_of_le_of_lt hc0 hb1
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hε : 0 < (δ : ℝ) * (a - b) := mul_pos hδ' (by linarith)
  have hlim : Tendsto (fun τ : ℕ => ((τ : ℝ) / ((τ : ℝ) + (k₀ : ℝ))) ^ D) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (k₀ : ℝ)).pow D
  have hev : ∀ᶠ τ : ℕ in atTop, c' / b < ((τ : ℝ) / ((τ : ℝ) + (k₀ : ℝ))) ^ D :=
    hlim.eventually_const_lt ((div_lt_one hbpos).2 hb1)
  have hfr := ((H _ hε).and_eventually (hev.and (eventually_gt_atTop 0)))
  have hfr' : ∃ᶠ τ' : ℕ in atTop, c ≤ (D.factorial : ℝ≥0∞) * (rk τ' : ℝ≥0∞) / (τ' : ℝ≥0∞) ^ D := by
    refine (tendsto_add_atTop_nat k₀).frequently (hfr.mono ?_)
    rintro τ ⟨⟨n, hn1, hn2⟩, hn3, hn4⟩
    have hτ : (0 : ℝ) < τ := by exact_mod_cast hn4
    have hτ' : (0 : ℝ) < (τ : ℝ) + k₀ := by positivity
    have hne0 : (((τ + k₀ : ℕ) : ℝ≥0∞)) ^ D ≠ 0 := by
      have : ((τ + k₀ : ℕ) : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (by omega : τ + k₀ ≠ 0)
      exact pow_ne_zero _ this
    have hnet : (((τ + k₀ : ℕ) : ℝ≥0∞)) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnet)]
    cases hr : rk (τ + k₀) with
    | top =>
      have hf : (D.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
      simp [ENNReal.mul_top hf]
    | coe m =>
      rw [hr] at hn2
      have hnm : n ≤ δ * m := by exact_mod_cast hn2
      have hnm' : (n : ℝ) ≤ δ * m := by exact_mod_cast hnm
      have e1 : ((δ : ℝ) * a - (δ : ℝ) * (a - b)) = δ * b := by ring
      rw [e1] at hn1
      have hfac : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
      have h3 : (δ : ℝ) * (b * (τ : ℝ) ^ D) ≤ δ * ((D.factorial : ℝ) * m) := by
        calc (δ : ℝ) * (b * (τ : ℝ) ^ D) = δ * b * (τ : ℝ) ^ D := by ring
          _ ≤ (D.factorial : ℝ) * n := hn1
          _ ≤ (D.factorial : ℝ) * (δ * m) := by gcongr
          _ = _ := by ring
      have h4 : b * (τ : ℝ) ^ D ≤ (D.factorial : ℝ) * m := le_of_mul_le_mul_left h3 hδ'
      have h5 : c' * ((τ : ℝ) + k₀) ^ D ≤ b * (τ : ℝ) ^ D := by
        rw [div_pow, div_lt_div_iff₀ hbpos (pow_pos hτ' D)] at hn3
        nlinarith [hn3]
      have hreal : c' * (((τ + k₀ : ℕ) : ℝ)) ^ D ≤ (D.factorial : ℝ) * m := by
        push_cast
        exact h5.trans h4
      have := ENNReal.ofReal_le_ofReal hreal
      rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, hcc] at this
      simpa using this
  have : c ≤ GlobalTheory.CompHt.growth D rk := Filter.le_limsup_of_frequently_le hfr'
  exact absurd h1 (not_lt.2 this)

section Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

theorem modelSmall_mono (Or : RootOrigin Y S RM Fx) (u : GlobalTheory.AllWt.Weight Dw) {R R' : ℝ} (hR : R ≤ R') :
    modelSmall Or u R ⊆ modelSmall Or u R' := by
  rintro s ⟨h1, w, hw, h2⟩
  refine ⟨h1, w, hw, fun z hz hne val hval => (h2 z hz hne val hval).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hR
    (Finset.prod_nonneg fun r _ => (zpow_pos ((Or.sing r).pos z hz.1) _).le)

variable {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

def trHom (Rd : Reading Fr h Z) (v : GlobalTheory.AllWt.Weight Dw) : RM.Ω →+ Om Z where
  toFun := trOf Rd v
  map_zero' := by simp [trOf]
  map_add' s t := by simp [trOf, add_div]

theorem card_le_rank (G : Top.Given) {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c}
    {e : Comp Xo c → Rul Xo c} (hL : CompLaws U h e) {x : ℝ}
    (hx : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x)
    {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} [DecidableEq (CMType H)]
    {T : Top.RootTower (CMType H) (Dw.p + Dw.q)} (o : Top.GoodOrigin Y T) {B : ℕ} {b : T.Comp}
    {Fr : Small.GenFrame (o.toTowerOrigin.Or B b)} {Z : Comp Xo c} (Rd : Reading Fr h Z) (hGeo : GeoRead Rd)
    (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {u : GlobalTheory.AllWt.Weight Dw} (hu : ∀ τ, StrictAnti (u τ))
    {k₀ τ : ℕ} (hτ : 0 < τ + k₀) {R₀ : ℝ} (hR₀ : 0 < R₀)
    {f : Fin (o.toTowerOrigin.Or B b).Fl.deg → (T.M B b).Ω}
    (hf : ∀ i, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (k₀ • u) R₀)
    (hinj : ∀ (v : GlobalTheory.AllWt.Weight Dw) (s : (T.M B b).Ω), (∀ i, trOf Rd v (s * f i) = 0) → s = 0)
    {n : ℕ} {f' : Fin n → (T.M B b).Ω} (hli : LinearIndependent ℤ f')
    (hsm : ∀ i, ∃ R, f' i ∈ modelSmall (o.toTowerOrigin.Or B b) (τ • u) R) :
    (n : ℕ∞) ≤ ((T.M B b).δ : ℕ∞) *
      Cardinal.toENat (Module.rank c.F (GlobalTheory.AllWt.cuspOn U Z ((τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0))) := by
  classical
  have hvu : (τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0 = GlobalTheory.AllWt.wtOf Dw ((τ + k₀) • u) 0 :=
    (GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c (T.M B b) u).2.2.1 _
  rw [hvu, (o.toTowerOrigin.Or B b).δ_eq]
  set v : GlobalTheory.AllWt.Weight Dw := (τ + k₀) • u with hv
  have hvanti : ∀ t, StrictAnti (v t) := by
    intro t i j hij
    have h1 := hu t hij
    have h2 : (0 : ℤ) < ((τ + k₀ : ℕ) : ℤ) := by exact_mod_cast hτ
    simp only [hv, Pi.smul_apply, nsmul_eq_mul]
    exact mul_lt_mul_of_pos_left h1 h2
  have key : ∀ j i, ∃ g ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw v 0), evC h Z g = trOf Rd v (f' j * f i) := by
    intro j i
    obtain ⟨R, hR⟩ := hsm j
    have hR' := modelSmall_mono (o.toTowerOrigin.Or B b) (τ • u) (le_max_left R 0) hR
    have hm : f' j * f i ∈ modelSmall (o.toTowerOrigin.Or B b) v (max R 0 * R₀) := by
      have := GlobalTheory.T.model_small_sections_mul E H Dw l Xo c Y T o B b (τ • u) (k₀ • u) (max R 0) R₀ (le_max_right _ _) hR₀.le _ hR' _ (hf i)
      rwa [← add_smul] at this
    obtain ⟨g, hg1, hg2, hg3⟩ := GlobalTheory.T.comp_laws_tower_bound G E H Dw l Xo c r U h e hL Y T o B b Fr Z Rd hGeo v _ hm.1
    refine ⟨g, ?_, hg3⟩
    refine GlobalTheory.T.weight_zero_section_membership E H Dw l Xo c r U h e hL hp hq x Z v hvanti g hg1 hg2 fun σ hσ => ⟨_, fun z hz =>
      GlobalTheory.T.uniform_norm_tower_bound G E H Dw l Xo c r U h e hL x hx Y T o B b Fr Z Rd hGeo v _ _
        (mul_nonneg (le_max_right _ _) hR₀.le) hm.2 g hg1 hg3 σ hσ z hz⟩
  choose g hg hgev using key
  let Gm : Fin n → Fin (o.toTowerOrigin.Or B b).Fl.deg → GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw v 0) :=
    fun j i => ⟨g j i, hg j i⟩
  have hli' : LinearIndependent ℤ Gm := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    refine (Fintype.linearIndependent_iff.1 hli) a (hinj v _ fun i => ?_)
    have h1 : ∑ j, a j • g j i = 0 := by
      have := congrArg (fun w => ((w i : GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw v 0)) : Rul Xo c)) ha
      simpa [Gm] using this
    have h2 : (∑ j, a j • f' j) * f i = ∑ j, a j • (f' j * f i) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => smul_mul_assoc _ _ _
    have h3 := congrArg (evCAlg h hL.genT Z) h1
    rw [map_zero, map_sum] at h3
    show trHom Rd v _ = 0
    rw [h2, map_sum, ← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul]
    exact congrArg (a j • ·) (hgev j i).symm
  have := card_le_of_intIndep (F := c.F) Gm hli'
  exact this

end Step

theorem vol_mul_flagDeg_le_growthOn : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) ≤ GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) := by
  intro hRR G E _ _ _ H Dw l Xo c r U h e hL x hx Y _ T o κ II hκ hII _ hT1 Z u hu
  have hj := o.toTowerOrigin.j_eq
  have hp : 1 ≤ Dw.p := hj ▸ T.j_pos
  have hq : 1 ≤ Dw.q := by
    have := T.j_lt
    omega
  have hW := GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c (T.M 0 (κ Z)) u
  have hdim : GlobalTheory.CompHt.dimFlag Dw = Top.dimFl (CMType H) (Dw.p + Dw.q) := hW.2.2.2.2.2.1
  have hWH : Top.WeightHyp T.j (reW u) 1 := by
    rw [hj]
    exact hW.2.2.2.2.2.2.2.1 hp hq hu
  have hB : Top.bigB0 (reW u) 1 < (⌈Top.bigB0 (reW u) 1⌉₊ : ℝ) + 1 :=
    (Nat.le_ceil _).trans_lt (lt_add_one _)
  obtain ⟨Fr, Rd, hGeo⟩ := GlobalTheory.T.tower_origin_component_bound E H Dw l Xo c r U h e hL Y T o.toTowerOrigin κ hκ ⌈Top.bigB0 (reW u) 1⌉₊ Z
  obtain ⟨k₀, R₀, f, -, hR₀, hf, -, hinj⟩ :=
    GlobalTheory.T.generic_frame_component_bound G E H Dw l Xo c h Y T o _ (κ Z) Fr Z Rd II u 1 hII hT1 hWH hB
  have main := le_growth_of_frequently (D := Top.dimFl (CMType H) (Dw.p + Dw.q)) (k₀ := k₀)
    (T.M ⌈Top.bigB0 (reW u) 1⌉₊ (κ Z)).δ_pos (T.vol (κ Z) * Top.flagDeg (reW u))
    (fun τ => Cardinal.toENat (Module.rank c.F (GlobalTheory.AllWt.cuspOn U Z (τ • GlobalTheory.AllWt.wtOf Dw u 0)))) (fun ε hε => by
      refine ((GlobalTheory.T.full_intersection_height_bound hRR G E H Dw l Xo c Y T o _ (κ Z) II u 1 hII hT1 hWH hB ε hε).and_eventually
        (eventually_gt_atTop 0)).mono ?_
      rintro τ ⟨⟨n, f', hli, hsm, hle⟩, hτ⟩
      exact ⟨n, hle, card_le_rank G hL hx o Rd hGeo hp hq hu (by omega) hR₀ hf hinj hli hsm⟩)
  rw [GlobalTheory.CompHt.growthOn, hdim]
  exact main

end GlobalTheory.CompanionTheory.Ar.Plug.IndependentCountBound

set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.CompanionTheory.Relay.uniform_norm_height_count : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) ≤ GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) :=
  GlobalTheory.CompanionTheory.Ar.Plug.IndependentCountBound.vol_mul_flagDeg_le_growthOn
