import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightThresholdLimitCoefficientsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianLineShiftPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ShiftHEqTensorConstLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StrictWeightGrowthBoundStatement
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem ofReal_limsup_div_le (x : ℕ → ℝ) (hx : ∀ τ, 0 ≤ x τ) (c : ℝ) (hc : 0 < c) :
    ENNReal.ofReal (limsup x atTop / c) ≤ limsup (fun τ => ENNReal.ofReal (x τ / c)) atTop := by
  by_cases hb : IsBoundedUnder (· ≤ ·) atTop x
  · have hmono : Monotone (fun v : ℝ => ENNReal.ofReal (v / c)) := fun a b h =>
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h hc.le)
    have hcont : Continuous (fun v : ℝ => ENNReal.ofReal (v / c)) :=
      ENNReal.continuous_ofReal.comp (continuous_id.div_const c)
    have hco : IsCoboundedUnder (· ≤ ·) atTop x :=
      isCoboundedUnder_le_of_le atTop hx
    exact (hmono.map_limsup_of_continuousAt x hcont.continuousAt hb hco).le
  · have hset : {a : ℝ | ∀ᶠ n in atTop, x n ≤ a} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun a ha => hb ⟨a, ?_⟩
      simpa [eventually_map] using ha
    have h0 : limsup x atTop = 0 := by
      rw [limsup_eq, hset, Real.sInf_empty]
    simp [h0]

theorem arithmeticVolume_div_le_countingVolume {Ω : Type} [Field Ω] (Pr : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (D d r : ℕ)
    (m : ℕ → ℕ∞) (hd : 0 < d) (hr : 0 < r)
    (hcount : ∀ τ, ((Nat.card {s : La τ // Pr τ (s : Ω)} : ℕ) : ℕ∞) ≤ m (8 * (r * τ))) :
    ENNReal.ofReal (arVolP Pr La 1 D / (((D : ℝ) + 1) * d * ((8 * r : ℕ) : ℝ) ^ (D + 1))) ≤
      GlobalTheory.CompHt.countVol D d 8 m := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ((D : ℝ) + 1) * d * ((8 * r : ℕ) : ℝ) ^ (D + 1) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; push_cast; positivity
  rw [← hcdef]
  obtain ⟨x, hxdef⟩ : ∃ x : ℕ → ℝ, x = fun k : ℕ => smallSectionCount Pr La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := ⟨_, rfl⟩
  have hx : ∀ τ, 0 ≤ x τ := fun τ => by
    rw [hxdef]
    exact div_nonneg (Real.log_natCast_nonneg _) (by positivity)
  have h1 := ofReal_limsup_div_le x hx c hc
  have hav : arVolP Pr La 1 D = limsup x atTop := by rw [hxdef]; rfl
  rw [hav]
  refine h1.trans ?_
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → ENNReal, f = fun k : ℕ => (D.factorial : ENNReal) * GlobalTheory.CompHt.logCard (m (8 * k)) /
      ((d : ENNReal) * ((8 * k : ℕ) : ENNReal) ^ (D + 1)) := ⟨_, rfl⟩
  have hcv : GlobalTheory.CompHt.countVol D d 8 m = limsup f atTop := by rw [hfdef]; rfl
  rw [hcv]
  have h2 : ∀ τ, ENNReal.ofReal (x τ / c) ≤ f (r * τ) := by
    intro τ
    rcases Nat.eq_zero_or_pos τ with rfl | hτ
    · have : x 0 = 0 := by rw [hxdef]; simp
      simp [this]
    · have hτR : (0 : ℝ) < τ := by exact_mod_cast hτ
      obtain ⟨W, hW⟩ : ∃ W : ℕ, W = d * (8 * (r * τ)) ^ (D + 1) := ⟨_, rfl⟩
      have hWpos : 0 < W := by rw [hW]; positivity
      have hWR : (0 : ℝ) < W := by exact_mod_cast hWpos
      have hle : ENNReal.ofReal (Real.log (Nat.card {s : La τ // Pr τ (s : Ω)})) ≤
          GlobalTheory.CompHt.logCard (m (8 * (r * τ))) := by
        rw [← GlobalTheory.CompHt.logCard_coe]
        exact EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 (hcount τ)))
      have hlog : smallSectionCount Pr La (1 * τ) = Real.log (Nat.card {s : La τ // Pr τ (s : Ω)}) := by
        rw [one_mul]; rfl
      have hxe : x τ / c = Real.log (Nat.card {s : La τ // Pr τ (s : Ω)}) * ((D.factorial : ℝ) / W) := by
        rw [hxdef, hcdef, hW]
        simp only [hlog]
        generalize Real.log (Nat.card {s : La τ // Pr τ (s : Ω)}) = large₂
        simp only [one_mul, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      have hfe : f (r * τ) = GlobalTheory.CompHt.logCard (m (8 * (r * τ))) * ((D.factorial : ENNReal) / W) := by
        have : (d : ENNReal) * ((8 * (r * τ) : ℕ) : ENNReal) ^ (D + 1) = W := by
          rw [hW]; push_cast; rfl
        rw [hfdef]
        simp only [this]
        rw [mul_comm, mul_div_assoc]
      rw [hxe, hfe, ENNReal.ofReal_mul (Real.log_natCast_nonneg _),
        ENNReal.ofReal_div_of_pos hWR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
      gcongr
  have hm : Tendsto (fun τ : ℕ => r * τ) atTop atTop := tendsto_id.const_mul_atTop' hr
  calc limsup (fun τ => ENNReal.ofReal (x τ / c)) atTop
      ≤ limsup (fun τ => f (r * τ)) atTop := limsup_le_limsup (Eventually.of_forall h2)
    _ = limsup f (map (fun τ : ℕ => r * τ) atTop) := by
        rw [limsup, limsup, map_map]; rfl
    _ ≤ limsup f atTop := limsup_le_limsup_of_le hm

theorem card_le_encard_of_mul {Ω : Type} [Field Ω] (L : AddSubgroup Ω) (Pr : Ω → Prop) (S : Set Ω) (θ : Ω)
    (hθ : θ ≠ 0) (h : ∀ σ ∈ L, Pr σ → σ * θ ∈ S) :
    ((Nat.card {s : L // Pr (s : Ω)} : ℕ) : ℕ∞) ≤ S.encard := by
  by_cases hS : S.Finite
  · haveI : Finite S := hS
    let f : {s : L // Pr (s : Ω)} → S := fun s => ⟨(s.1 : Ω) * θ, h _ s.1.2 s.2⟩
    have hf : Function.Injective f := fun a b hab => by
      have h1 : (a.1 : Ω) * θ = (b.1 : Ω) * θ := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (mul_right_cancel₀ hθ h1))
    rw [← hS.cast_ncard_eq, ← Nat.card_coe_set_eq]
    exact_mod_cast Nat.card_le_card_of_injective f hf
  · rw [Set.Infinite.encard_eq hS]
    exact le_top

theorem le_countVol_of_nef {Ψ : Type} [Fintype Ψ] {N : ℕ} (h6 : BirationalPullbackPushforwardFormula) (RM : Top.RootModel Ψ N)
    (hD : 1 ≤ Top.dimFl Ψ N) (II : IntersectionSystem) (hII : IsIntersectionSystem II) (A : HermLine RM.ι)
    (hA : Small.IsNefH (mCoordIdeal RM.y) A) (κ : ℝ) (r : ℕ) (hr : 0 < r) (m : ℕ → ℕ∞)
    (hcount : ∀ τ, ((Nat.card {s : chartLatNm RM.y A.a τ //
      IsSmallH (mCoordIdeal RM.y) RM.y (Small.shiftH A κ) τ (s : RM.Ω)} : ℕ) : ℕ∞) ≤ m (8 * (r * τ))) :
    ENNReal.ofReal ((II RM.K RM.ι (mCoordIdeal RM.y) (Top.dimFl Ψ N + 1) (fun _ => A) +
        ((Top.dimFl Ψ N : ℝ) + 1) * κ * geomDeg (mCoordIdeal RM.y) A (Top.dimFl Ψ N)) /
        (((Top.dimFl Ψ N : ℝ) + 1) * RM.δ * ((8 * r : ℕ) : ℝ) ^ (Top.dimFl Ψ N + 1))) ≤
      GlobalTheory.CompHt.countVol (Top.dimFl Ψ N) RM.δ 8 m := by
  have hNs := (GlobalTheory.T.hermitian_line_shift_properties RM.K RM.ι (mCoordIdeal RM.y) A κ 1).2.1 hA
  obtain ⟨P1, hP1, hsp⟩ := hNs.semipos
  have h := h6 RM.K RM.ι RM.Ω RM.y (Top.dimFl Ψ N) (Small.shiftH A κ) P1 II hD hII RM.arith RM.birational hP1 hsp
    hNs.nef hNs.conj
  have hsm : IsSmoothHerm A := by
    obtain ⟨_, _, h'⟩ := hA.semipos
    exact h'.1
  rw [Small.selfInt_shiftH RM.K RM.ι (mCoordIdeal RM.y) (Top.dimFl Ψ N) A κ II hII RM.arith hsm] at h
  have hδ : (0 : ℝ) < RM.δ := by exact_mod_cast RM.δ_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hden : (0 : ℝ) ≤ ((Top.dimFl Ψ N : ℝ) + 1) * RM.δ * ((8 * r : ℕ) : ℝ) ^ (Top.dimFl Ψ N + 1) := by
    push_cast; positivity
  refine (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h hden)).trans ?_
  exact arithmeticVolume_div_le_countingVolume _ _ (Top.dimFl Ψ N) RM.δ r m RM.δ_pos hr hcount

theorem slope_alg (I G q δ D t' : ℝ) (hG : G ≠ 0) (hq : q ≠ 0) (hδ : δ ≠ 0) (hD : D + 1 ≠ 0) (e : ℕ) :
    (I / ((D + 1) * G) / q * (G / q ^ e) + t' * (G / q ^ e)) / δ =
      (I + (D + 1) * (q * t') * G) / ((D + 1) * δ * q ^ (e + 1)) := by
  field_simp
  ring

end GlobalTheory.CompanionTheory.Ar.Plug

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem volume_ge_slope : Top.Given → BirationalPullbackPushforwardFormula → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∀ t : ℝ, ENNReal.ofReal (T.vol b * Top.flagDeg (reW u) * (T.slope II B b (reW u) + t)) ≤ GlobalTheory.CompHt.countVol (Top.dimFl (CMType H) (Dw.p + Dw.q)) (T.M B b).δ 8 fun τ => (modelSmall (o.toTowerOrigin.Or B b) (τ • u) (Real.exp (τ * t))).encard := by
  intro hG h6 E _ _ _ H Dw l Xo c Y _ T o B b II u g hII hT1 hW hBig t
  have hanti : ∀ τ, StrictAnti (u τ) := fun τ a b' h => by
    have := hW.2.1 τ a b' h
    simpa [reW] using this
  obtain ⟨C, s, q, m, θ, hC, hs, hs0, hq, hm, hsm⟩ := GlobalTheory.T.strict_weight_growth_bound hG E H Dw l Xo c Y T o B b u hanti
  obtain ⟨hnef, hdeg, hsl, hV⟩ := GlobalTheory.T.weight_threshold_limit_coefficients (CMType H) (Dw.p + Dw.q) T II B (reW u) g b s q m hII hT1 hW hBig
    hs hs0 (fun n => (hq n).1) hm
  have hD : 1 ≤ Top.dimFl (CMType H) (Dw.p + Dw.q) := by
    obtain ⟨τ, hτ⟩ := GlobalTheory.HostModel.exists_embedding_rt_eq H
    haveI : Nonempty (CMType H) := ⟨⟨τ, hτ⟩⟩
    have h1 := T.j_pos
    have h2 := T.j_lt
    have h3 : 2 ≤ Dw.p + Dw.q := by omega
    refine Nat.mul_pos Fintype.card_pos (Nat.div_pos ?_ (by norm_num))
    calc 2 ≤ (Dw.p + Dw.q) * 1 := by omega
      _ ≤ (Dw.p + Dw.q) * (Dw.p + Dw.q - 1) := Nat.mul_le_mul_left _ (by omega)
  choose r hr using fun n => (hq n).2.1
  have hrpos : ∀ n, 0 < r n := fun n => by
    have := (hq n).1
    rw [hr n] at this
    omega
  have hδ : (0 : ℝ) < (T.M B b).δ := by exact_mod_cast (T.M B b).δ_pos
  have hapos := hdeg.eventually_const_lt (mul_pos hδ hV)
  have hst : Tendsto (fun n => t - C * s n) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub (hs0.const_mul C)
  have hlim := ((hsl.mul hdeg).add (hst.mul hdeg)).div_const ((T.M B b).δ : ℝ)
  have hval : (T.slope II B b (reW u) * ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u))) +
      t * ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)))) / ((T.M B b).δ : ℝ) =
      T.vol b * Top.flagDeg (reW u) * (T.slope II B b (reW u) + t) := by
    field_simp
  rw [hval] at hlim
  refine le_of_tendsto (ENNReal.tendsto_ofReal hlim) ?_
  filter_upwards [hnef, hapos] with n hn ha
  have hqn : (0 : ℝ) < q n := by exact_mod_cast (hq n).1
  have hG0 : geomDeg (T.M B b).P (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n))
      (Top.dimFl (CMType H) (Dw.p + Dw.q)) ≠ 0 := by
    intro h0
    rw [h0] at ha
    simp at ha
  have hkey := le_countVol_of_nef h6 (T.M B b) hD II hII.1 _ hn (q n * (t - C * s n)) (r n) (hrpos n)
    (fun τ => (modelSmall (o.toTowerOrigin.Or B b) (τ • u) (Real.exp (τ * t))).encard) (fun τ => by
      have he : 8 * (r n * τ) = τ * q n := by rw [hr n]; ring
      simp only [he]
      refine card_le_encard_of_mul _ _ _ (θ n ^ τ) (pow_ne_zero _ (hq n).2.2) fun σ h1 h2 => ?_
      have := hsm n τ (t - C * s n) σ h1 h2
      rwa [sub_add_cancel] at this)
  rw [← hr n] at hkey
  have halg := slope_alg (II (T.M B b).K (T.M B b).ι (T.M B b).P (Top.dimFl (CMType H) (Dw.p + Dw.q) + 1)
      (fun _ => Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)))
    (geomDeg (T.M B b).P (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n))
      (Top.dimFl (CMType H) (Dw.p + Dw.q))) (q n) ((T.M B b).δ : ℝ) (Top.dimFl (CMType H) (Dw.p + Dw.q) : ℝ)
    (t - C * s n) hG0 hqn.ne' hδ.ne' (by positivity) (Top.dimFl (CMType H) (Dw.p + Dw.q))
  simp only [Small.normHt]
  rw [halg]
  exact hkey

end GlobalTheory.CompanionTheory.Ar.Plug
