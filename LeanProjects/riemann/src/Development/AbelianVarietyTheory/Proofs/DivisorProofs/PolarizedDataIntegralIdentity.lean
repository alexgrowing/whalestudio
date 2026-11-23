import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinAtMinusRhoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConeRepresentatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesRationalInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesMeasurable
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.ConeSmallUnfEis

section Abstract

open scoped Pointwise ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G} [μ.IsMulLeftInvariant]

theorem translates_fundamentalDomain {Γ P : Subgroup G} (hP : P ≤ Γ) {T : Set G} [Countable T] (hT : T ⊆ Γ)
    (hrep : ∀ γ ∈ Γ, ∃! t, t ∈ T ∧ γ * t⁻¹ ∈ P) {D : Set G} (hD : IsFundamentalDomain Γ D μ) :
    Pairwise (Function.onFun (AEDisjoint μ) fun t : T => (fun g => t.1⁻¹ * g) ⁻¹' D) ∧
      IsFundamentalDomain P (⋃ t : T, (fun g => t.1⁻¹ * g) ⁻¹' D) μ := by
  let S : G → Set G := fun h => (fun g => h⁻¹ * g) ⁻¹' D
  have hsmul : ∀ δ : Γ, δ • D = S δ.1 := fun δ => by
    ext g; rw [Set.mem_smul_set_iff_inv_smul_mem]; rfl
  have hdisj : ∀ δ δ' : G, δ ∈ Γ → δ' ∈ Γ → δ ≠ δ' → AEDisjoint μ (S δ) (S δ') := by
    intro δ δ' hδ hδ' hne
    have := hD.aedisjoint (show (⟨δ, hδ⟩ : Γ) ≠ ⟨δ', hδ'⟩ from fun h => hne (congrArg Subtype.val h))
    rwa [Function.onFun, hsmul, hsmul] at this
  refine ⟨fun x y hxy => hdisj _ _ (hT x.2) (hT y.2) fun heq => hxy (Subtype.ext heq), ?_⟩
  have hnm : ∀ h, NullMeasurableSet (S h) μ := fun h =>
    hD.nullMeasurableSet.preimage (measurePreserving_mul_left μ h⁻¹).quasiMeasurePreserving
  have hq : ∀ q : P, q • (⋃ t : T, S t.1) = ⋃ t : T, S (q.1 * t.1) := by
    intro q
    rw [Set.smul_set_iUnion]
    refine Set.iUnion_congr fun x => ?_
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show x.1⁻¹ * (q.1⁻¹ * g) ∈ D ↔ (q.1 * x.1)⁻¹ * g ∈ D
    rw [mul_inv_rev, mul_assoc]
  refine { nullMeasurableSet := NullMeasurableSet.iUnion fun x => hnm x.1, ae_covers := ?_, aedisjoint := ?_ }
  · filter_upwards [hD.ae_covers] with g ⟨δ, hδg⟩
    obtain ⟨t, ⟨htT, ht⟩, -⟩ := hrep δ.1⁻¹ (inv_mem δ.2)
    refine ⟨⟨(δ.1⁻¹ * t⁻¹)⁻¹, inv_mem ht⟩, Set.mem_iUnion.2 ⟨⟨t, htT⟩, ?_⟩⟩
    show t⁻¹ * ((δ.1⁻¹ * t⁻¹)⁻¹ * g) ∈ D
    have e : t⁻¹ * ((δ.1⁻¹ * t⁻¹)⁻¹ * g) = δ.1 * g := by group
    rw [e]
    exact hδg
  · intro q q' hqq'
    rw [Function.onFun, hq, hq, AEDisjoint.iUnion_left_iff]
    intro x
    rw [AEDisjoint.iUnion_right_iff]
    intro y
    apply hdisj _ _ (mul_mem (hP q.2) (hT x.2)) (mul_mem (hP q'.2) (hT y.2))
    intro heq
    obtain ⟨t, -, hu⟩ := hrep (q.1 * x.1) (mul_mem (hP q.2) (hT x.2))
    have h1 : x.1 = t := hu _ ⟨x.2, by rw [mul_inv_cancel_right]; exact q.2⟩
    have h2 : y.1 = t := hu _ ⟨y.2, by rw [heq, mul_inv_cancel_right]; exact q'.2⟩
    rw [h1, h2] at heq
    exact hqq' (Subtype.ext (mul_right_cancel heq))

theorem unfold_translates {T : Set G} [Countable T] {D : Set G} (hD : NullMeasurableSet D μ)
    (hd : Pairwise (Function.onFun (AEDisjoint μ) fun t : T => (fun g => t.1⁻¹ * g) ⁻¹' D)) {f : G → ℂ}
    (hf : AEStronglyMeasurable f μ) (hfin : ∑' t : T, ∫⁻ g in D, ‖f (t.1 * g)‖ₑ ∂μ ≠ ⊤) :
    IntegrableOn f (⋃ t : T, (fun g => t.1⁻¹ * g) ⁻¹' D) μ ∧
      ∫ g in ⋃ t : T, (fun g => t.1⁻¹ * g) ⁻¹' D, f g ∂μ = ∫ g in D, ∑' t : T, f (t.1 * g) ∂μ := by
  have hnm : ∀ t : T, NullMeasurableSet ((fun g => t.1⁻¹ * g) ⁻¹' D) μ := fun t =>
    hD.preimage (measurePreserving_mul_left μ t.1⁻¹).quasiMeasurePreserving
  have hpre : ∀ t : G, (fun g => t * g) ⁻¹' ((fun g => t⁻¹ * g) ⁻¹' D) = D := fun t => by
    ext g; simp
  have hL : ∀ t : G, ∫⁻ g in (fun g => t⁻¹ * g) ⁻¹' D, ‖f g‖ₑ ∂μ = ∫⁻ g in D, ‖f (t * g)‖ₑ ∂μ := fun t => by
    have := (measurePreserving_mul_left μ t).setLIntegral_comp_preimage_emb (measurableEmbedding_mulLeft t)
      (fun g => ‖f g‖ₑ) ((fun g => t⁻¹ * g) ⁻¹' D)
    rw [hpre] at this
    exact this.symm
  have hI : ∀ t : G, ∫ g in (fun g => t⁻¹ * g) ⁻¹' D, f g ∂μ = ∫ g in D, f (t * g) ∂μ := fun t => by
    have := (measurePreserving_mul_left μ t).setIntegral_preimage_emb (measurableEmbedding_mulLeft t)
      f ((fun g => t⁻¹ * g) ⁻¹' D)
    rw [hpre] at this
    exact this.symm
  have hint : IntegrableOn f (⋃ t : T, (fun g => t.1⁻¹ * g) ⁻¹' D) μ := by
    refine ⟨hf.restrict, ?_⟩
    show ∫⁻ g in _, ‖f g‖ₑ ∂μ < ⊤
    refine (lintegral_iUnion_le _ _).trans_lt ?_
    simp only [hL]
    exact lt_top_iff_ne_top.2 hfin
  refine ⟨hint, ?_⟩
  rw [integral_iUnion_ae hnm hd hint, integral_tsum (fun t => ?_) hfin]
  · simp only [hI]
  · exact (hf.comp_quasiMeasurePreserving (measurePreserving_mul_left μ t.1).quasiMeasurePreserving).restrict

theorem tsum_ofReal_rpow_le {ι : Type*} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {r : ℝ} {S : ℂ}
    (h : HasSum (fun i => (a i : ℂ) ^ (r : ℂ)) S) : ∑' i, ENNReal.ofReal (a i ^ r) ≤ ENNReal.ofReal ‖S‖ := by
  have h1 : HasSum (fun i => a i ^ r) S.re := by
    have := Complex.hasSum_re h
    simpa only [← Complex.ofReal_cpow (ha _).le, Complex.ofReal_re] using this
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (Real.rpow_pos_of_pos (ha i) r).le) h1.summable, h1.tsum_eq]
  exact ENNReal.ofReal_le_ofReal (Complex.re_le_norm S)

theorem rpow_le_add {x r ε : ℝ} (hx : 0 < x) (hε : 0 ≤ ε) : x ^ r ≤ x ^ (r - ε) + x ^ (r + ε) := by
  have h1 := Real.rpow_pos_of_pos hx (r - ε)
  have h2 := Real.rpow_pos_of_pos hx (r + ε)
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hx h (show r - ε ≤ r by linarith)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h (show r ≤ r + ε by linarith)
    linarith

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem iwaHt_pos {K : Subgroup (UA σ J)} {x : Fin n → E} {hf : UA σ J → ℝ} (hiw : GlobalTheory.ConeSmall.IsIwaHt K x hf)
    (hdec : ∀ g, ∃ (p k : UA σ J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F x = l.1 • incV F x ∧ g = p * k) (g : UA σ J) :
    0 < hf g := by
  obtain ⟨p, k, l, hk, hl, rfl⟩ := hdec g
  rw [hiw p k l hk hl]
  have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h1))

theorem hasSum_eis {K : Subgroup (UA σ J)} {x : Fin n → E} {hf : UA σ J → ℝ} (hiw : GlobalTheory.ConeSmall.IsIwaHt K x hf)
    {Eis : ℂ → UA σ J → ℂ} (hE : GlobalTheory.ConeSmall.IsEisSer K x Eis) {T : Set (UA σ J)} (hT : GlobalTheory.ConeSmallCT.IsReps T x)
    {s : ℂ} (hs : ((n : ℝ) - 1) / 2 < s.re) (g : UA σ J) :
    HasSum (fun t : T => (hf (t.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) (Eis s g) := by
  obtain ⟨hf', hiw', hdec, hsum⟩ := hE
  have e : hf = hf' := funext fun y => by
    obtain ⟨p, k, l, hk, hl, rfl⟩ := hdec y
    rw [hiw p k l hk hl, hiw' p k l hk hl]
  rw [e]
  exact hsum T hT.1 hT.2 s hs g

theorem series_le_qht {K : Subgroup (UA σ J)} {x : Fin n → E} {hf : UA σ J → ℝ} (hiw : GlobalTheory.ConeSmall.IsIwaHt K x hf)
    (hpos : ∀ g, 0 < hf g) {Eis : ℂ → UA σ J → ℂ} (hE : GlobalTheory.ConeSmall.IsEisSer K x Eis)
    (hloc : ∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → UA σ J → ℂ) (C : ℝ) (N : ℕ), U ∈ 𝓝 s₀ ∧
      (∀ s ∈ U, s ≠ s₀ → ∀ g, Hol s g = (s - s₀) ^ k * Eis s g) ∧ ∀ s ∈ U, ∀ g, ‖Hol s g‖ ≤ C * (ht g : ℝ) ^ N)
    {T : Set (UA σ J)} (hT : GlobalTheory.ConeSmallCT.IsReps T x) {r : ℝ} (hr : ((n : ℝ) - 1) / 2 < r) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g, ∑' t : T, ENNReal.ofReal (hf (t.1 * g) ^ (r + ((n : ℝ) - 1) / 2)) ≤
      ENNReal.ofReal (C * (qht g : ℝ) ^ N) := by
  obtain ⟨k, U, Hol, C, N, hU, hH, hb⟩ := hloc (r : ℂ)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  set ε : ℝ := min (δ / 2) ((r - ((n : ℝ) - 1) / 2) / 2) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hε1 : ε ≤ δ / 2 := min_le_left _ _
  have hε2 : ε ≤ (r - ((n : ℝ) - 1) / 2) / 2 := min_le_right _ _
  have key : ∀ u : ℝ, |u - r| = ε → ∀ g, ∑' t : T, ENNReal.ofReal (hf (t.1 * g) ^ (u + ((n : ℝ) - 1) / 2)) ≤
      ENNReal.ofReal (max (C / ε ^ k) 0 * (qht g : ℝ) ^ N) := by
    intro u hu g
    have hn : ‖(u : ℂ) - (r : ℂ)‖ = ε := by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hu]
    have huU : (u : ℂ) ∈ U := hδU (by rw [Metric.mem_ball, dist_eq_norm, hn]; linarith)
    have hne : (u : ℂ) ≠ r := fun h0 => by rw [h0, sub_self, norm_zero] at hn; exact hε.ne hn
    have hus : ((n : ℝ) - 1) / 2 < (u : ℂ).re := by
      rw [Complex.ofReal_re]
      have := (abs_le.1 hu.le).1
      linarith
    have hbd : ∀ y, ‖Eis u y‖ ≤ C / ε ^ k * (ht y : ℝ) ^ N := fun y => by
      have h1 := hb _ huU y
      rw [hH _ huU hne y, norm_mul, norm_pow, hn] at h1
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hε k), mul_comm]
      exact h1
    have hq := GlobalTheory.ThKOrthVInt.norm_le_qht_of_le_ht (g := Eis u)
      (fun γ hγ y => GlobalTheory.ConeSmall.eis_rat_left_invariant K x Eis hE u hus γ hγ y) hbd g
    have hs := hasSum_eis hiw hE hT hus g
    have e : (u : ℂ) + ((n : ℂ) - 1) / 2 = ((u + ((n : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e] at hs
    exact (tsum_ofReal_rpow_le (fun t : T => hpos (t.1 * g)) hs).trans (ENNReal.ofReal_le_ofReal hq)
  refine ⟨2 * max (C / ε ^ k) 0, N, by positivity, fun g => ?_⟩
  have h1 := key (r - ε) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε]) g
  have h2 := key (r + ε) (by rw [add_sub_cancel_left, abs_of_pos hε]) g
  have h0 : 0 ≤ max (C / ε ^ k) 0 * (qht g : ℝ) ^ N := by positivity
  calc ∑' t : T, ENNReal.ofReal (hf (t.1 * g) ^ (r + ((n : ℝ) - 1) / 2))
      ≤ ∑' t : T, (ENNReal.ofReal (hf (t.1 * g) ^ (r - ε + ((n : ℝ) - 1) / 2)) +
          ENNReal.ofReal (hf (t.1 * g) ^ (r + ε + ((n : ℝ) - 1) / 2))) := by
        refine ENNReal.tsum_le_tsum fun t => ?_
        refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
        have := rpow_le_add (r := r + ((n : ℝ) - 1) / 2) (hpos (t.1 * g)) hε.le
        convert this using 3 <;> ring
    _ ≤ ENNReal.ofReal (max (C / ε ^ k) 0 * (qht g : ℝ) ^ N) + ENNReal.ofReal (max (C / ε ^ k) 0 * (qht g : ℝ) ^ N) := by
        rw [ENNReal.tsum_add]
        exact add_le_add h1 h2
    _ = _ := by rw [← ENNReal.ofReal_add h0 h0]; congr 1; ring

theorem unfold_eis : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ K : Subgroup (UA σ G.V'.J), IsStab B K → ∀ X om om', IsTriple B G X om om' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∀ hf : UA σ G.V'.J → ℝ, GlobalTheory.ConeSmall.IsIwaHt K H.x hf → (∀ g, ∃ (p k : UA σ G.V'.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k) →
    ∀ Eis : ℂ → UA σ G.V'.J → ℂ, GlobalTheory.ConeSmall.IsEisSer K H.x Eis →
    ∃ 𝓓 : Set (UA σ G.V'.J), IsFundamentalDomain (ratStab σ G.V'.J H.x) 𝓓 G.M'.μ ∧ ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re → ∀ h,
      GlobalTheory.ConeSmallCT.Bint G.M' om' Φ' Eis s h = ∫ g in 𝓓, theta om' Φ' g h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2) ∂G.M'.μ ∧
      IntegrableOn (fun g => theta om' Φ' g h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)) 𝓓 G.M'.μ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC K hK X om om' hT Φ' hΦ' hf hiw hdec Eis hES
  have hV' : IsPair B G.M' X.α (X.α / X.β) om' G.q (b + 2 - G.q) (a + (b + 2) - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV', skew := hT.geo.hW, good := hT.geo.hM', hX := hT.chars.heckeα,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeα hT.chars.heckeβ, resX := hT.chars.resα,
      resW := by rw [add_comm a (b + 2)]; exact GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resα hT.chars.resβ,
      weil := hT.weil' }
  have hΦs : Φ' ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) :=
    GlobalTheory.ThKRatInv.polData_le_schA B G.M' hT.geo.hM' (Submodule.mem_inf.1 hΦ').1
  obtain ⟨hcont, hinv, -⟩ := (GlobalTheory.T.theta_basic_properties hKP.base F E σ B (b + 2) (a + (b + 2)) G.V' G.W G.M' X.α (X.α / X.β) om'
    _ _ _ _ hV').1 Φ' hΦs
  have hdecay := GlobalTheory.T.schwartz_orbit_decay hKP F E σ B (b + 2) (a + (b + 2)) G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hV' Φ'
    (Submodule.mem_inf.1 hΦ').2
  have hfin : G.M'.μ G.M'.dom < ⊤ :=
    GlobalTheory.UnitaryVol.measure_dom_lt_top F E σ B a (b + 2) G X om om' hKP.siegelSetUnitary hT
  obtain ⟨Eis', hES', hloc, -⟩ := GlobalTheory.T.eisenstein_at_minus_rho hKP F E σ B a b G G₁ H H' hC X om om' hT K hK
  obtain ⟨K', -, -, hK'stab, hK'cpt, -, -⟩ := GlobalTheory.StabHaar.stabEx hKP.base F E σ B (b + 2) G.V' _ _ hT.base hT.geo.hV'
  have hKK : K = K' := Subgroup.ext fun g => (hK g).trans (hK'stab g).symm
  have hfc : Continuous hf := GlobalTheory.ConeSmallMeas.continuous_ht K (hKK ▸ hK'cpt) H.x hf hiw hdec
  have hpos := iwaHt_pos hiw hdec
  obtain ⟨T, hTr⟩ := GlobalTheory.ConeSmallCT.exists_isReps F E σ (b + 2) G.V'.J H.x
  haveI hR := GlobalTheory.UnitaryVol.countable_ratU σ G.V'.J
  haveI : Countable T := Set.Countable.to_subtype ((Set.countable_coe_iff.1 hR).mono hTr.1)
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI := (GlobalTheory.LeviModulus.topUA σ G.V'.J).1
  haveI := (GlobalTheory.LeviModulus.topUA σ G.V'.J).2.2.1
  haveI : MeasurableMul (UA σ G.V'.J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI := hT.geo.hM'.haar
  have hrep : ∀ γ ∈ ratU σ G.V'.J, ∃! t, t ∈ T ∧ γ * t⁻¹ ∈ ratStab σ G.V'.J H.x := by
    intro γ hγ
    obtain ⟨t, ⟨ht, hl⟩, hu⟩ := hTr.2 γ hγ
    exact ⟨t, ⟨ht, mul_mem hγ (inv_mem (hTr.1 ht)), hl⟩, fun u hu' => hu u ⟨hu'.1, hu'.2.2⟩⟩
  obtain ⟨hdisj, hfd⟩ := translates_fundamentalDomain (μ := G.M'.μ) (Γ := ratU σ G.V'.J) (P := ratStab σ G.V'.J H.x)
    (fun γ hγ => hγ.1) hTr.1 hrep hT.geo.hM'.dom
  refine ⟨_, hfd, (((b + 2 : ℕ) : ℝ) - 1) / 2, fun s hs h => ?_⟩
  have hθ : ∀ (t : T) g, theta om' Φ' (t.1 * g) h = theta om' Φ' g h := fun t g => by
    have := hinv t.1 (hTr.1 t.2) 1 (one_mem _) g h
    rwa [one_mul] at this
  have hθc : Continuous fun g => theta om' Φ' g h := hcont.comp (continuous_id.prodMk continuous_const)
  have hm : Measurable fun g => theta om' Φ' g h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2) :=
    hθc.measurable.mul ((Complex.measurable_ofReal.comp hfc.measurable).pow_const _)
  obtain ⟨C, N, hC0, hser⟩ := series_le_qht hiw hpos hES'
    (fun s₀ => by
      obtain ⟨k, U, Hol, C, N, h1, h2, -, h4⟩ := hloc s₀
      exact ⟨k, U, Hol, C, N, h1, h2, h4⟩) hTr hs
  obtain ⟨C₁, k, hC₁⟩ := hdecay N
  have hre : (s + (((b + 2 : ℕ) : ℂ) - 1) / 2).re = s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2 := by
    have e : (((b + 2 : ℕ) : ℂ) - 1) / 2 = (((((b + 2 : ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.add_re, Complex.ofReal_re]
  have hpt : ∀ g, ∑' t : T, ‖theta om' Φ' (t.1 * g) h * (hf (t.1 * g) : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)‖ₑ ≤
      ENNReal.ofReal (C * (C₁ * (ht h : ℝ) ^ k)) := by
    intro g
    have e : ∀ t : T, ‖theta om' Φ' (t.1 * g) h * (hf (t.1 * g) : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)‖ₑ =
        ENNReal.ofReal ‖theta om' Φ' g h‖ * ENNReal.ofReal (hf (t.1 * g) ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2)) := by
      intro t
      rw [← ofReal_norm_eq_enorm, norm_mul, hθ, Complex.norm_cpow_eq_rpow_re_of_pos (hpos _), hre,
        ENNReal.ofReal_mul (norm_nonneg _)]
    simp only [e]
    rw [ENNReal.tsum_mul_left]
    refine (mul_le_mul_right (hser g) _).trans ?_
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖theta om' Φ' g h‖ * (C * (qht g : ℝ) ^ N) = C * (‖theta om' Φ' g h‖ * (qht g : ℝ) ^ N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC₁ g h) hC0
  have hsumfin : ∑' t : T, ∫⁻ g in G.M'.dom,
      ‖theta om' Φ' (t.1 * g) h * (hf (t.1 * g) : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)‖ₑ ∂G.M'.μ ≠ ⊤ := by
    have hmt : ∀ t : T, Measurable fun g =>
        ‖theta om' Φ' (t.1 * g) h * (hf (t.1 * g) : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)‖ₑ :=
      fun t => (hm.comp (measurable_const_mul t.1)).enorm
    rw [← lintegral_tsum fun t : T => (hmt t).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  obtain ⟨hint, heq⟩ := unfold_translates hT.geo.hM'.dom.nullMeasurableSet hdisj hm.aestronglyMeasurable hsumfin
  refine ⟨?_, hint⟩
  rw [heq, GlobalTheory.ConeSmallCT.Bint]
  congr 1
  funext g
  simp only [hθ]
  rw [tsum_mul_left, (hasSum_eis hiw hES hTr hs g).tsum_eq]

end GlobalTheory.ConeSmallUnfEis

end
