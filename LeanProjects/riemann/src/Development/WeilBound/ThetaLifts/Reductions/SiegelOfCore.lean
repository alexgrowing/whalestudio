import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.WeilBound.ThetaLifts.Reductions.SiegelHaar

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)
open PositivityTheory.ThKEst PositivityTheory.ThKEst.Sieg

namespace PositivityTheory.ThKR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

theorem iwasawa_of (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {K : Subgroup (GAd σ J)}
    (hPK : ∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) :
    ∀ g, ∃ p ∈ minParOne σ J X, ∃ t a, (∀ i, 0 < t i) ∧ IsTorusElt σ J X Y t a ∧ ∃ k ∈ K, g = p * a * k := by
  obtain ⟨a, ha⟩ := exists_isTorus h hJ hW
  obtain ⟨τ, -, -, -, -, hτP⟩ := exists_tau h hJ hW ha
  intro g
  obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
  let P : minParSub X h hJ hW := ⟨p, hp⟩
  exact ⟨p * (a (τ P))⁻¹, hτP P, fun i => Real.exp (τ P i), a (τ P), fun i => Real.exp_pos _, ha.tor _, k, hk,
    by rw [inv_mul_cancel_right]⟩

theorem isClosed_logCone (c : ℝ) : IsClosed {s : Fin r → ℝ | (fun i => Real.exp (s i)) ∈ cone r c} := by
  have e : {s : Fin r → ℝ | (fun i => Real.exp (s i)) ∈ cone r c} =
      (⋂ i : Fin r, ⋂ j : Fin r, ⋂ (_ : j.val = i.val + 1), {s : Fin r → ℝ | c * Real.exp (s j) ≤ Real.exp (s i)}) ∩
        ⋂ i : Fin r, ⋂ (_ : i.val + 1 = r), {s : Fin r → ℝ | c ≤ Real.exp (s i)} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨fun i => Real.exp_pos _, h.1, h.2⟩⟩
  rw [e]
  exact IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le (by fun_prop) (by fun_prop)) (isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_le (by fun_prop) (by fun_prop))

open scoped Pointwise in

theorem siegelSet_eq (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J}
    (ha : IsTorus σ J X Y a) (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ) :
    siegelSet σ J X Y Ω c K = Ω * a '' {s : Fin r → ℝ | (fun i => Real.exp (s i)) ∈ cone r c} * (K : Set (GAd σ J)) := by
  ext g
  constructor
  · rintro ⟨p, hp, t, ht, b, hb, k, hk, rfl⟩
    have et : (fun i => Real.exp (Real.log (t i))) = t := funext fun i => Real.exp_log (ht.1 i)
    have h3 : IsTorusElt σ J X Y t (a fun i => Real.log (t i)) := by
      have h4 := ha.tor (fun i => Real.log (t i))
      beta_reduce at h4
      rwa [et] at h4
    have hb' : b = a (fun i => Real.log (t i)) := isTorusElt_unique h hJ hW hb h3
    have hs : (fun i => Real.log (t i)) ∈ {s : Fin r → ℝ | (fun i => Real.exp (s i)) ∈ cone r c} := by
      show (fun i => Real.exp (Real.log (t i))) ∈ cone r c
      rw [et]
      exact ht
    exact ⟨p * b, ⟨p, hp, b, ⟨_, hs, hb'.symm⟩, rfl⟩, k, hk, rfl⟩
  · rintro ⟨_, ⟨p, hp, _, ⟨s, hs, rfl⟩, rfl⟩, k, hk, rfl⟩
    exact ⟨p, hp, _, hs, a s, ha.tor s, k, hk, rfl⟩

theorem isClosed_siegelSet (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {K : Subgroup (GAd σ J)}
    {Ω : Set (GAd σ J)} {c : ℝ} (hK : IsCompact (K : Set (GAd σ J))) (hΩ : IsCompact Ω) (hΩP : Ω ⊆ minParOne σ J X)
    (hc : 0 < c) : IsClosed (siegelSet σ J X Y Ω c K) := by
  obtain ⟨a, ha⟩ := exists_isTorus h hJ hW
  obtain ⟨τ, hτc, -, hτa, -, -⟩ := exists_tau h hJ hW ha
  have hP : IsClosed ((minParSub X h hJ hW : Subgroup (GAd σ J)) : Set (GAd σ J)) := isClosed_minPar h hJ hW
  have hsc : Continuous (ha.sub h hJ hW) := ha.cont.subtype_mk _
  have h1 : IsClosed (ha.sub h hJ hW '' {s : Fin r → ℝ | (fun i => Real.exp (s i)) ∈ cone r c}) :=
    PositivityTheory.ThKR.Sieg.isClosed_image_section τ hτc _ hsc hτa (isClosed_logCone c)
  have h2 : IsClosed (a '' {s : Fin r → ℝ | (fun i => Real.exp (s i)) ∈ cone r c}) := by
    have := hP.isClosedEmbedding_subtypeVal.isClosedMap _ h1
    rwa [← Set.image_comp] at this
  rw [siegelSet_eq h hJ hW ha]
  exact (h2.mul_left_of_isCompact hΩ).mul_right_of_isCompact hK

theorem measurableSet_cone (r : ℕ) (c : ℝ) : MeasurableSet (cone r c) := by
  have : cone r c = (⋂ i, {t : Fin r → ℝ | 0 < t i}) ∩ ((⋂ i, ⋂ j, ⋂ (_ : (j : Fin r).val = (i : Fin r).val + 1),
      {t : Fin r → ℝ | c * t j ≤ t i}) ∩ ⋂ i, ⋂ (_ : (i : Fin r).val + 1 = r), {t : Fin r → ℝ | c ≤ t i}) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [this]
  exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_const.mul (measurable_pi_apply j)) (measurable_pi_apply i)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurableSet_le measurable_const (measurable_pi_apply i)))

theorem cone_lower {r : ℕ} {c : ℝ} (h3 : 0 ≤ c) {u : Fin r → ℝ} (hu : u ∈ cone r c) :
    ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → c ^ (k + 1) ≤ u i := by
  intro k
  induction k with
  | zero => intro i hi; simpa using hu.2.2 i (by omega)
  | succ k ih =>
    intro i hi
    have hj : i.val + 1 < r := by omega
    have h1 := ih ⟨i.val + 1, hj⟩ (by simp; omega)
    have h2 := hu.2.1 i ⟨i.val + 1, hj⟩ rfl
    calc c ^ (k + 1 + 1) = c * c ^ (k + 1) := by ring
      _ ≤ c * u ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 h3
      _ ≤ u i := h2

theorem lintegral_logCone (F : Type) [Field F] [NumberField F] (n r : ℕ) {c : ℝ} (hc : 0 < c)
    (h : (Fin r → ℝ) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ s in {s : Fin r → ℝ | (fun i => Real.exp (s i)) ∈ cone r c}, h (fun i => Real.exp (s i)) *
        ENNReal.ofReal (Real.exp (-(2 * (Module.finrank ℚ F : ℝ) * rho2 n s))) =
      ∫⁻ u in cone r c, h u * ENNReal.ofReal ((modulus F n u * ∏ i, u i)⁻¹) := by
  let Φ : (Fin r → ℝ) → Fin r → ℝ := fun s i => Real.exp (s i)
  let Φ' : (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] Fin r → ℝ := fun s =>
    LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.diagonal (Φ s)))
  set D := {s : Fin r → ℝ | (fun i => Real.exp (s i)) ∈ cone r c} with hD
  have hDm : MeasurableSet D :=
    (measurableSet_cone r c).preimage (measurable_pi_lambda _ fun i => Real.measurable_exp.comp (measurable_pi_apply i))
  have hd : ∀ s ∈ D, HasFDerivWithinAt Φ (Φ' s) D s := fun s _ => by
    refine HasFDerivAt.hasFDerivWithinAt (hasFDerivAt_pi'.2 fun i => ?_)
    have := (hasFDerivAt_apply (𝕜 := ℝ) i s).exp
    refine this.congr_fderiv ?_
    ext v
    simp [Φ', Φ, Matrix.mulVec_diagonal]
  have hi : Set.InjOn Φ D := fun s _ t _ e => funext fun i => Real.exp_injective (congrFun e i)
  have himg : Φ '' D = cone r c := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hu
      refine ⟨fun i => Real.log (u i), ?_, funext fun i => Real.exp_log (hu.1 i)⟩
      change (fun i => Real.exp (Real.log (u i))) ∈ cone r c
      simpa [Real.exp_log (hu.1 _)] using hu
  rw [← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hDm hd hi]
  refine lintegral_congr fun s => ?_
  have e2 : (Φ' s).det = ∏ i, Φ s i := by
    simp [Φ', ContinuousLinearMap.det, LinearMap.det_toLin']
  have e3 : 0 < ∏ i, Φ s i := Finset.prod_pos fun i _ => Real.exp_pos _
  have e4 : modulus F n (Φ s) = Real.exp (2 * Module.finrank ℚ F * rho2 n s) := modulus_exp F n s
  rw [e2, abs_of_pos e3, e4, mul_left_comm, ← ENNReal.ofReal_mul e3.le]
  congr 2
  rw [mul_inv, mul_left_comm, mul_inv_cancel₀ e3.ne', mul_one, ← Real.exp_neg]

theorem lintegral_cone_lt_top (F : Type) [Field F] [NumberField F] {n r : ℕ} (hr : 2 * r ≤ n) {c : ℝ} (hc : 0 < c) :
    ∫⁻ u in cone r c, ENNReal.ofReal ((modulus F n u * ∏ i, u i)⁻¹) < ⊤ := by
  have hd0 : (1 : ℝ) ≤ (Module.finrank ℚ F : ℝ) := Nat.one_le_cast.2 (Module.finrank_pos (R := ℚ) (M := F))
  let ex : Fin r → ℝ := fun i => -(2 * (Module.finrank ℚ F : ℝ) * ((n : ℝ) - 2 * (i.val : ℝ) - 1)) - 1
  have hex : ∀ i, ex i < -1 := fun i => by
    have h1 : (i.val : ℝ) + 1 ≤ r := by exact_mod_cast i.isLt
    have h2 : (2 * r : ℝ) ≤ n := by exact_mod_cast hr
    have : 0 < 2 * (Module.finrank ℚ F : ℝ) * ((n : ℝ) - 2 * (i.val : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    simp only [ex]
    linarith
  let b : Fin r → ℝ := fun i => c ^ (r - i.val)
  have hb : ∀ i, 0 < b i := fun i => pow_pos hc _
  have hBm : MeasurableSet (Set.univ.pi fun i => Set.Ici (b i)) := MeasurableSet.univ_pi fun i => measurableSet_Ici
  have hsub : cone r c ⊆ Set.univ.pi fun i => Set.Ici (b i) := fun u hu i _ => by
    have h1 := cone_lower hc.le hu (r - i.val - 1) i (by omega)
    have e : r - i.val = r - i.val - 1 + 1 := by omega
    change c ^ (r - i.val) ≤ u i
    rw [e]
    exact h1
  have hB : ∀ u ∈ Set.univ.pi (fun i => Set.Ici (b i)), ENNReal.ofReal ((modulus F n u * ∏ i, u i)⁻¹) =
      ENNReal.ofReal (∏ i, u i ^ ex i) := fun u hu => by
    congr 1
    have hpos : ∀ i, 0 < u i := fun i => (hb i).trans_le (hu i (Set.mem_univ i))
    rw [modulus, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_add_one (hpos i).ne', ← Real.rpow_neg (hpos i).le]
    congr 1
    simp only [ex]
    push_cast
    ring
  have hint : Integrable (fun u : Fin r → ℝ => ∏ i, u i ^ ex i)
      (volume.restrict (Set.univ.pi fun i => Set.Ici (b i))) := by
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod (f := fun i (x : ℝ) => x ^ ex i) fun i =>
      Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_Ioi_rpow_of_lt (hex i) (hb i))
  calc ∫⁻ u in cone r c, ENNReal.ofReal ((modulus F n u * ∏ i, u i)⁻¹)
      ≤ ∫⁻ u in Set.univ.pi (fun i => Set.Ici (b i)), ENNReal.ofReal ((modulus F n u * ∏ i, u i)⁻¹) :=
        lintegral_mono_set hsub
    _ = ∫⁻ u in Set.univ.pi (fun i => Set.Ici (b i)), ENNReal.ofReal (∏ i, u i ^ ex i) := setLIntegral_congr_fun hBm hB
    _ < ⊤ := hint.lintegral_lt_top

theorem siegel_measure (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {K : Subgroup (GAd σ J)}
    {Ω : Set (GAd σ J)} {c : ℝ} (hK : IsCompact (K : Set (GAd σ J))) (hΩ : IsCompact Ω) (hΩP : Ω ⊆ minParOne σ J X)
    (hc : 0 < c) (hPK : ∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) (hG : GoodPosition σ J X Y K) :
    ∀ μ : Measure (GAd σ J), μ.IsHaarMeasure → μ (siegelSet σ J X Y Ω c K) < ⊤ ∧
      ∃ C : ℝ≥0, ∀ (f : GAd σ J → ℝ≥0∞) (h : (Fin r → ℝ) → ℝ≥0∞), Measurable h →
        (∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ K, f (p * a * k) ≤ h t) →
        ∫⁻ g in siegelSet σ J X Y Ω c K, f g ∂μ ≤
          C * ∫⁻ t in cone r c, h t * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) := by
  intro μ hμ
  obtain ⟨a, ha⟩ := exists_isTorus h hJ hW
  obtain ⟨τ, hτc, hτm, hτa, hτ0, -⟩ := exists_tau h hJ hW ha
  have hP : IsClosed ((minParSub X h hJ hW : Subgroup (GAd σ J)) : Set (GAd σ J)) := isClosed_minPar h hJ hW
  have : LocallyCompactSpace (minParSub X h hJ hW) := hP.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let ρ : (Fin r → ℝ) → ℝ := fun s => 2 * (Module.finrank ℚ F : ℝ) * rho2 n s
  have hρ : Continuous ρ := by
    simp only [ρ, rho2]
    fun_prop
  have hρa : ∀ s t, ρ (s + t) = ρ s + ρ t := fun s t => by
    simp only [ρ, rho2, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hsub : ∀ s t, ha.sub h hJ hW (s + t) = ha.sub h hJ hW s * ha.sub h hJ hW t := fun s t =>
    Subtype.ext (ha.add s t)
  obtain ⟨C, hC⟩ := PositivityTheory.ThKR.Sieg.lintegral_siegel_le μ (minParSub X h hJ hW) K hP hK (fun g => hPK g) τ hτc hτm
    (ha.sub h hJ hW) (ha.cont.subtype_mk _) hsub hτa ρ hρ hρa (fun s => map_mul_torus h hJ hW ha _ s) hΩ
    (fun p hp => ⟨minParOne_subset (hΩP hp), hτ0 p (hΩP hp)⟩)
    (fun m hm t => Subtype.ext (commute_of_goodPosition h hJ hW ha hK hG m.2 hm t))
  have hS : MeasurableSet (siegelSet σ J X Y Ω c K) := (isClosed_siegelSet h hJ hW hK hΩ hΩP hc).measurableSet
  have hSΩ : ∀ g ∈ siegelSet σ J X Y Ω c K, ∃ p ∈ Ω,
      ∃ t ∈ {s : Fin r → ℝ | (fun i => Real.exp (s i)) ∈ cone r c}, ∃ k ∈ K,
        g = p * (ha.sub h hJ hW t : GAd σ J) * k := by
    intro g hg
    rw [siegelSet_eq h hJ hW ha] at hg
    obtain ⟨_, ⟨p, hp, _, ⟨s, hs, rfl⟩, rfl⟩, k, hk, rfl⟩ := hg
    exact ⟨p, hp, s, hs, k, hk, rfl⟩
  have key : ∀ (f : GAd σ J → ℝ≥0∞) (h : (Fin r → ℝ) → ℝ≥0∞), Measurable h →
      (∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ K, f (p * a * k) ≤ h t) →
      ∫⁻ g in siegelSet σ J X Y Ω c K, f g ∂μ ≤
        C * ∫⁻ t in cone r c, h t * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) := by
    intro f h' hh hf
    have hh' : Measurable fun s : Fin r → ℝ => h' fun i => Real.exp (s i) :=
      hh.comp (measurable_pi_lambda _ fun i => Real.measurable_exp.comp (measurable_pi_apply i))
    have e := hC _ _ (isClosed_logCone c).measurableSet hS hSΩ f (fun s => h' fun i => Real.exp (s i)) hh'
      (fun p hp s hs k hk => hf p hp _ hs (a s) (ha.tor s) k hk)
    rwa [lintegral_logCone F n r hc h' hh] at e
  refine ⟨?_, C, key⟩
  have e := key (fun _ => 1) (fun _ => 1) measurable_const (fun _ _ _ _ _ _ _ _ => le_rfl)
  simp only [one_mul, setLIntegral_const] at e
  exact lt_of_le_of_lt (by simpa using e) (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (lintegral_cone_lt_top F (two_mul_le_of_wittFrame (sigma_sigma h) hJ hW) hc))

theorem siegel_of_core (hC : SiegelCore) : GlobalTheory.Published.SiegelSetUnitary := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨K, Ω, c, hK, hΩ, hΩP, hc, hPK, hG, hcov, hconj, hht, hrap⟩ := hC F E σ h n J hJ r X Y hW
  exact ⟨K, Ω, c, hK, hΩ, hΩP, hc, iwasawa_of h hJ hW hPK, isClosed_siegelSet h hJ hW hK hΩ hΩP hc, hcov, hconj,
    siegel_measure h hJ hW hK hΩ hΩP hc hPK hG, hht, hrap⟩

end PositivityTheory.ThKR

end
