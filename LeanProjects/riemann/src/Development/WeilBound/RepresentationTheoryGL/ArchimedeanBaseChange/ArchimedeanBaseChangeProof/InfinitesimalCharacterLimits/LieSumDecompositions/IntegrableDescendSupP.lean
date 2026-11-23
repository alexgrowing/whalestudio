import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.GrowPHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

noncomputable section

open NumberField MeasureTheory ComplexConjugate Filter Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

namespace Pair

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

def rmulEquiv (x : GA E N) : Quot (latticeGL E N) ≃ᵐ Quot (latticeGL E N) where
  toFun := rmul (latticeGL E N) x
  invFun := rmul (latticeGL E N) x⁻¹
  left_inv q := by rw [← rmul_mul, mul_inv_cancel, rmul_one]
  right_inv q := by rw [← rmul_mul, inv_mul_cancel, rmul_one]
  measurable_toFun := measurable_rmul x
  measurable_invFun := measurable_rmul x⁻¹

theorem descend_rmul {f : GA E N → ℂ} (hf : LeftInv (latticeGL E N) f) (x : GA E N) (q : Quot (latticeGL E N)) :
    descend (latticeGL E N) f (rmul (latticeGL E N) x q) = f (q.out * x) := by
  have hq : rmul (latticeGL E N) x q = mk (latticeGL E N) (q.out * x) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq, hf.descend_mk]

theorem exists_eps (a : ℕ → ℝ) (N : ℕ) (h : ∀ r, 0 < r → r < N → 0 < a r) :
    ∃ ε > 0, ∀ r, 0 < r → r < N → ε < a r := by
  induction N with
  | zero => exact ⟨1, one_pos, fun r _ h => absurd h (Nat.not_lt_zero r)⟩
  | succ n ih =>
    obtain ⟨ε, hε, hε'⟩ := ih fun r h1 h2 => h r h1 (Nat.lt_succ_of_lt h2)
    by_cases hn : 0 < n
    · refine ⟨min ε (a n / 2), lt_min hε (half_pos (h n hn (Nat.lt_succ_self n))), fun r h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h3 | rfl
      · exact (min_le_left _ _).trans_lt (hε' r h1 h3)
      · exact (min_le_right _ _).trans_lt (half_lt_self (h r h1 (Nat.lt_succ_self r)))
    · refine ⟨ε, hε, fun r h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h3 | rfl
      · exact hε' r h1 h3
      · exact absurd h1 hn

def supP (K : Set (GA E N)) (f g : GA E N → ℂ) (y : GA E N) : ℝ :=
  sSup ((fun k => ‖f (y * k)‖ * ‖g (y * k)‖) '' K)

omit [IsTotallyComplex E] in
theorem continuous_supP {K : Set (GA E N)} (hK : IsCompact K) {f g : GA E N → ℂ} (hf : Continuous f)
    (hg : Continuous g) : Continuous (supP K f g) :=
  hK.continuous_sSup (f := fun y k => ‖f (y * k)‖ * ‖g (y * k)‖)
    ((hf.comp continuous_mul).norm.mul (hg.comp continuous_mul).norm)

omit [IsTotallyComplex E] in
theorem le_supP {K : Set (GA E N)} (hK : IsCompact K) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g)
    (y : GA E N) {k : GA E N} (hk : k ∈ K) : ‖f (y * k)‖ * ‖g (y * k)‖ ≤ supP K f g y :=
  le_csSup (hK.image ((hf.comp (continuous_const.mul continuous_id)).norm.mul
    (hg.comp (continuous_const.mul continuous_id)).norm)).bddAbove ⟨k, hk, rfl⟩

omit [IsTotallyComplex E] in
theorem supP_nonneg (K : Set (GA E N)) (f g : GA E N → ℂ) (y : GA E N) : 0 ≤ supP K f g y :=
  Real.sSup_nonneg (by rintro _ ⟨k, -, rfl⟩; positivity)

theorem supP_left {K : Set (GA E N)} {f g : GA E N → ℂ} (hf : LeftInv (latticeGL E N) f)
    (hg : LeftInv (latticeGL E N) g) : ∀ γ ∈ latticeGL E N, ∀ y, supP K f g (γ * y) = supP K f g y := by
  intro γ hγ y
  unfold supP
  simp only [mul_assoc, hf γ hγ, hg γ hγ]

omit [IsTotallyComplex E] in
theorem bnd_supP {K : Set (GA E N)} (hK : IsCompact K) (hK0 : K.Nonempty) {f g : GA E N → ℂ}
    {m₁ m₂ : ℕ → ℝ} (hf : An.Bnd f m₁) (hg : An.Bnd g m₂) :
    An.Bnd (fun y => (supP K f g y : ℂ)) (m₁ + m₂) := by
  intro ω hω hωB t₀ Q hQ
  have hQ' : IsCompact ((fun p : GA E N × GA E N => p.1 * p.2) '' (Q ×ˢ K)) :=
    (hQ.prod hK).image continuous_mul
  obtain ⟨C₁, hC₁⟩ := hf ω hω hωB t₀ _ hQ'
  obtain ⟨C₂, hC₂⟩ := hg ω hω hωB t₀ _ hQ'
  refine ⟨C₁ * C₂, fun b hb x hx q hq => ?_⟩
  rw [Complex.norm_real, Real.norm_of_nonneg (supP_nonneg _ _ _ _)]
  refine csSup_le (hK0.image _) ?_
  rintro _ ⟨k, hk, rfl⟩
  have hqk : q * k ∈ (fun p : GA E N × GA E N => p.1 * p.2) '' (Q ×ˢ K) := ⟨(q, k), ⟨hq, hk⟩, rfl⟩
  have h1 := hC₁ b hb x hx _ hqk
  have h2 := hC₂ b hb x hx _ hqk
  have e : b * An.tor E x * q * k = b * An.tor E x * (q * k) := mul_assoc _ _ _
  simp only [e]
  have h3 := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  refine h3.trans (le_of_eq ?_)
  have e2 : ∑ r ∈ Finset.range N, (m₁ + m₂) r * An.sr x r =
      ∑ r ∈ Finset.range N, m₁ r * An.sr x r + ∑ r ∈ Finset.range N, m₂ r * An.sr x r := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Pi.add_apply, add_mul]
  rw [e2, Real.exp_add]
  ring

theorem lintegral_supP_lt_top (hI : IntBnd) {K : Set (GA E N)} (hK : IsCompact K) (hK0 : K.Nonempty)
    {f g : GA E N → ℂ} (hf : GrowP f) (hg : GrowQ g) :
    ∫⁻ y in stdDom (latticeGL E N), ENNReal.ofReal (supP K f g y) ∂(Measure.haar : Measure (GA E N)) < ⊤ := by
  obtain ⟨hfc, hfl, hfb⟩ := hf
  obtain ⟨hgc, hgl, κ, hκ, hgb⟩ := hg
  obtain ⟨ε, hε, hε'⟩ := exists_eps (fun r => An.rho E N r - κ r) N (fun r h1 h2 => sub_pos.2 (hκ r h1 h2))
  refine hI E N _ (continuous_supP hK hfc hgc) (supP_nonneg K f g) (supP_left hfl hgl) _ ?_
    (bnd_supP hK hK0 (hfb ε hε) hgb)
  intro r h1 h2
  have := hε' r h1 h2
  simp only [Pi.add_apply]
  linarith

theorem integrable_pet (hI : IntBnd) {f g : GA E N → ℂ} (hf : GrowP f) (hg : GrowQ g) :
    Integrable (fun q => descend (latticeGL E N) f q * conj (descend (latticeGL E N) g q))
      (quotMeasure (latticeGL E N) (Measure.haar : Measure (GA E N))) := by
  have hfl : LeftInv (latticeGL E N) f := hf.2.1
  have hgl : LeftInv (latticeGL E N) g := hg.2.1
  have hl : LeftInv (latticeGL E N) (fun y => f y * conj (g y)) := fun γ hγ y => by
    simp only [hfl γ hγ, hgl γ hγ]
  have e : (fun q => descend (latticeGL E N) f q * conj (descend (latticeGL E N) g q)) =
      descend (latticeGL E N) (fun y => f y * conj (g y)) := rfl
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [aestronglyMeasurable_quotMeasure_iff_lift, hl.lift_descend]
    exact (hf.1.mul (Complex.continuous_conj.comp hg.1)).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm, lintegral_quotMeasure (isFundamentalDomain_stdDom _ _)]
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_)
      (lintegral_supP_lt_top hI isCompact_singleton (Set.singleton_nonempty 1) hf hg)
    rw [hl.descend_mk, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, Complex.norm_conj]
    simpa using le_supP isCompact_singleton hf.1 hg.1 y (Set.mem_singleton 1)

def cX (X : Lie E N) (t : ℝ) : GA E N := infGL E N (GlobalTheory.ExpDeriv.expGL X t)

theorem continuous_cX (X : Lie E N) : Continuous (cX X) := by
  have hv : Continuous fun t : ℝ => NormedSpace.exp (t • Matrix.of X) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  have hinv : ∀ t, (GlobalTheory.ExpDeriv.expGL X t)⁻¹ = GlobalTheory.ExpDeriv.expGL X (-t) := fun t =>
    (eq_inv_of_mul_eq_one_right (by rw [← GlobalTheory.ExpDeriv.expGL_add, add_neg_cancel, GlobalTheory.ExpDeriv.expGL_zero])).symm
  have he : Continuous (GlobalTheory.ExpDeriv.expGL X) := Units.continuous_iff.2 ⟨hv, by
    simp only [hinv, GlobalTheory.ExpDeriv.expGL_val]
    exact hv.comp continuous_neg⟩
  exact GlobalTheory.CuspQuot.continuous_infGL.comp he

theorem cX_zero (X : Lie E N) : cX X 0 = 1 := by
  simp only [cX, GlobalTheory.ExpDeriv.expGL_zero, map_one]

theorem descend_eq_sec {X : Type*} {φ : GA E N → X} (hl : LeftInv (latticeGL E N) φ) :
    descend (latticeGL E N) φ = φ ∘ sec (latticeGL E N) := by
  funext q
  conv_lhs => rw [← mk_sec q]
  exact hl.descend_mk _

theorem aesm_descend {X : Type*} [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] {φ : GA E N → X} (hc : Continuous φ) (hl : LeftInv (latticeGL E N) φ) :
    AEStronglyMeasurable (descend (latticeGL E N) φ)
      (quotMeasure (latticeGL E N) (Measure.haar : Measure (GA E N))) := by
  rw [descend_eq_sec hl]
  exact (hc.measurable.comp measurableEmbedding_sec.measurable).aestronglyMeasurable

theorem integrable_descend_supP (hI : IntBnd) {K : Set (GA E N)} (hK : IsCompact K) (hK0 : K.Nonempty)
    {f g : GA E N → ℂ} (hf : GrowP f) (hg : GrowQ g) :
    Integrable (descend (latticeGL E N) (supP K f g))
      (quotMeasure (latticeGL E N) (Measure.haar : Measure (GA E N))) := by
  have hl : LeftInv (latticeGL E N) (supP K f g) := supP_left hf.2.1 hg.2.1
  refine ⟨?_, ?_⟩
  · exact aesm_descend (continuous_supP hK hf.1 hg.1) hl
  rw [hasFiniteIntegral_iff_enorm, lintegral_quotMeasure (isFundamentalDomain_stdDom _ _)]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) (lintegral_supP_lt_top hI hK hK0 hf hg)
  rw [hl.descend_mk, ← ofReal_norm, Real.norm_of_nonneg (supP_nonneg _ _ _ _)]

end Pair

open Pair in
theorem pairRt : PairRt := by
  intro E _ _ _ N x f g hf hg
  have : (Measure.haar : Measure (GA E N)).IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E N _
  have hmp : MeasurePreserving (rmulEquiv x) (quotMeasure (latticeGL E N) (Measure.haar : Measure (GA E N)))
      (quotMeasure (latticeGL E N) (Measure.haar : Measure (GA E N))) := measurePreserving_rmul x
  have hg' : LeftInv (latticeGL E N) fun y => g (y * x⁻¹) := LeftInv.mul_right (Γ := latticeGL E N) hg x⁻¹
  unfold pr pet
  refine (integral_congr_ae (Eventually.of_forall fun q => ?_)).trans (hmp.integral_comp'
    (fun q => descend (latticeGL E N) f q * conj (descend (latticeGL E N) (fun y => g (y * x⁻¹)) q)))
  change f (q.out * x) * conj (g q.out) = descend (latticeGL E N) f (rmul (latticeGL E N) x q) *
    conj (descend (latticeGL E N) (fun y => g (y * x⁻¹)) (rmul (latticeGL E N) x q))
  rw [descend_rmul hf, descend_rmul hg', mul_inv_cancel_right]

open Pair in
theorem pairLin_of (hI : IntBnd) : PairLin := by
  intro E _ _ _ N
  refine ⟨fun f₁ f₂ g c h₁ h₂ hg => ⟨?_, ?_⟩, fun f g₁ g₂ c hf h₁ h₂ => ⟨?_, ?_⟩⟩
  · unfold pr pet
    rw [← integral_add (integrable_pet hI h₁ hg) (integrable_pet hI h₂ hg)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [descend, Pi.add_apply, add_mul]
  · unfold pr pet
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [descend, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · unfold pr pet
    rw [← integral_add (integrable_pet hI hf h₁) (integrable_pet hI hf h₂)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [descend, Pi.add_apply, map_add, mul_add]
  · unfold pr pet
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [descend, Pi.smul_apply, smul_eq_mul, map_mul]
    ring

open Pair in
theorem pairLie_of (hI : IntBnd) : PairLie := by
  intro E _ _ _ N X χ u hχ hXχ hu hXu
  have hc : Continuous (cX (E := E) (N := N) X) := continuous_cX X
  have hc0 : cX (E := E) (N := N) X 0 = 1 := cX_zero X
  set c := cX (E := E) (N := N) X with hcdef
  set K : Set (GA E N) := c '' Set.Icc (-1) 1 with hKdef
  have hK : IsCompact K := isCompact_Icc.image hc
  have hK0 : K.Nonempty := ⟨c 0, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
  set Γ := latticeGL E N with hΓ
  set μq := quotMeasure Γ (Measure.haar : Measure (GA E N)) with hμq
  set Xχ := act (.lie X) χ with hXχdef
  set Xu := act (.lie X) u with hXudef
  let F : ℝ → Quot Γ → ℂ := fun t q => χ.1 (q.out * c t) * conj (u.1 (q.out * c t))
  let F' : ℝ → Quot Γ → ℂ := fun t q => Xχ.1 (q.out * c t) * conj (u.1 (q.out * c t)) +
    χ.1 (q.out * c t) * conj (Xu.1 (q.out * c t))
  let bound : Quot Γ → ℝ := fun q => supP K Xχ.1 u.1 q.out + supP K χ.1 Xu.1 q.out
  have hJ : ∀ t, ∫ q, F t q ∂μq = pr χ.1 u.1 := by
    intro t
    have h := pairRt E N (c t) χ.1 (fun y => u.1 (y * c t)) hχ.2.1
      (LeftInv.mul_right (Γ := latticeGL E N) hu.2.1 _)
    simp only [inv_mul_cancel_right] at h
    exact h
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μq := Eventually.of_forall fun t =>
    aesm_descend (φ := fun y => χ.1 (y * c t) * conj (u.1 (y * c t)))
      ((hχ.1.comp (continuous_id.mul continuous_const)).mul
        (Complex.continuous_conj.comp (hu.1.comp (continuous_id.mul continuous_const))))
      (fun γ hγ y => by simp only [mul_assoc, hχ.2.1 γ hγ, hu.2.1 γ hγ])
  have e0 : F 0 = fun q => descend Γ χ.1 q * conj (descend Γ u.1 q) := by
    funext q; simp only [F, hc0, mul_one, descend]
  have hF_int : Integrable (F 0) μq := by rw [e0]; exact integrable_pet hI hχ hu
  have e0' : F' 0 = fun q => (descend Γ Xχ.1 q * conj (descend Γ u.1 q) +
      descend Γ χ.1 q * conj (descend Γ Xu.1 q)) := by
    funext q; simp only [F', hc0, mul_one, descend]
  have hF'_meas : AEStronglyMeasurable (F' 0) μq := by
    rw [e0']
    exact ((integrable_pet hI hXχ hu).add (integrable_pet hI hχ hXu)).aestronglyMeasurable
  have h_bound : ∀ᵐ q ∂μq, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖F' t q‖ ≤ bound q := by
    refine Eventually.of_forall fun q t ht => ?_
    have hk : c t ∈ K := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_conj]
      exact le_supP hK hXχ.1 hu.1 q.out hk
    · rw [norm_mul, Complex.norm_conj]
      exact le_supP hK hχ.1 hXu.1 q.out hk
  have bound_int : Integrable bound μq :=
    (integrable_descend_supP hI hK hK0 hXχ hu).add (integrable_descend_supP hI hK hK0 hχ hXu)
  have h_diff : ∀ᵐ q ∂μq, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (F · q) (F' t q) t := by
    refine Eventually.of_forall fun q t _ => ?_
    have h1 := GlobalTheory.ExpDeriv.hasDerivAt_along X χ q.out t
    have h2 := (GlobalTheory.ExpDeriv.hasDerivAt_along X u q.out t).star
    exact h1.mul h2
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μq) (F := F) (x₀ := 0)
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)) hF_meas hF_int hF'_meas h_bound
    bound_int h_diff
  have hconst : (fun t => ∫ q, F t q ∂μq) = fun _ => pr χ.1 u.1 := funext hJ
  have hd := hmain.2
  rw [hconst] at hd
  have hz : ∫ q, F' 0 q ∂μq = 0 := hd.unique (hasDerivAt_const 0 _)
  rw [e0', integral_add (integrable_pet hI hXχ hu) (integrable_pet hI hχ hXu)] at hz
  exact eq_neg_of_add_eq_zero_left hz

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
