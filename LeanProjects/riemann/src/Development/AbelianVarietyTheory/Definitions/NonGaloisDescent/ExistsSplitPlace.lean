import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

namespace GlobalTheory.TypeRec.Model

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.TypeRec.factG

section Compl
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [hp : Fact p.Prime]

local notation "K" => HeightOneSpectrum.adicCompletion F w

theorem emb_surjective (hw : (p : 𝓞 F) ∈ w.asIdeal) (h2 : (p : 𝓞 F) ∉ w.asIdeal ^ 2)
    (hN : Ideal.absNorm w.asIdeal = p) : Function.Surjective (Formalism.BasicNotions.Examples₂.LocF.emb w p hw) := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hres : ∀ a : 𝓞 F, ∃ m : ℤ, a - m ∈ w.asIdeal := by
    intro a
    haveI := Formalism.BasicNotions.Examples₂.LocF.finite_quot w
    letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
    have hc : Fintype.card (𝓞 F ⧸ w.asIdeal) = p := by
      rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    obtain ⟨z, hz⟩ := (ZMod.ringEquivOfPrime (𝓞 F ⧸ w.asIdeal) hp.out hc).surjective (Ideal.Quotient.mk _ a)
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
    rw [map_intCast] at hz
    exact ⟨m, Ideal.Quotient.eq.1 (by rw [map_intCast, hz])⟩
  have hvp : WithZero.exp (-1 : ℤ) ≤ Valued.v (p : K) := by
    have e : (p : K) = algebraMap F K (algebraMap (𝓞 F) F (p : 𝓞 F)) := by simp
    rw [e, adic_valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    have h3 : ¬ w.intValuation (p : 𝓞 F) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
      h2 ((w.intValuation_le_pow_iff_mem _ 2).1 h)
    have h0 : w.intValuation (p : 𝓞 F) ≠ 0 := w.intValuation_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at h3 ⊢
    omega
  have step : ∀ y : K, Valued.v y ≤ 1 → ∃ (m : ℤ) (z : K), Valued.v z ≤ 1 ∧ y = m + p * z := by
    intro y hy
    obtain ⟨a, ha⟩ := adic_exists_approx w y hy
    obtain ⟨m, hm⟩ := hres a
    rw [adic_algebraMap_R] at ha
    have h1 : Valued.v (algebraMap F K (algebraMap (𝓞 F) F (a - m))) < 1 := by
      rw [adic_valued_algebraMap]
      exact (w.valuation_lt_one_iff_mem _).2 hm
    have h4 : Valued.v (y - m) < 1 := by
      have := Valuation.map_add_lt _ ha h1
      rwa [map_sub, map_sub, map_intCast, map_intCast, sub_add_sub_cancel] at this
    refine ⟨m, (y - m) / p, ?_, by rw [mul_div_cancel₀ _ hp0, add_sub_cancel]⟩
    rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hp0))]
    refine le_trans ?_ hvp
    by_cases h0 : Valued.v (y - m) = 0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h4
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
  have iter : ∀ (n : ℕ) (y : K), Valued.v y ≤ 1 → ∃ (m : ℤ) (z : K), Valued.v z ≤ 1 ∧ y = m + (p : K) ^ n * z := by
    intro n y hy
    induction n with
    | zero => exact ⟨0, y, hy, by simp⟩
    | succ n ih =>
      obtain ⟨m, z, hz, e⟩ := ih
      obtain ⟨m', z', hz', e'⟩ := step z hz
      exact ⟨m + p ^ n * m', z', hz', by rw [e, e', Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]; ring⟩
  letI := (Formalism.BasicNotions.Examples₂.LocF.emb w p hw).toAlgebra
  have : ContinuousSMul ℚ_[p] K := continuousSMul_of_algebraMap _ _ (Formalism.BasicNotions.Examples₂.LocF.emb_cont w p hw)
  have hcl : IsClosed (Set.range (Formalism.BasicNotions.Examples₂.LocF.emb w p hw)) :=
    (LinearMap.range (Algebra.linearMap ℚ_[p] K)).closed_of_finiteDimensional
  have hlt := Formalism.BasicNotions.Examples₂.LocF.norm_l_lt w p hw
  have hint : ∀ y : K, ‖y‖ ≤ 1 → y ∈ Set.range (Formalism.BasicNotions.Examples₂.LocF.emb w p hw) := by
    intro y hy
    rw [← hcl.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
    obtain ⟨m, z, hz, e⟩ := iter n y (Valued.toNormedField.norm_le_one_iff.1 hy)
    refine ⟨m, ⟨m, map_intCast _ _⟩, ?_⟩
    rw [dist_eq_norm, e, add_sub_cancel_left, norm_mul, norm_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (Valued.toNormedField.norm_le_one_iff.2 hz)) hn
  intro y
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < (‖y‖ + 1)⁻¹ by positivity) hlt
  obtain ⟨x, hx⟩ := hint ((p : K) ^ n * y) (by
    rw [norm_mul, norm_pow]
    have h1 : ‖(p : K)‖ ^ n * (‖y‖ + 1) ≤ 1 := by
      rw [← le_div_iff₀ (by positivity), one_div]; exact hn.le
    nlinarith [pow_nonneg (norm_nonneg (p : K)) n])
  refine ⟨x / (p : ℚ_[p]) ^ n, ?_⟩
  rw [map_div₀, hx, map_pow, map_natCast]
  field_simp

end Compl

theorem nonempty_ident (D : D7) : Nonempty (Ident D) := by
  have key : ∀ k v, Function.Surjective (Formalism.BasicNotions.Examples₂.LocF.emb (D.naut.plGw k v) (D.host.g k) (D.naut.plGw_over k v)) := by
    intro k v
    refine emb_surjective _ _ _ (fun h => ?_)
      (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v))
    have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (D.host.g_prime k).ne_zero
    have hs := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
      (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard (D.host.g_prime k) (D.nd.g_split k)).2
    have := hs (D.naut.plGw k v).asIdeal (by rw [← sq, Ideal.dvd_span_singleton]; exact h)
    exact (D.naut.plGw k v).isPrime.ne_top (Ideal.isUnit_iff.1 this)
  exact ⟨⟨fun k v => RingEquiv.ofBijective _ ⟨RingHom.injective _, key k v⟩,
    fun k v => Formalism.BasicNotions.Examples₂.LocF.emb_cont _ _ (D.naut.plGw_over k v)⟩⟩

theorem ident_unique (D : D7) (I J : Ident D) : I = J := by
  obtain ⟨i, hi⟩ := I
  obtain ⟨j, hj⟩ := J
  congr 1
  funext k v
  refine RingEquiv.ext (congrFun ((Padic.denseRange_ratCast _).equalizer (hi k v) (hj k v) (funext fun q => ?_)))
  simp

theorem cls_eq_of_iso {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (σ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (h : Nonempty (pull I k v σ ≅ pull I k v τ)) : GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls τ := by
  obtain ⟨e⟩ := h
  have e' := Representation.equivOfIso e
  refine congrArg (Sigma.mk n) (GlobalTheory.SmGL.IrrRep.cl_eq_iff.2 ⟨Representation.Equiv.mk e'.toLinearEquiv fun g => ?_⟩)
  have hg : Matrix.GeneralLinearGroup.map (I.i k v).toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom g) = g :=
    Units.ext (Matrix.ext fun a b => (I.i k v).apply_symm_apply _)
  rw [← hg]
  exact e'.toIntertwiningMap.isIntertwining' _

open Classical in

theorem exists_isRc (hL : GlobalTheory.Published.LocalLanglandsGL) {D : D7} (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) :
    ∃ rc, IsRc hL T I rc := by
  refine ⟨fun k v n π => if h : ∃ σ, Nonempty (π ≅ pull I k v σ) then
    (T.e _).symm (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 (D.naut.plGw k v)) (GlobalTheory.LocLanglands.cls h.choose))
    else D.naut.lpZero _, fun k v n σ π h => ?_⟩
  have h' : ∃ σ, Nonempty (π ≅ pull I k v σ) := ⟨σ, h⟩
  beta_reduce
  rw [dif_pos h', Equiv.apply_symm_apply, cls_eq_of_iso I k v _ σ ⟨h'.choose_spec.some.symm ≪≫ h.some⟩]

theorem isRc_dim {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} {I : Ident D} {rc}
    (h : IsRc hL T I rc) (k v n σ) : D.naut.lpDim (rc k v n (pull I k v σ)) = n := by
  rw [← T.dim, h k v n σ _ ⟨CategoryTheory.Iso.refl _⟩]
  obtain ⟨_, _, _, -, H⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
  exact H.dim _

theorem param_eq {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} {I : Ident D} {rc}
    (h : IsRc hL T I rc) {rep cp} (hc : IsComp I rep cp) {loc : D.what₂.FT → ∀ w, D.naut.LP w} {sat}
    (hr : GlobalTheory.HeightCounting.RowTrue hL D rep (fun σ w => T.e w (loc σ w)) sat) (σ k v) :
    loc σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v) := by
  obtain ⟨s, hs, τ, h1, h2⟩ := hc σ k v
  apply (T.e _).injective
  rw [h2, h k v _ τ _ ⟨CategoryTheory.Iso.refl _⟩]
  have key : ∀ (w) (hs : s.w = w) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E))),
      GlobalTheory.HeightCounting.IsLocS (rep σ).S s (hs ▸ τ) → T.e w (loc σ w) =
        GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls τ) := by
    rintro _ rfl τ h1
    exact hr.1 σ s τ h1
  exact key _ hs τ h1

theorem map_surj {D : D7} (I : Ident D) (k v) (n : ℕ) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) (I.i k v).toRingHom) := fun g =>
  ⟨Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom g,
    Units.ext (Matrix.ext fun _ _ => (I.i k v).apply_symm_apply _)⟩

theorem irrSm_pull {D : D7} (I : Ident D) (k v) {n : ℕ} (σ) : GlobalTheory.SerSys.IrrSm (pull I k v (n := n) σ) := by
  refine ⟨(GlobalTheory.GLp.Model.isIrrRep_iff _).2 (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp σ.irr _ (map_surj I k v n)), fun x => ?_⟩
  have hc : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) (I.i k v).toRingHom) :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => (I.cont k v).comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => (I.cont k v).comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  exact (σ.smooth x).preimage hc

theorem emb_le {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime]
    (f : ℚ_[p] →+* w.adicCompletion F) (hf : Continuous f) (t : ℚ_[p]) (ht : ‖t‖ ≤ 1) : ‖f t‖ ≤ 1 := by
  have hd : DenseRange (Int.cast : ℤ → ℤ_[p]) := PadicInt.denseRange_intCast
  refine hd.induction_on (p := fun z : ℤ_[p] => ‖f z‖ ≤ 1) ⟨t, ht⟩
    (isClosed_le (hf.comp continuous_subtype_val).norm continuous_const) fun m => ?_
  simpa using Formalism.BasicNotions.Examples₂.LocF.norm_int_le w m

theorem exists_iso {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (p : ℕ) [hp : Fact p.Prime]
    (hw : (p : 𝓞 L) ∈ s.w.asIdeal) (I : ℚ_[p] ≃+* s.w.adicCompletion L) (hI : Continuous I) :
    ∃ i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous i ∧
      ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  have hv : (p : 𝓞 (maximalRealSubfield L)) ∈ s.v.asIdeal := by
    rw [← s.split_alg_mem, map_natCast]; exact hw
  set f := Formalism.BasicNotions.Examples₂.LocF.emb s.v p hv
  have hf : Continuous f := Formalism.BasicNotions.Examples₂.LocF.emb_cont s.v p hv
  have hlt := Formalism.BasicNotions.Examples₂.LocF.norm_l_lt s.v p hv
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have key : ∀ x : L, f (I.symm (algebraMap L _ x)) = s.i x := by
    intro x
    set y := I.symm (algebraMap L _ x)
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) hlt
    have hpn : (0 : ℝ) < ‖(p : ℚ_[p]) ^ n‖ := norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero))
    obtain ⟨q, hq⟩ := Padic.rat_dense p y hpn
    have h1 : ‖(y - q) / (p : ℚ_[p]) ^ n‖ ≤ 1 := by rw [norm_div, div_le_one hpn]; exact hq.le
    have hpv : (0 : ℝ) < ‖(p : s.v.adicCompletion (maximalRealSubfield L))‖ ^ n :=
      pow_pos (norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)) n
    have h2 := emb_le s.v p f hf _ h1
    have h3 := emb_le s.w p I.toRingHom hI _ h1
    have e3 : I.toRingHom ((y - q) / (p : ℚ_[p]) ^ n) = algebraMap L _ ((x - q) / (p : L) ^ n) := by
      simp [y]
    rw [e3, Valued.toNormedField.norm_le_one_iff, ← PI.CompAtExist.stepA s, ← Valued.toNormedField.norm_le_one_iff] at h3
    simp only [map_div₀, map_sub, map_pow, map_natCast, map_ratCast, norm_div, norm_pow, div_le_one hpv] at h2 h3
    calc dist (f y) (s.i x) ≤ dist (f y) q + dist (s.i x) q := dist_triangle_right _ _ _
      _ ≤ ε := by rw [dist_eq_norm, dist_eq_norm]; linarith
  letI := f.toAlgebra
  have : ContinuousSMul ℚ_[p] (s.v.adicCompletion (maximalRealSubfield L)) := continuousSMul_of_algebraMap _ _ hf
  have hcl : IsClosed (Set.range f) :=
    (LinearMap.range (Algebra.linearMap ℚ_[p] (s.v.adicCompletion (maximalRealSubfield L)))).closed_of_finiteDimensional
  have hs : Function.Surjective f := by
    rw [← Set.range_eq_univ, ← hcl.closure_eq]
    refine DenseRange.closure_range ((s.v.denseRange_algebraMap (maximalRealSubfield L)).mono ?_)
    rintro _ ⟨a, rfl⟩
    exact ⟨_, (key (algebraMap _ L a)).trans (s.i.commutes a)⟩
  let e := RingEquiv.ofBijective f ⟨f.injective, hs⟩
  let el : ℚ_[p] ≃ₗ[ℚ_[p]] s.v.adicCompletion (maximalRealSubfield L) :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) ⟨f.injective, hs⟩
  have hc : Continuous e.symm := by
    refine el.toContinuousLinearEquiv.symm.continuous.congr fun y => e.injective ?_
    exact (el.toContinuousLinearEquiv.apply_symm_apply y).trans (e.apply_symm_apply y).symm
  refine ⟨e.symm.trans I, hI.comp hc, fun x => ?_⟩
  rw [← key]
  exact (congrArg I (e.symm_apply_apply _)).trans (I.apply_symm_apply _)

theorem exists_splitPlace (D : D7) (k v) : ∃ s : SplitPlace D.host.E, s.w = D.naut.plGw k v := by
  obtain ⟨s, -, h, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v)
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [GlobalTheory.SplitConjPlace.mem_conj_w]
  refine (h x _ ?_).symm
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

def constTyp (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : NG.FinTyp L n where
  S := Submodule.span ℂ {1}
  stable h f hf := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hf
    exact hf
  smooth f hf := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hf
    exact ⟨1, one_pos, fun _ _ => rfl⟩
  ne := by simp
  irr S' h _ := ((Submodule.isAtom_iff_finrank_eq_one.2 (finrank_span_singleton one_ne_zero)).le_iff).1 h

theorem isComp_const (D : D7) (I : Ident D) : IsComp I (fun _ => constTyp D.host.E D.R.r)
    fun _ k v => pull I k v (GlobalTheory.SmGL.IrrRep.ofChar 1 GlobalTheory.SmGL.isSmoothChar_one) := by
  intro σ k v
  obtain ⟨s, hs⟩ := exists_splitPlace D k v
  refine ⟨s, hs, _, ?_, rfl⟩
  have key : ∀ (w) (hs : s.w = w) (hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal)
      (J : ℚ_[D.host.g k] ≃+* w.adicCompletion D.host.E), Continuous J →
      GlobalTheory.HeightCounting.IsLocS (constTyp D.host.E D.R.r).S s (hs ▸ (GlobalTheory.SmGL.IrrRep.ofChar 1 GlobalTheory.SmGL.isSmoothChar_one :
        GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E)))) := by
    rintro _ rfl hw J hJ
    obtain ⟨i, h1, h2⟩ := exists_iso s _ hw J hJ
    refine ⟨i, LinearMap.toSpanSingleton ℂ _ 1, h1, h2, fun a b h => ?_,
      fun a => Submodule.mem_span_singleton.2 ⟨a, rfl⟩, fun x _ (a : ℂ) => ?_⟩
    · exact smul_left_injective ℂ (one_ne_zero : (1 : GAf D.host.E D.R.r → ℂ) ≠ 0) h
    · funext g
      change ((1 : ℂ) * a) • (1 : ℂ) = a • (1 : ℂ)
      rw [one_mul]
  exact key _ hs (D.naut.plGw_over k v) (I.i k v) (I.cont k v)

theorem not_isComp_zero (D : D7) (I : Ident D) (rep) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (cp)
    (h : IsComp I rep cp) : Nontrivial (cp σ k v) := by
  obtain ⟨_, _, τ, -, h2⟩ := h σ k v
  rw [h2]
  exact (irrSm_pull I k v τ).1.1

theorem exists_pull {D : D7} (I : Ident D) (k v) {n : ℕ} (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (h : GlobalTheory.SerSys.IrrSm π) : ∃ σ, Nonempty (π ≅ pull I k v σ) := by
  letI := (I.i k v).toRingHom.toAlgebra
  have : ContinuousSMul ℚ_[D.host.g k] ((D.naut.plGw k v).adicCompletion D.host.E) :=
    continuousSMul_of_algebraMap _ _ (I.cont k v)
  let el : ℚ_[D.host.g k] ≃ₗ[ℚ_[D.host.g k]] (D.naut.plGw k v).adicCompletion D.host.E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) (I.i k v).bijective
  have hi : Continuous (I.i k v).symm := by
    refine el.toContinuousLinearEquiv.symm.continuous.congr fun y => (I.i k v).injective ?_
    exact (el.toContinuousLinearEquiv.apply_symm_apply y).trans ((I.i k v).apply_symm_apply y).symm
  have hc : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) (I.i k v).symm.toRingHom) :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  have hg : ∀ g : GL (Fin n) ℚ_[D.host.g k], Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun a b => (I.i k v).symm_apply_apply _)
  refine ⟨⟨π, π.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom), fun x => (h.2 x).preimage hc,
    GlobalTheory.CuspRep.ParLaws.isIrreducible_comp ((GlobalTheory.GLp.Model.isIrrRep_iff _).1 h.1) _ fun g => ⟨_, hg g⟩⟩,
    ⟨Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ π) fun g => LinearMap.ext fun x => ?_)⟩⟩
  change π.ρ g x = π.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g)) x
  rw [hg]

theorem isRc_unique {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} {I : Ident D} {rc rc'}
    (h : IsRc hL T I rc) (h' : IsRc hL T I rc') (k v n π) (hπ : GlobalTheory.SerSys.IrrSm π) : rc k v n π = rc' k v n π := by
  obtain ⟨σ, e⟩ := exists_pull I k v π hπ
  exact (T.e _).injective ((h k v n σ π e).trans (h' k v n σ π e).symm)

end GlobalTheory.TypeRec.Model

end
