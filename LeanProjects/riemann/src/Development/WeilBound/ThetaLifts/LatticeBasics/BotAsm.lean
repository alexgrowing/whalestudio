import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HodgeTateFromSandwich
import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsHeckeLOfCompleted

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

theorem eq_zero_of_right {U : Set ℂ} (hU : IsOpen U) (hd : ∀ z : ℂ, ∀ᶠ z' in 𝓝[≠] z, z' ∈ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U ∩ {z | 0 < z.re})) {t : ℝ} (ht : ∀ z : ℂ, t < z.re → z ∈ U ∧ f z = 0) {s : ℂ} (hs : s ∈ U)
    (hs' : 0 < s.re) : f s = 0 := by
  have hc : (Uᶜ).Countable := by
    haveI : DiscreteTopology (Uᶜ : Set ℂ) := discreteTopology_subtype_iff.2 fun x _ => by
      rw [Filter.inf_principal_eq_bot, compl_compl]; exact hd x
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let ψ : ℂ → ℂ := fun w => (Real.exp w.re : ℂ) + w.im * Complex.I
  have re : ∀ w, (ψ w).re = Real.exp w.re := fun w => by simp [ψ, Complex.exp_ofReal_re]
  have im : ∀ w, (ψ w).im = w.im := fun w => by simp [ψ, Complex.exp_ofReal_im]
  have inj : Function.Injective ψ := fun w w' e =>
    Complex.ext (Real.exp_injective (by rw [← re, ← re, e])) (by rw [← im, ← im w', e])
  have e : U ∩ {z | 0 < z.re} = ψ '' (ψ ⁻¹' Uᶜ)ᶜ := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      have : ψ ⟨Real.log z.re, z.im⟩ = z := Complex.ext (by rw [re]; exact Real.exp_log h2) (by rw [im])
      exact ⟨_, fun h => h (this.symm ▸ h1), this⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨not_not.1 hw, by show 0 < (ψ w).re; rw [re]; exact Real.exp_pos _⟩
  have hcon : IsPreconnected (U ∩ {z | 0 < z.re}) := by
    rw [e]
    exact ((hc.preimage_of_injOn inj.injOn).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected.image _
      (Continuous.continuousOn (by fun_prop))
  have ho : IsOpen (U ∩ {z : ℂ | 0 < z.re}) := hU.inter (isOpen_lt continuous_const Complex.continuous_re)
  have h1 : t < ((max t 0 + 1 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith [le_max_left t 0]
  refine (hf.analyticOnNhd ho).eqOn_zero_of_preconnected_of_eventuallyEq_zero hcon (z₀ := ((max t 0 + 1 : ℝ) : ℂ))
    ⟨(ht _ h1).1, by show 0 < Complex.re _; rw [Complex.ofReal_re]; linarith [le_max_right t 0]⟩ ?_ ⟨hs, hs'⟩
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1] with z hz using (ht z hz).2

theorem hasProd_off {χ : Chr F E} {T : Finset (Pl F)} (h : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → ¬ UnrAt χ w)
    {z : ℂ} (hz : 1 < z.re) : HasProd (fun v : {v : Pl F // v ∉ T} => Lv (charFam χ) v.1 z) (charL χ (∅ : Set (Pl F)) z) := by
  have h1 := hasProd_Lv (S := (∅ : Set (Pl F))) (converges_charFam _ χ hz)
  have h2 : HasProd (fun v : Pl F => Lv (charFam χ) v z) (charL χ (∅ : Set (Pl F)) z) :=
    (Equiv.subtypeUnivEquiv (p := fun v => v ∉ (∅ : Set (Pl F))) (fun _ => Set.notMem_empty _)).hasProd_iff.1 h1
  refine (hasProd_subtype_iff_of_mulSupport_subset (s := {v | v ∉ T}) fun v hv hT => hv ?_).2 h2
  refine Finset.prod_eq_one fun w hw => ?_
  have : ¬ UnrAt χ w := h w (by rwa [mem_aboveF.1 hw])
  simp [locL, charFam, this]

theorem pair_ne_zero (hH : HgtEx) (hN : NormZeta) (hE : EulerProd) (hM : LocMeas) (hU : LocUnr) (hB : BadFactor) (hI : RealInv)
    (hD : DProd) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (h : IsPair B M χX χW om r s r' s') (h0 : min r s = 0) (h0' : min r' s' = 0) (hn : 1 ≤ n) (hd : n < d)
    (he : Even d) {T : Finset (Pl F)} (hT : T ⊆ B.P) (uX : UnrOff χX (T : Set (Pl F))) (uW : UnrOff χW (T : Set (Pl F)))
    (ram : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → ¬ UnrAt χW w)
    {P : Type} [AddCommGroup P] [Module ℂ P] [Nontrivial P] {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (hp : RealQuot B M om p)
    {Λ : ℂ → ℂ} (l1 : Differentiable ℂ Λ) (l2 : ∀ z : ℂ, 1 < z.re → Λ z = charL χW (∅ : Set (Pl F)) z)
    (l3 : ∀ z : ℤ, -(d : ℤ) ≤ 2 * z → Λ z ≠ 0) : ∃ Φ ∈ PolData B M, M.I om Φ ≠ 0 := by
  obtain ⟨⟨K, a, hK, ha, -⟩, e, -, he'⟩ := hH F E σ B n X r s h.base (Or.inl h.herm)
  obtain ⟨f₀, p0, n0, i0⟩ := hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ h h0 P p hp
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let ν : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  obtain ⟨Φ, pΦ, b1, b2, b3⟩ := hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ h h0 h0' hd.le he T hT uX uW f₀ p0 n0 i0 K a e hK ha he' ν hν
  obtain ⟨U, Z, t₀, u1, u2, u3, u4, u5, u6⟩ := hN F E σ B _ _ _ _ _ _ _ _ _ _ _ _ h h0 h0' hn (by omega) K a e hK ha he' ν hν Φ pΦ
  obtain ⟨dT, d1, d2⟩ := hD F E n T
  choose μl hμl using hM F E σ B n X r s h.base h.herm
  refine ⟨Φ, pΦ, fun hz => ?_⟩
  set H : ℂ → ℂ := fun z => ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ z g ∂M.μ with hHdef
  have res0 : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW 0 := fun x => by
    rw [h.resW x, he.neg_one_pow, pow_zero]
  have key : ∀ z : ℂ, max t₀ (n / 2) < z.re →
      z ∈ U ∧ Z z * dT z - (∏ i ∈ Finset.range n, Λ (z + n / 2 - i)) * H z = 0 := fun z hz => by
    have z1 := (le_max_left _ _).trans_lt hz
    have z2 := (le_max_right _ _).trans_lt hz
    have n1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨m1, m2, m3⟩ := u5 z z1
    refine ⟨m1, sub_eq_zero.2 ?_⟩
    choose! f f1 f2 using b1 z
    have lu := fun v (hv : v ∉ T) => hU F E σ B n X r s h.base h.herm χW h.hW res0 K e hK he' v
      (fun w hw => uW w (by show ¬ w.under (𝓞 F) ∈ (T : Set (Pl F)); rw [hw]; exact hv)) (μl v) (hμl v).1 (hμl v).2 z (f v) z2
      (f1 v hv)
    have t1 := hE F E σ B n X r s h.base h.herm T M.μ h.good.haar μl hμl _ (fun v u => f v (e (u, 1))) m2 fun v hv =>
      ⟨fun u hu => (f2 v hv u hu).2, fun u hu => (f2 v hv u hu).1, (lu v hv).1⟩
    have t2 := t1.mul (d2 z (by linarith)).2
    have t3 : HasProd (fun v : {v : Pl F // v ∉ T} => ∏ i ∈ Finset.range n, Lv (charFam χW) v.1 (z + n / 2 - i))
        (∏ i ∈ Finset.range n, Λ (z + n / 2 - i)) := hasProd_prod fun i hi => by
      have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hi
      have : 1 < (z + n / 2 - i).re := by
        simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.div_ofNat_re]; linarith
      rw [l2 _ this]; exact hasProd_off ram this
    rw [m3]
    refine tendsto_nhds_unique t2 ((Filter.Tendsto.mul_const (H z) t3).congr fun S => ?_)
    rw [mul_right_comm, ← Finset.prod_mul_distrib]
    exact congrArg (· * H z) (Finset.prod_congr rfl fun v _ => (lu v.1 v.2).2.symm)
  have s0 : 0 < (((d : ℂ) - n) / 2).re := by
    have : (n : ℝ) < d := by exact_mod_cast hd
    simp only [Complex.sub_re, Complex.natCast_re, Complex.div_ofNat_re]; linarith
  have fin := eq_zero_of_right u1 u2 (f := fun z => Z z * dT z - (∏ i ∈ Finset.range n, Λ (z + n / 2 - i)) * H z)
    (((u4.mono Set.inter_subset_left).mul (d1.mono Set.inter_subset_right)).sub
      ((Differentiable.fun_finsetProd fun i _ => l1.comp ((differentiable_id.add_const _).sub_const _)).mul b2).differentiableOn)
    key u3 s0
  simp only [u6 hz, zero_mul, zero_sub, neg_eq_zero] at fin
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i hi => ?_) b3 fin
  obtain ⟨k, hk⟩ := he
  have := l3 ((k : ℤ) - i) (by have := Finset.mem_range.1 hi; omega)
  rwa [show (((k : ℤ) - i : ℤ) : ℂ) = ((d : ℂ) - n) / 2 + n / 2 - i by rw [hk]; push_cast; ring] at this

theorem nonZeroBottom_of_doubling_integral (hR : KReal) (hL : LInt2) (hH : HgtEx) (hN : NormZeta) (hE : EulerProd) (hM : LocMeas) (hU : LocUnr)
    (hB : BadFactor) (hI : RealInv) (hD : DProd) : NonZeroBot := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h hp hq
  obtain ⟨R, hr⟩ := hR F E σ B a a' G X om om' h
  obtain ⟨Λ, l1, l2, l3⟩ := hL F E σ B a a' G X om om' h X.ν (Or.inl rfl)
  obtain ⟨Λ', l1', l2', l3'⟩ := hL F E σ B a a' G X om om' h X.ν⁻¹ (Or.inr rfl)
  have g1 := h.geo.lt
  have g2 := h.geo.aBig
  have c := h.chars
  have hν := isHecke_nu h
  have e : X.β / X.α = X.ν⁻¹ := by rw [Chars.ν, inv_div]
  have uν : UnrOff X.ν (X.T : Set (Pl F)) := fun w hw => by
    rw [Chars.ν, div_eq_mul_inv]; exact (c.unrα w hw).mul (c.unrβ w hw).inv
  have rν : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.ν (a + a') := fun x => by
    show ((X.α _ / X.β _ : Circle) : ℂ) = _
    rw [Circle.coe_div, c.resα x, c.resβ x, h.geo.even.neg_one_pow]
    split_ifs
    · exact div_one _
    · rw [div_eq_one_iff_eq (pow_ne_zero _ (by norm_num)), neg_one_pow_congr (Nat.even_add.1 h.geo.even).symm]
  have rν' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.ν⁻¹ (a + a') := fun x => by
    show (((X.ν _)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv, rν x, h.geo.even.neg_one_pow, ite_self, inv_one]
  have hν' : IsHecke F E X.ν⁻¹ := ⟨hν.1.inv, fun x => by rw [MonoidHom.inv_apply, hν.2 x, inv_one]⟩
  haveI := hr.nontriv
  exact ⟨pair_ne_zero hH hN hE hM hU hB hI hD (χW := X.ν⁻¹)
      ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, c.heckeβ, hν', c.resβ, rν', e ▸ h.weil⟩ (by omega) (by omega) (by omega) (by omega)
      h.geo.even c.sub c.unrβ (fun w hw => (uν w hw).inv) (fun w hw hu => c.ram w hw (by simpa using hu.inv)) hr.quot l1' l2' l3',
    pair_ne_zero hH hN hE hM hU hB hI hD (χW := X.ν)
      ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', c.heckeα, hν, c.resα, rν, h.weil'⟩ (by omega) (by omega) (by omega) (by omega)
      h.geo.even c.sub c.unrα uν c.ram hr.quot' l1 l2 l3⟩

end GlobalTheory.ThK.Dbl

end
