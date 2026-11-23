import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
import Development.WeilBound.ThetaLifts.LatticeBasics.SWFull
import Development.WeilBound.ThetaLifts.LatticeBasics.HodgeTateFromSandwich
import Development.WeilBound.ThetaLifts.LatticeBasics.BoxSecX
import Development.WeilBound.ThetaLifts.LatticeBasics.SchToPol

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

theorem swFullX_of (h1 : SWAnisoX) (h2 : EisContinues) (h3 : BoxSecX) : SWFullX := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2
  obtain ⟨U, Ê, hE, hR⟩ := h2 F E σ B n X r s hB hn (.inl hX) χ hχ d hr K a hK ha _ _
    (h3 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2)
  obtain ⟨k, hk⟩ := hR (((d : ℂ) - n) / 2)
  exact ⟨_, _, hE.update hk (h1 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2),
    Set.mem_insert _ _, fun x => by rw [Function.update_self]⟩

theorem inv_scale {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : G → ℂ, (Integrable (fun g => f g⁻¹) μ → Integrable f μ) ∧ ∫ g, f g⁻¹ ∂μ = c * ∫ g, f g ∂μ := by
  have e := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have c0 : μ.inv.haarScalarFactor μ ≠ 0 := fun h => NeZero.ne μ (by rw [← μ.inv_inv, e, h, zero_smul]; exact Measure.map_zero _)
  refine ⟨((μ.inv.haarScalarFactor μ : ℝ) : ℂ), by simpa using c0, fun f => ⟨fun h => ?_, ?_⟩⟩
  · have : Integrable f μ.inv := (integrable_map_equiv (MeasurableEquiv.inv G) f).2 h
    rw [e] at this
    exact (integrable_smul_measure (ENNReal.coe_ne_zero.2 c0) ENNReal.coe_ne_top).1 this
  · have : ∫ g, f g ∂μ.inv = ∫ g, f g⁻¹ ∂μ := integral_map_equiv (MeasurableEquiv.inv G) f
    rw [← this]
    conv_lhs => rw [e]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem normZeta_of (hS : SWFullX) (hX : BoxSecX) (hW : DblX) (hH : HgtEx) (hT : HgtInt) (hK : Stab2Cpt) (hC : CptAll)
    (hB : ThetaBasic) (hP : PolSch) : NormZeta := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' T h0 h0' hn hd K a e k1 k2 he ν hν Φ hΦ
  have cX := hC F E σ B _ X _ _ T.base (.inl T.herm) h0
  have cW := hC F E σ B _ W _ _ T.base (.inr T.skew) h0'
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  obtain ⟨⟨K', a', k1', k2', k3, k4⟩, e', ce, he'⟩ := hH F E σ B _ X _ _ T.base (.inl T.herm)
  obtain rfl : K' = K := Subgroup.ext fun k => (k1' k).trans (k1 k).symm
  obtain rfl : a' = a := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := k2.iwa x
    rw [k2.val p t hp k hk, k2'.val p t hp k hk]
  obtain rfl : e' = e := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he' x.1 x.2).trans (he x.1 x.2).symm))
  have b := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T).1 Φ (hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T Φ hΦ)
  have s1 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T Φ hΦ
  obtain ⟨dd, om₂, S, l, d1, d2, d3, d4⟩ := hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T
  obtain ⟨c', c0, hc⟩ := d4 ν hν
  obtain ⟨t₀, hi⟩ := hT F E σ B _ X _ _ T.base (.inl T.herm) K' a' e' k1 k2 he M.μ T.good.haar
  have sec := hX F E σ B _ _ _ _ M _ _ _ _ T.base hn hd T.herm T.skew h0' T.good χW T.hW T.resW dd om₂ S l d3 d1 K' a' k1 k2 Φ hΦ Φ hΦ
  obtain ⟨U, Ê, hE, u, hv⟩ := hS F E σ B _ _ _ _ M _ _ _ _ T.base hn hd T.herm T.skew h0' T.good χW T.hW T.resW dd om₂ S l d3 d1
    K' a' k1 k2 μ D hμ hD Φ hΦ Φ hΦ
  obtain ⟨hol, t₁, far⟩ := kpair_cont T.base (.inl T.herm) h0 cX T.hW he ce (hK F E σ B _ X _ _ T.base (.inl T.herm) K' k1)
    k2 k3 k4 sec.cont sec.law hE T.good.haar T.good.dom hi
  haveI := cX.sc; haveI := cW.sc; haveI := cX.lc; haveI := cW.lc; haveI := T.good.haar; haveI := cX.right M.μ T.good.haar
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cX.fin _ _ T.good.haar T.good.dom⟩
  obtain ⟨c, c1, hc1⟩ := inv_scale M.μ
  have rp : IsRapid (fun _ : UA σ X.J => (1 : ℂ)) := cX.rapid continuous_const fun _ _ _ => rfl
  have v0 := Complex.ofReal_ne_zero.2 (cX.vol_ne T.good.haar T.good.dom)
  have c2 := Complex.ofReal_ne_zero.2 c0.ne'
  have id : ∀ z g, flat a' (fun x => l (om₂ x (boxFun Φ (star Φ)))) (((d : ℂ) - n) / 2) z (e' (1, g)) * detInv χW g =
      c' * zint om ν a' e' Φ z g⁻¹ := fun z g => by
    have := (Law.flat (s₀ := ((d : ℂ) - n) / 2) (f := fun x => l (om₂ x (boxFun Φ (star Φ)))) sec.law k2 k4 z).diag (aniso_of T.base (.inl T.herm) h0) he g (e' (g⁻¹, 1))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one] at this
    have e2 := ((d2 Φ s1 Φ s1).2 1 g⁻¹ 1 _ (he _ _)).2
    rw [detInv_rat T.hW (one_mem _), one_smul, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one, Module.End.one_apply] at e2
    rw [this, flat, e2, hc _ (T.weil.isUSplitting.pres _ _ s1) _ s1, zint, coef]
    exact mul_left_comm _ _ _
  refine ⟨U, fun z => (c' * c * M.μ.real M.dom : ℂ)⁻¹ * kpair χW e' M.μ M.dom (Ê z) fun _ => 1, t₁, hE.isOpen, hE.disc, u,
    (hol _ rp).const_mul _, fun z hz => ⟨(far z hz).1, (hc1 _).1 ?_, ?_⟩, fun I0 => mul_eq_zero_of_right _ ?_⟩
  · simpa only [id, integrable_const_mul_iff c2.isUnit] using (far z hz).2.1
  · simp only [(far z hz).2.2 _ rp, id, pet, star_one, mul_one, setIntegral_const, integral_mul_const, integral_const_mul,
      (hc1 _).2, Complex.real_smul]
    field_simp
  · have cT : Continuous fun x : UA σ W.J × UA σ X.J => theta om Φ x.2 x.1 := b.1.comp continuous_swap
    have := An.at_value (φ := fun _ => 1) (M.μ.restrict M.dom) (μ.restrict D)
      ⟨cT, cW.bdd₂ cX cT fun γ hγ δ hδ g g' => b.2.1 δ hδ γ hγ _ _⟩ ⟨continuous_const, 1, by simp⟩
    have z : ∀ h, ∫ g in M.dom, 1 * star (theta om Φ g h) ∂M.μ = 0 := fun h => by
      simp only [one_mul, Complex.star_def, integral_conj]
      exact (map_eq_zero _).2 (congrFun I0 h)
    simp only [z, zero_mul, integral_zero] at this
    refine Eq.trans ?_ ((congrArg ((if n < d then 1 else 2) * (((μ.real D)⁻¹ : ℝ) : ℂ) * ·) this).trans (mul_zero _))
    simp only [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, setAverage_eq, Complex.real_smul, ← fun g => (((d2 Φ s1 Φ s1).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring

end GlobalTheory.ThK.Dbl

end
