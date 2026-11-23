import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.ConeLaw
import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sfin_of {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (s : Set α) : SFinite μ ∧ SFinite (μ.restrict s) :=
  ⟨inferInstance, inferInstance⟩

theorem sfin_haar {G : Type} [Group G] [TopologicalSpace G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (s : Set G) : SFinite μ ∧ SFinite (μ.restrict s) := ⟨inferInstance, inferInstance⟩

theorem cone_core (hUn : Unfold) (hU : UnipEx) (hD : StabDec) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hA : EvAdm)
    {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
    {M₀ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {j₀ j₁ i₀ i₁ r s r' s' r₀ s₀ r₀' s₀' : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) {I e} (he : IsEv B M M₀ H.ι H'.ι I e)
    {K : Subgroup (UA σ X.J)} {μK : Measure K} {μ : Measure (AE F E)ˣ} (hI : Iwa H K) (hμK : μK.IsHaarMeasure) (hμ : μ.IsHaarMeasure)
    (u : (AE F E)ˣ → Ten F E n d) (z : ℕ) (ι : (AE F E)ˣ → (AE F E)ˣ) (hι : ι = id ∨ ι = fun l => l⁻¹) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om r s r' s' → IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀' →
      ∀ (ν χ : Chr F E) (S : Submodule ℂ (Fn F n d)), Continuous ν → Laws B M om om₀ H H' e u ν χ z ι →
      (∀ Ψ ∈ S, Ψ ∈ schA F (Fin n × Fin d)) → (∀ x, ∀ Ψ ∈ S, om x Ψ ∈ S) →
      (∀ Ψ ∈ S, ∀ h₁, ∫⁻ l, (∫⁻ g in M₀.dom, ‖theta om₀ (e (M.co.rho B.ψ (u l) Ψ)) g h₁‖ₑ ∂M₀.μ) *
        ENNReal.ofReal ((absE F E l : ℝ) ^ z) ∂μ < ⊤) →
      (∀ Ψ ∈ schA F (Fin n × Fin d), ∃ Ψ₁ ∈ schA F (Fin n₁ × Fin d₁), ∀ l₁ ∈ (adeleClass F).adm (Fin n₁ × Fin d₁),
        Integrable (fun l : (AE F E)ˣ => l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) μ ∧
        l₁ Ψ₁ = ∫ l, l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ) →
      ∀ Φ ∈ S, KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (u 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (u 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (u 1) Φ h (γ x * g) ∂M.μ = κ * coneI B M om M₀ om₀ e K μK μ u ν z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ u ν z (om (1, p * h) Φ) 1 =
        (χ t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) * coneI B M om M₀ om₀ e K μK μ u ν z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ u ν z (om (1, h) Φ) h₁ = M₀.I om₀ (cone B M om e K μK μ u ν z (om (1, h) Φ)) h₁ := by
  by_cases hex : ∃ χX χW om om₀, IsPair B M χX χW om r s r' s' ∧ IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀'
  swap
  · exact ⟨1, one_ne_zero, fun χX χW om om₀ hp hp₀ => absurd ⟨χX, χW, om, om₀, hp, hp₀⟩ hex⟩
  obtain ⟨χ0, χ0', o, o₀, hq, hq₀⟩ := hex
  obtain ⟨-, -, -, -, ⟨lev, hlc, hlev, -⟩, -⟩ := hU F E σ B n n₁ X X₁ H j₀ j₁ r s hq.base (Or.inl hq.herm) hH
  obtain ⟨-, -, -, -, ⟨lev', -, hlev', -⟩, -⟩ := hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hq.base (Or.inr hq.skew) hH'
  obtain ⟨κ, hκ, hUnf⟩ := hUn F E σ B n n₁ X X₁ H j₀ j₁ r s hq.base hq.herm hH K μK μ M.μ M.dom M₀.μ M₀.dom lev hI hμK hμ
    hq.good.haar hq.good.dom hq₀.good.haar hq₀.good.dom hlev
  refine ⟨κ, by exact_mod_cast hκ.ne', fun χX χW om om₀ hp hp₀ ν χ S hν hL hle hst hfin hlam Φ hΦ hK => ?_⟩
  obtain ⟨-, -, i1, -, i2, i3, i4⟩ := ideleTop F E
  obtain ⟨j1, j2, j3, -⟩ := i4 μ hμ
  obtain ⟨k1, k2, -⟩ := hG F E σ hp.base.cm n₁ X₁.J (hE F E σ B hp.base n₁ X₁ r₀ s₀ (Or.inl hp₀.herm)).1
  obtain ⟨-, k3, -⟩ := hG F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1
  have k4 : BorelSpace (UA σ X₁.J) := ⟨rfl⟩
  have k5 : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have k6 := hp₀.good.haar
  obtain ⟨k10, k11⟩ := sfin_haar M₀.μ M₀.dom
  have k12 : SFinite μ := (sfin_of μ ∅).1
  have k7 : CompactSpace K := isCompact_iff_compactSpace.1 hI.1
  obtain ⟨⟨l₀, hl₀, hl₀'⟩, hrho, hev⟩ := hA F E σ B n d n₁ d₁ X W X₁ W₁ M M₀ hp.base hp.good hp₀.good
  obtain ⟨l₁, hl₁, hl₁'⟩ := hev _ _ _ e he (u 1) l₀ hl₀
  have hsch : ∀ v, ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ v Ψ) ∈ schA F (Fin n₁ × Fin d₁) :=
    fun v Ψ h => he.maps _ (hrho v Ψ h)
  have hcv : ∀ Ψ ∈ schA F (Fin n × Fin d), Continuous fun x => thetaSum F (e (M.co.rho B.ψ (u 1) (om x Ψ))) := fun Ψ h =>
    (pair_cont hp hl₁ h).congr fun x => by rw [hl₁' _ (pair_pres hp x h), hl₀' _ (hsch _ _ (pair_pres hp x h))]
  have hιc : Continuous ι := by rcases hι with rfl | rfl; exacts [continuous_id, continuous_inv]
  have habs : Continuous fun l : (AE F E)ˣ => (absE F E l : ℝ) := NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE
  have hw : Continuous fun l : (AE F E)ˣ => (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z :=
    (continuous_subtype_val.comp hν).mul ((Complex.continuous_ofReal.comp habs).pow z)
  have hw0 : ∀ l : (AE F E)ˣ, (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ≠ 0 := fun l =>
    mul_ne_zero (Circle.coe_ne_zero _) (pow_ne_zero _ (by exact_mod_cast absE_ne l))
  have hOK : LineOK B M om M₀ om₀ e μ u ν z S := by
    refine ⟨hle, hst, fun l => hsch _, fun g h => ⟨_, pair_adm hp₀ (g, h) hl₀, fun Φ hΦ => hl₀' _ (pair_pres hp₀ _ hΦ)⟩,
      fun Ψ hΨ h₁ => ?_, hlam⟩
    refine int_prod μ _ (θ := fun x => theta om₀ (e (M.co.rho B.ψ (u x.1) Ψ)) x.2 h₁) ?_ hw (fun l => ?_) (hfin Ψ hΨ h₁)
    · have c1 : Continuous fun x : (AE F E)ˣ × UA σ X₁.J =>
          thetaSum F (e (M.co.rho B.ψ (u 1) (om (lev (ι x.1, x.2), lev' (1, h₁)) Ψ))) *
            (((absE F E (ι x.1) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) / ((ν x.1 : ℂ) * ((absE F E x.1 : ℝ) : ℂ) ^ z) :=
        (((hcv Ψ (hle Ψ hΨ)).comp ((hlc.comp ((hιc.comp continuous_fst).prodMk continuous_snd)).prodMk continuous_const)).mul
          (Complex.continuous_ofReal.comp ((habs.comp (hιc.comp continuous_fst)).rpow_const fun x => Or.inl (absE_ne _)))).div
          (hw.comp continuous_fst) fun x => hw0 _
      exact c1.congr fun x => by rw [hL.toLawsT.theta (hlev _ _) (hlev' _ _) (hle Ψ hΨ), mul_div_cancel_right₀ _ (hw0 _)]
    · rw [norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  obtain ⟨m, Ψ, c, hΨ, hc, hd⟩ := kfin_dec hp (hle Φ hΦ) hK S fun k => hst _ _ hΦ
  have hci : ∀ i, Integrable (c i) μK := fun i => (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd' : ∀ h (k : K), om (k.1, 1) (om (1, h) Φ) = ∑ i, c i k • om (1, h) (Ψ i) := fun h k => by
    rw [show om (k.1, 1) (om (1, h) Φ) = om (1, h) (om (k.1, 1) Φ) by simp [om_mul], hd, map_sum]
    simp only [map_smul]
  refine ⟨fun γ hγ h => ?_, fun t h₁ p hl h => hL.coneI_law hp μK (hle Φ hΦ) hl h,
    fun h h₁ => hOK.coneI_eq μK (fun i => hst _ _ (hΨ i)) hci (hd' h) h₁⟩
  obtain ⟨f1, f2⟩ := hOK.unf μK (fun i => hst _ _ (hΨ i)) hci (hd' h) ι
    (fun G => by rcases hι with rfl | rfl; exacts [rfl, lintegral_inv_eq_self G])
    (fun G => by rcases hι with rfl | rfl; exacts [rfl, integral_inv_eq_self G μ]) lev (thv B M om e (u 1) Φ h) (fun l g k => by
      rw [← hL.toLawsT.theta (hlev _ _) (levi_one (W₁ := W₁) H') (pair_pres hp _ (pair_pres hp _ (hle Φ hΦ)))]
      simp [thv, om_mul])
  rw [← f2]
  refine hUnf γ hγ _ ((hcv Φ (hle Φ hΦ)).comp (continuous_id.prodMk continuous_const)) (fun v hv g => ?_)
    (fun δ hδ hx g => hL.toLawsT.rat hD hTB hp hp₀ hH (hsch _) (hle Φ hΦ) h hδ hx g) f1
  unfold thv
  rw [show om (v * g, h) Φ = om (v, 1) (om (g, h) Φ) by simp [om_mul], hL.uni v hv _ (pair_pres hp _ (hle Φ hΦ))]

end PositivityTheory.ThKCT

end
