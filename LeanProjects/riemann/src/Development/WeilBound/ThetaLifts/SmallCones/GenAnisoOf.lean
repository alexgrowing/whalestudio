import Development.WeilBound.ThetaLifts.SmallCones.HodgeTateFromSandwich
import Development.WeilBound.ThetaLifts.SmallCones.ConeBasic
import Development.WeilBound.ThetaLifts.SmallCones.ThetaKernelGeneralIdentity

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}

theorem dom_change (hG : GrpTop) (hE : EpsOf) (hB : B.IsGood σ) {r s : ℕ} (hX : X.IsHerm σ B r s)
    {m m' : Measure (UA σ X.J)} {D D' : Set (UA σ X.J)} (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure)
    (hd : IsFundamentalDomain (ratU σ X.J) D m) (hd' : IsFundamentalDomain (ratU σ X.J) D' m') :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : UA σ X.J → ℂ, (∀ γ ∈ ratU σ X.J, ∀ g, φ (γ * g) = φ g) →
      ∫ g in D, φ g ∂m = c * ∫ g in D', φ g ∂m' := by
  obtain ⟨b1, b2, b3, b4, -⟩ := hG F E σ hB.cm n X.J (hE F E σ B hB n X r s (Or.inl hX)).1
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ X.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have hc : m = Measure.haarScalarFactor m m' • m' := Measure.isMulLeftInvariant_eq_smul m m'
  have hpos : 0 < Measure.haarScalarFactor m m' := Measure.haarScalarFactor_pos_of_isHaarMeasure m m'
  have hac : m ≪ m' := by
    rw [hc]; exact Measure.smul_absolutelyContinuous
  have hd'' : IsFundamentalDomain (ratU σ X.J) D' m := hd'.mono hac
  refine ⟨((Measure.haarScalarFactor m m' : NNReal) : ℂ), ?_, fun φ hφ => ?_⟩
  · exact_mod_cast hpos.ne'
  · have h1 : ∫ g in D, φ g ∂m = ∫ g in D', φ g ∂m := hd.setIntegral_eq hd'' fun γ g => hφ γ γ.2 g
    rw [h1]
    conv_lhs => rw [hc]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure]
    simp [NNReal.smul_def]

theorem isLevi_one : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' 1 1 1 :=
  ⟨by rw [mat_one', Matrix.one_mulVec, Units.val_one, one_smul],
    by rw [mat_one', Matrix.one_mulVec, inv_one, Units.val_one, map_one, one_smul],
    by rw [mat_one', mat_one', Matrix.one_mul, Matrix.mul_one]⟩

theorem weil_bound (hW : WeilConv) {M : Model σ X W} {χX χW om r s r' s'} (hp : IsPair B M χX χW om r s r' s')
    (hr : d + 2 * min r s < 2 * n ∨ min r s = 0) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ (C : ℝ) (k : ℕ), ∀ h, ∫⁻ g in M.dom, ‖theta om Φ g h‖ₑ ∂M.μ ≤ ENNReal.ofReal (C * (ht h : ℝ) ^ k) := by
  obtain ⟨h1, C, k, h2⟩ := (hW F E σ B n d X W M χX χW om r s r' s' hp hr).1 Φ hΦ
  refine ⟨C, k, fun h => ?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm (h1 h)]
  exact ENNReal.ofReal_le_ofReal (h2 h)

theorem zero_term (hM : MixW) (hT : ThetaBasic) {M : Model σ X W} {M₁ : Model σ X W₁} {χX χW om om₁ r s r' s' r₁ s₁ i₀ i₁}
    (hp : IsPair B M χX χW om r s r' s') (hp₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    {e} (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) {c : ℂ} (hc : ∀ φ : UA σ X.J → ℂ, (∀ γ ∈ ratU σ X.J, ∀ g, φ (γ * g) = φ g) →
      ∫ g in M.dom, φ g ∂M.μ = c * ∫ g in M₁.dom, φ g ∂M₁.μ) (C₀ : ℂ) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    HasLaw W₁ H' χX ((n : ℝ) / 2) (fun h => ∫ g in M.dom, C₀ * thetaSum F (e (om (g, h) Φ)) ∂M.μ) ∧
      ∀ h₁ p, IsLevi H' 1 h₁ p → ∀ h, ∫ g in M.dom, C₀ * thetaSum F (e (om (g, p * h) Φ)) ∂M.μ =
        C₀ * c * M₁.I om₁ (e (om (1, h) Φ)) h₁ := by
  have key : ∀ g t h₁ p, IsLevi H' t h₁ p → ∀ h, thetaSum F (e (om (g, p * h) Φ)) =
      (χX t : ℂ) * (((absE F E t : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * theta om₁ (e (om (1, h) Φ)) g h₁ := fun g t h₁ p hl h => by
    have := hM F E σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hp₁ e he g t h₁ p hl 1 (one_mem _) _
      (pair_pres hp (1, h) hΦ)
    rw [om_mul, Prod.mk_mul_mk, mul_one, one_mul] at this
    rw [this, thetaSum_smul', theta]
  have key1 : ∀ g h₁ p, IsLevi H' 1 h₁ p → ∀ h, thetaSum F (e (om (g, p * h) Φ)) = theta om₁ (e (om (1, h) Φ)) g h₁ :=
    fun g h₁ p hl h => by rw [key g 1 h₁ p hl h]; simp
  refine ⟨fun t m hl h => ?_, fun h₁ p hl h => ?_⟩
  · simp only [key _ t 1 m hl h, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have := key1 g 1 1 isLevi_one h
    rw [one_mul] at this
    simp only [this]
    ring
  · obtain ⟨-, t2, -⟩ := (hT F E σ B n d₁ X W₁ M₁ χX χW om₁ r s r₁ s₁ hp₁).1 _ (he.maps _ (pair_pres hp (1, h) hΦ))
    simp only [key1 _ h₁ p hl h]
    rw [integral_const_mul, hc _ fun γ hγ g => by simpa using t2 γ hγ 1 (one_mem _) g h₁, mul_assoc, Model.I]

theorem genAniso_of (hK : CTKernel) (hF : CTFub) (hM : MixW) (hW : WeilConv) (hT : ThetaBasic) (hWi : Witt) (hG : GrpTop)
    (hE : EpsOf) : GenAniso := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ H' i₀ i₁ r s r' s' r₁ s₁ X' M M₁ hX hrs hH e he
  subst hX
  by_cases h0 : ∃ χX χW om om₁, IsPair B M χX χW om r s r' s' ∧ IsPair B M₁ χX χW om₁ r s r₁ s₁
  swap
  · exact ⟨1, one_ne_zero, fun χX χW om om₁ h1 h2 => absurd ⟨χX, χW, om, om₁, h1, h2⟩ h0⟩
  obtain ⟨_, _, _, _, q, q₁⟩ := h0
  obtain ⟨C₀, hC₀, h1, -⟩ := hK F E σ B n d d₁ X' W W₁ M M₁ H' i₀ i₁ hH q₁.good e he
  obtain ⟨c, hc0, hc⟩ := dom_change hG hE q.base q.herm q.good.haar q₁.good.haar q.good.dom q₁.good.dom
  refine ⟨C₀ * c, mul_ne_zero hC₀ hc0, fun χX χW om om₁ hp hp₁ Φ hΦ => ?_⟩
  obtain ⟨z1, z2⟩ := zero_term hM hT hp hp₁ hH he hc C₀ hΦ
  exact ⟨_, (hF F E σ B n d X' W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ hH Φ hΦ (weil_bound hW hp (Or.inr hrs) hΦ) _
    (h1 ((hWi F E σ B n X' r s hp.base hp.herm).1 hrs) χX χW om r s r' s' hp Φ hΦ)).2, z1, z2⟩

theorem genBig_of (hK : CTKernel) (hF : CTFub) (hA : ConeA) (hM : MixW) (hW : WeilConv) (hT : ThetaBasic) (hWi : Witt)
    (hG : GrpTop) (hE : EpsOf) : GenBig := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ e g₁ g₀ he₀ he z hz K μK μ hI hμK hμ
  by_cases h0 : ∃ χX χW om, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1)
  swap
  · exact ⟨1, 1, one_ne_zero, one_ne_zero, fun χX χW om _ _ h1 => absurd ⟨χX, χW, om, h1⟩ h0⟩
  obtain ⟨_, _, _, q⟩ := h0
  obtain ⟨C₀, hC₀, -, h1⟩ := hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' g₁ e₀ he₀
  obtain ⟨C₁, hC₁, h2⟩ := h1 n₁ X₁ H j₀ j₁ M₀ hH g₀ e he
  obtain ⟨κ, hκ, h3⟩ := hA F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' e he z hz K μK μ hI hμK hμ
  obtain ⟨c, hc0, hc⟩ := dom_change hG hE q.base q.herm q.good.haar g₁.haar q.good.dom g₁.dom
  obtain ⟨γ, hγ⟩ := (hWi F E σ B n X _ _ q.base q.herm).2 n₁ H (adapted_x_ne hH) hH.xx
  refine ⟨C₀ * c, C₁ * κ, mul_ne_zero hC₀ hc0, mul_ne_zero hC₁ hκ, fun χX χW om om₁ om₀ hp hp₁ hp₀ Φ hΦ hfin => ?_⟩
  obtain ⟨z1, z2⟩ := zero_term hM hT hp hp₁ hH' he₀ hc C₀ hΦ
  obtain ⟨a1, a2, a3⟩ := h3 χX χW om om₀ hp hp₀ Φ hΦ hfin
  obtain ⟨f1, f2⟩ := hF F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ hH' Φ hΦ
    (weil_bound hW hp (Or.inl (by omega)) hΦ) _ fun g => (h2 γ hγ χX χW om _ _ _ _ hp Φ hΦ g).2
  refine ⟨_, fun h => C₁ * κ * coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) 1, ?_, z1,
    fun t m hl h => ?_, fun h₁ p hl h => ⟨?_, z2 h₁ p hl h⟩⟩
  · convert f2 using 1
    funext h
    obtain ⟨-, b2, b3⟩ := a1 γ hγ h
    have b4 := b2.const_mul C₁
    have b5 := (f1 h).sub b4
    rw [Pi.add_apply, mul_assoc, ← b3, ← integral_const_mul, ← integral_add _ b4]
    · rfl
    · refine b5.congr (Eventually.of_forall fun g => ?_)
      exact add_sub_cancel_right _ _
  · simp only [a2 t 1 m hl h]
    ring
  · simp only [a2 1 h₁ p hl h, a3]
    simp

end PositivityTheory.ThKCT
