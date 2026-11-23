import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

section Gen

set_option linter.unusedSectionVars false

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [FirstCountableTopology Γ] [LocallyCompactSpace Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (ν : Measure Γ) [ν.IsHaarMeasure]

theorem cont_of_rinv {f : Γ → ℂ} {U : Subgroup Γ} (hU : IsOpen (U : Set Γ)) (hf : ∀ u ∈ U, ∀ g, f (g * u) = f g) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  refine (continuousAt_const (y := f g)).congr ?_
  have hm : {y : Γ | g⁻¹ * y ∈ U} ∈ 𝓝 g :=
    (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [U.one_mem])
  filter_upwards [hm] with y hy
  have := hf _ hy g
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem cont_convL {φ₁ φ₂ : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂) :
    Continuous fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
  have e : (fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) = fun g => ∫ h in tsupport φ₁, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
    funext g
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hh, zero_mul]
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ s₁.isCompact
  exact (h₁.comp continuous_snd).mul (h₂.comp (continuous_snd.inv.mul continuous_fst))

theorem supp_convL {φ₁ φ₂ : Γ → ℂ} (s₁ : HasCompactSupport φ₁) (s₂ : HasCompactSupport φ₂) :
    HasCompactSupport fun g => ∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν := by
  refine HasCompactSupport.intro (s₁.isCompact.mul s₂.isCompact) fun g hg => ?_
  have : ∀ h, φ₁ h * φ₂ (h⁻¹ * g) = 0 := by
    intro h
    by_cases h1 : h ∈ tsupport φ₁
    · have h2 : h⁻¹ * g ∉ tsupport φ₂ := fun h2 => hg (Set.mem_mul.2 ⟨h, h1, h⁻¹ * g, h2, mul_inv_cancel_left h g⟩)
      rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  simp [this]

theorem cont_convR {φ₂ f : Γ → ℂ} (h₂ : Continuous φ₂) (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Continuous fun h => ∫ k, φ₂ k * f (h * k) ∂ν := by
  have e : (fun h => ∫ k, φ₂ k * f (h * k) ∂ν) = fun h => ∫ k in tsupport φ₂, φ₂ k * f (h * k) ∂ν := by
    funext h
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hk, zero_mul]
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ s₂.isCompact
  exact (h₂.comp continuous_snd).mul (hf.comp (continuous_fst.mul continuous_snd))

theorem int_L {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Integrable (fun g => (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g) ν :=
  ((cont_convL ν h₁ s₁ h₂).mul hf).integrable_of_hasCompactSupport ((supp_convL ν s₁ s₂).mul_right)

theorem int_R {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    Integrable (fun h => φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν) ν :=
  (h₁.mul (cont_convR ν h₂ s₂ hf)).integrable_of_hasCompactSupport s₁.mul_right

theorem swap_key {φ₁ φ₂ f : Γ → ℂ} (h₁ : Continuous φ₁) (s₁ : HasCompactSupport φ₁) (h₂ : Continuous φ₂)
    (s₂ : HasCompactSupport φ₂) (hf : Continuous f) :
    ∫ g, (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g ∂ν = ∫ h, φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν ∂ν := by
  have hc : Continuous (Function.uncurry fun g h : Γ => φ₁ h * φ₂ (h⁻¹ * g) * f g) :=
    ((h₁.comp continuous_snd).mul (h₂.comp (continuous_snd.inv.mul continuous_fst))).mul (hf.comp continuous_fst)
  have hs : HasCompactSupport (Function.uncurry fun g h : Γ => φ₁ h * φ₂ (h⁻¹ * g) * f g) := by
    refine HasCompactSupport.intro ((s₁.isCompact.mul s₂.isCompact).prod s₁.isCompact) fun p hp => ?_
    show φ₁ p.2 * φ₂ (p.2⁻¹ * p.1) * f p.1 = 0
    by_cases h1 : p.2 ∈ tsupport φ₁
    · have h2 : p.2⁻¹ * p.1 ∉ tsupport φ₂ := fun h2 =>
        hp ⟨Set.mem_mul.2 ⟨p.2, h1, p.2⁻¹ * p.1, h2, mul_inv_cancel_left p.2 p.1⟩, h1⟩
      rw [image_eq_zero_of_notMem_tsupport h2, mul_zero, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul, zero_mul]
  calc ∫ g, (∫ h, φ₁ h * φ₂ (h⁻¹ * g) ∂ν) * f g ∂ν
      = ∫ g, ∫ h, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ h, ∫ g, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν ∂ν := integral_integral_swap_of_hasCompactSupport hc hs
    _ = ∫ h, φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        have e1 := integral_mul_left_eq_self (μ := ν) (fun g => φ₂ (h⁻¹ * g) * f g) h
        simp only [inv_mul_cancel_left] at e1
        show ∫ g, φ₁ h * φ₂ (h⁻¹ * g) * f g ∂ν = φ₁ h * ∫ k, φ₂ k * f (h * k) ∂ν
        rw [e1, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        show φ₁ h * φ₂ (h⁻¹ * g) * f g = φ₁ h * (φ₂ (h⁻¹ * g) * f g)
        ring

end Gen

theorem finH_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (g h : Hf E a b) :
    finH (g * h) = finH g * finH h := by
  simp [finH, map_mul]

attribute [local instance] borelG borelF borelH

theorem convMul_holds : Tail.ConvMul := by
  intro E _ _ _ B A ψ ψ' U F hψ hψ' hU hF
  have := B.hν
  have : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  refine ⟨?_, ?_⟩
  · funext i X
    obtain ⟨p, x₀⟩ := i
    have hfc : ∀ z, Continuous fun g => F (p, z) (X * finH g) := by
      intro z
      refine cont_of_rinv hU fun u hu g => ?_
      rw [finH_mul', ← mul_assoc, hF _ u hu]
    simp only [convF, mulF]
    calc ∑ z, ∫ g, (∑ w, ∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν
        = ∑ z, ∑ w, ∫ g, (∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν := by
          refine Finset.sum_congr rfl fun z _ => ?_
          simp_rw [Finset.sum_mul]
          exact integral_finsetSum _ fun w _ =>
            int_L B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)
      _ = ∑ w, ∑ z, ∫ g, (∫ h, ψ x₀ w h * ψ' w z (h⁻¹ * g) ∂B.ν) * F (p, z) (X * finH g) ∂B.ν :=
          Finset.sum_comm
      _ = ∑ w, ∑ z, ∫ h, ψ x₀ w h * ∫ k, ψ' w z k * F (p, z) (X * finH h * finH k) ∂B.ν ∂B.ν := by
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
          rw [swap_key B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)]
          simp only [finH_mul', mul_assoc]
      _ = ∑ w, ∫ h, ψ x₀ w h * ∑ z, ∫ k, ψ' w z k * F (p, z) (X * finH h * finH k) ∂B.ν ∂B.ν := by
          refine Finset.sum_congr rfl fun w _ => ?_
          simp_rw [Finset.mul_sum]
          refine (integral_finsetSum _ fun z _ => ?_).symm
          have := int_R B.ν (hψ x₀ w).1 (hψ x₀ w).2 (hψ' w z).1 (hψ' w z).2 (hfc z)
          simpa only [finH_mul', mul_assoc] using this
  · intro hψU i u hu x
    simp only [convF]
    refine Finset.sum_congr rfl fun z _ => ?_
    have e := integral_mul_left_eq_self (μ := B.ν) (fun k => ψ' i.2 z k * F (i.1, z) (x * finH k)) u
    simp only [hψU _ _ u hu, finH_mul', ← mul_assoc] at e
    exact e

theorem fmOneOf_holds : FmOneOf := by
  intro hOff hIdem E _ _ _ κ _ S P B e hS hP U₁ U₂ L A F w₀ hU₁ hU₂ hL hD hF hw₀
  have hLev : ∀ i, HasLev (F i) := fun i => (hF i).1

  have hxy : ∀ x y : B.κ, (∀ w : P, e x w = e y w) → x = y := fun x y h => e.injective (funext h)

  have hent : ∀ (x : B.κ) (w : Pl E), (w ∉ P → L.s w = idem (U₁ w)) → L.ent P (e x) (e x) w = idem (U₁ w) := by
    intro x w hw
    unfold LM.ent
    split_ifs with h
    · rw [hD w h]; simp
    · exact hw h
  have hP1 : ∀ (w : Pl E) (G : H E B.a B.b → ℂ), w ∈ S → HasLev G → G ∈ fixed (pairRt B.a B.b w) (U₁ w) →
      actP w (idem (U₁ w)) G = G := fun w G _ hG hfx =>
    ((hIdem E B.a B.b w (U₁ w) G (hU₁.1 w).1 (hU₁.1 w).2 hG).1).2 hfx
  have hT1 : ∀ (w : Pl E) (G : H E B.a B.b → ℂ), HasLev G → G ∈ fixed (pairRtT B.a B.b w) (U₂ w) →
      actT w (idem (U₂ w)) G = G := fun w G hG hfx =>
    ((hIdem E B.a B.b w (U₂ w) G (hU₂.1 w).1 (hU₂.1 w).2 hG).2).2 hfx
  refine ⟨fun hw₀P hs ht i => ?_, fun hsp hs ht i => ?_⟩
  · have hne : ∀ w ∈ P, ∀ h : w ∈ S, (Sum.inl ⟨w₀, hw₀⟩ : Slot S) ≠ Sum.inl ⟨w, h⟩ := by
      intro w hwP h heq
      have : w₀ = w := congrArg Subtype.val (Sum.inl_injective heq)
      exact hw₀P (this ▸ hwP)
    have hQ : Quiet S P B e L (Sum.inl ⟨w₀, hw₀⟩) F := by
      refine ⟨fun w hwP hw x y hxy' => ?_, fun j hj p x y hxe => ?_⟩
      · rw [hD w hwP, if_neg hxy']
      · have hx : x = y := hxy x y fun w => hxe w fun h => hne w.1 w.2 h
        subst hx
        rcases j with ⟨w, hwS⟩ | ⟨w, hwS, hwsp⟩
        · have hww : w ≠ w₀ := fun h => hj (by subst h; rfl)
          show actP w (L.ent P (e x) (e x) w) (F (p, x)) = F (p, x)
          rw [hent x w fun _ => hs w hww]
          exact hP1 w _ hwS (hLev _) ((hF _).2 w hwS).1
        · show actT w (L.t w) (F (p, x)) = F (p, x)
          rw [ht w]
          exact hT1 w _ (hLev _) (((hF _).2 w hwS).2 hwsp)
    obtain ⟨p, x⟩ := i
    exact hOff E κ S P B e hS hP A L (Sum.inl ⟨w₀, hw₀⟩) F hL hLev hne hQ p x
  · have hne : ∀ w ∈ P, ∀ h : w ∈ S, (Sum.inr ⟨w₀, hw₀, hsp⟩ : Slot S) ≠ Sum.inl ⟨w, h⟩ := by
      intro w _ h heq
      cases heq
    have hQ : Quiet S P B e L (Sum.inr ⟨w₀, hw₀, hsp⟩) F := by
      refine ⟨fun w hwP hw x y hxy' => ?_, fun j hj p x y hxe => ?_⟩
      · rw [hD w hwP, if_neg hxy']
      · have hx : x = y := hxy x y fun w => hxe w fun h => hne w.1 w.2 h
        subst hx
        rcases j with ⟨w, hwS⟩ | ⟨w, hwS, hwsp⟩
        · show actP w (L.ent P (e x) (e x) w) (F (p, x)) = F (p, x)
          rw [hent x w fun _ => hs w]
          exact hP1 w _ hwS (hLev _) ((hF _).2 w hwS).1
        · have hww : w ≠ w₀ := fun h => hj (by subst h; rfl)
          show actT w (L.t w) (F (p, x)) = F (p, x)
          rw [ht w hww]
          exact hT1 w _ (hLev _) (((hF _).2 w hwS).2 hwsp)
    obtain ⟨p, x⟩ := i
    exact hOff E κ S P B e hS hP A L (Sum.inr ⟨w₀, hw₀, hsp⟩) F hL hLev hne hQ p x

end PositivityTheory.Rg.BcB.F.FA

end
