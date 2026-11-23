import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFirst

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinSelbergLFunctionAnalytic

theorem eq_zero_of_mul_eq_zero {Lf T Dd : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    (hL : Differentiable ℂ Lf) {t : ℂ} (ht : Lf t ≠ 0) (hT : ContinuousOn T U) (hT0 : T s₀ ≠ 0)
    (hD : ContinuousOn Dd U) (h : ∀ s ∈ U, Lf s * T s * Dd s = 0) : Dd s₀ = 0 := by
  have hLa : AnalyticOnNhd ℂ Lf Set.univ := hL.differentiableOn.analyticOnNhd isOpen_univ
  have hne : ∀ᶠ z in 𝓝[≠] s₀, Lf z ≠ 0 := by
    rcases (hLa s₀ (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h0 | h1
    · have := hLa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ s₀) h0
      exact absurd (this (Set.mem_univ t)) ht
    · exact h1
  have hUn : U ∈ 𝓝 s₀ := hU.mem_nhds hs₀
  have hTc : ContinuousAt T s₀ := hT.continuousAt hUn
  have hDc : ContinuousAt Dd s₀ := hD.continuousAt hUn
  have hT1 : ∀ᶠ z in 𝓝 s₀, T z ≠ 0 := hTc.eventually_ne hT0
  have hz : ∀ᶠ z in 𝓝[≠] s₀, Dd z = 0 := by
    filter_upwards [hne, nhdsWithin_le_nhds hT1, nhdsWithin_le_nhds hUn] with z h1 h2 h3
    have := h z h3
    simpa [h1, h2] using this
  have hl : Tendsto Dd (𝓝[≠] s₀) (𝓝 (Dd s₀)) := hDc.tendsto.mono_left nhdsWithin_le_nhds
  have hl0 : Tendsto Dd (𝓝[≠] s₀) (𝓝 0) := tendsto_const_nhds.congr' (hz.mono fun z hz => hz.symm)
  exact tendsto_nhds_unique hl hl0

theorem one_sub_two_cpow_ne {s : ℂ} (h : 0 < s.re) : 1 - (2 : ℂ) ^ s ≠ 0 := by
  intro h0
  have h1 : (2 : ℂ) ^ s = 1 := (sub_eq_zero.1 h0).symm
  have h2 : ‖((2 : ℝ) : ℂ) ^ s‖ = (2 : ℝ) ^ s.re := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) s
  have h3 : (1 : ℝ) < (2 : ℝ) ^ s.re := Real.one_lt_rpow (by norm_num) h
  rw [show ((2 : ℝ) : ℂ) = 2 by norm_num, h1, norm_one] at h2
  linarith

theorem strip_alg {s A Bq C G G' T T' sg gm g3 gr Es Ep Ls Lp Λs Λp R Bf : ℂ}
    (e1 : (s - 1) ^ 2 * Es = Bq * (C * G * T) * Λs * Ls)
    (e2 : s ^ 2 * Ep = A * (C * G' * T') * Λp * Lp)
    (e3 : A * Es = Bq * Ep) (e6 : T' = sg * gm * g3 * T)
    (e4 : -s * Ls * R = (s - 1) * Bf * gm * Lp)
    (e5 : sg * G' * R = gr * G * Bf)
    (hA : A ≠ 0) (hB : Bq ≠ 0) (hC : C ≠ 0) (hG : G ≠ 0) (hs : s - 1 ≠ 0) (hBf : Bf ≠ 0) (hgm : gm ≠ 0) :
    Lp * T * (-s * Λs - (s - 1) * (gr * g3) * Λp) = 0 := by
  subst e6
  have h1 : s ^ 2 * (C * G * T) * Λs * Ls - (s - 1) ^ 2 * (C * G' * (sg * gm * g3 * T)) * Λp * Lp = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero hA hB)
    linear_combination (-A * s ^ 2) * e1 + (Bq * (s - 1) ^ 2) * e2 + (s ^ 2 * (s - 1) ^ 2) * e3
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hC hG) hs) hBf) hgm)
  linear_combination R * h1 + (s * C * G * T * Λs) * e4 + ((s - 1) ^ 2 * C * gm * g3 * T * Λp * Lp) * e5

theorem IsUnit1.mul' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {a b : Fˣ →* ℂˣ} (ha : IsUnit1 a) (hb : IsUnit1 b) : IsUnit1 (a * b) :=
  ⟨(ha.1.mul hb.1 : Continuous fun x => a x * b x), fun x => by simp [ha.2 x, hb.2 x]⟩

theorem IsUnit1.inv' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {a : Fˣ →* ℂˣ} (ha : IsUnit1 a) : IsUnit1 a⁻¹ :=
  ⟨(ha.1.inv : Continuous fun x => (a x)⁻¹), fun x => by simp [ha.2 x]⟩

theorem localChar_inv (c : HeckeCharacter ℚ) (v : Pl) : localChar c⁻¹ v = (localChar c v)⁻¹ := by
  have h := GroundTheory.Automorphic.GodementSection.localChar_mul_inv (1 : HeckeCharacter ℚ) c v
  have h1 : localChar (1 : HeckeCharacter ℚ) v = 1 := by
    have h2 := GroundTheory.Automorphic.GodementSection.localChar_mul_inv c c v
    rwa [mul_inv_cancel, mul_inv_cancel] at h2
  rw [one_mul, h1, one_mul] at h
  exact h

theorem x1 (hL2 : Ad3.Loc2) (hB : B0) (h9 : A9) (h9g : LocalGammaFunctionalEquation) (h10 : A10) (h11 : A11) (hH : H1) (hF0 : F0b)
    (hF1 : F1) (hX0 : X0) (hXg : RealPlaceGammaFactors) (hXa : HalfPlaneAnalyticIdentities) : X1 := by
  intro k N _ hk χ hχ f a hf ha ω φ hOm hLift hP μ₁ μ₂ φ₀ hM D hDk hDν hDb c δ S hAdm Λ Λ' hC hC'
  obtain ⟨hB1, -, -, -, -, ⟨m, hm⟩, -, -⟩ := hB
  have hstd : ∀ v : Pl, IsStd (localAdelicChar ℚ v) := fun v => (hB1 v).1
  have hu : ∀ (c : HeckeCharacter ℚ) (v : Pl), IsUnit1 (localChar c v) := fun c v => (hB1 v).2.2.2.2.2.2 c
  have hk1 : 1 ≤ k := by omega
  have hSb : ∀ v, pOf v ∣ N → v ∈ S := fun v h => hAdm.bad ((hDb v).2 h)
  have hsign : ∏ v ∈ S, ((localChar ω v (-1) : ℂˣ) : ℂ) = (-1) ^ k :=
    (hF0 k N χ hχ (hF1 k N χ f a hf ha.2.1 ω hOm).1 ω hOm).sign S hSb
  obtain ⟨L, L', hLd, hL'd, hLs, hLfe, hL1, hL1'⟩ := hH c δ S hAdm.fin hAdm.sgn hAdm.unr
  have hXg' := hXg k δ hk1
  have hW : ∀ v, W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) ∈ V2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) :=
    fun v => Submodule.subset_span ⟨φ₀ v, hM.sb v, rfl⟩
  have hW' : ∀ v (x : Qv v), (fun g => W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (g * uni2 x)) ∈
      V2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) :=
    fun v x => (hL2 (Qv v) _ (hstd v) (μ₁ v) (μ₂ v) (hM.u₁ v) (hM.u₂ v)).1.stable _ (hW v) (uni2 x)
  have hZSd : ∀ (c : HeckeCharacter ℚ) (x : ∀ v : S, Qv v.1) (Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ), (∀ v, SB (Ψ v)) →
      DifferentiableOn ℂ (ZS m μ₁ μ₂ φ₀ S x Ψ c) {s | 0 < s.re} := by
    intro c x Ψ hΨ
    refine DifferentiableOn.fun_finset_prod (fun v _ => ?_)
    haveI := (hm v.1).1
    haveI := (hm v.1).2
    exact ((h10 (Qv v.1) _ (hstd v.1) (m v.1) (μ₁ v.1) (μ₂ v.1) (localChar c v.1) (hM.u₁ _) (hM.u₂ _) (hu c _) _
      (hW _) _ (hW' _ (x v))).2 (Ψ v) (hΨ v)).2
  have hex : ∀ s₀ : ℂ, 0 < s₀.re → ∃ (x : ∀ v : S, Qv v.1) (Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ),
      (∀ v, SB (Ψ v)) ∧ ZS m μ₁ μ₂ φ₀ S x Ψ c s₀ ≠ 0 := by
    intro s₀ hs₀
    have h : ∀ v : S, ∃ (x : Qv v.1) (Ψ : (Fin 2 → Qv v.1) → ℂ), SB Ψ ∧
        Zv (m v.1) (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1))
          (fun g => W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (g * uni2 x)) Ψ (localChar c v.1) s₀ ≠ 0 := by
      intro v
      haveI := (hm v.1).1
      haveI := (hm v.1).2
      exact h11 (Qv v.1) _ (hstd v.1) (m v.1) (μ₁ v.1) (μ₂ v.1) (localChar c v.1) (hM.u₁ _) (hM.u₂ _) (hu c _) _
        (hW _) (by rw [hM.one]; exact one_ne_zero) s₀ hs₀
    choose x Ψ hΨ hZ using h
    exact ⟨x, Ψ, hΨ, Finset.prod_ne_zero_iff.2 fun v _ => hZ v⟩
  have hgne : ∀ (v : Pl) (s : ℂ), Strip s → gam (localAdelicChar ℚ v) (localChar c v) s ≠ 0 := by
    intro v s hs h0
    have h := (h9g (Qv v) _ (hstd v) (localChar c v) (hu c v)).2 s hs
    rw [h0, zero_mul] at h
    exact Units.ne_zero _ h.symm
  have hgS : ∀ s, gamS D c δ S s = gamR k δ s *
      ∏ v ∈ S, gam3 (localAdelicChar ℚ v) (μ₁ v * (μ₂ v)⁻¹) (localChar c v) s := by
    intro s
    simp only [gamS, hDk, hDν]
  have pack : ∀ (x : ∀ v : S, Qv v.1) (Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ), (∀ v, SB (Ψ v)) →
      (∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → L' (1 - s) * ZS m μ₁ μ₂ φ₀ S x Ψ c s *
        (-s * Λ s - (s - 1) * gamS D c δ S s * Λ' (1 - s)) = 0) ∧
      (ZS m μ₁ μ₂ φ₀ S x Ψ c 1 ≠ 0 → Dih a ∨ Λ 1 = 0) := by
    intro x Ψ hΨ
    obtain ⟨C, E, E', hC0, hEd, hE'd, hEs, hEfe, hE1⟩ := hX0 k N hk χ hχ f a hf ha ω φ hOm hLift hP μ₁ μ₂ φ₀ hM m hm
      S hSb c δ hAdm.fin hAdm.sgn hAdm.unr x Ψ hΨ
    have hΨ' : ∀ v : S, SB (sF (localAdelicChar ℚ v.1) (Ψ v)) := fun v => RankinSelbergRotation.sF_mem (hstd v.1) (hΨ v)
    have a1 := hXa E Λ L (fun s => C * GG k s * ZS m μ₁ μ₂ φ₀ S x Ψ c s)
      (fun s => ∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c v.1) s) (Lp c S) hEd hC.1 hLd
      (((differentiableOn_const C).mul hXg'.1).mul (hZSd c x Ψ hΨ))
      (fun s hs => ⟨(hEs s hs).1, by rw [hC.2.2 s hs]; simp only [eul, hDν], (hLs s hs).1⟩)
    have a2 := hXa E' Λ' L' (fun s => C * GG k s * ZS m μ₁ μ₂ φ₀ S x (fun v => sF (localAdelicChar ℚ v.1) (Ψ v)) c⁻¹ s)
      (fun s => ∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c⁻¹ v.1) s) (Lp c⁻¹ S) hE'd hC'.1 hL'd
      (((differentiableOn_const C).mul hXg'.1).mul (hZSd c⁻¹ x _ hΨ'))
      (fun s hs => ⟨(hEs s hs).2, by rw [hC'.2.2 s hs]; simp only [eul, hDν], (hLs s hs).2.1⟩)
    refine ⟨fun s h1 h2 => ?_, fun hZ1 => ?_⟩
    · have hs : Strip s := ⟨by linarith, by linarith⟩
      have hre : 1 / 4 < (1 - s).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      have e1 := a1.1 s h1
      have e2 := a2.1 (1 - s) hre
      have e2' : s ^ 2 * E' (1 - s) = (1 - 2 ^ s) * (C * GG k (1 - s) *
          ZS m μ₁ μ₂ φ₀ S x (fun v => sF (localAdelicChar ℚ v.1) (Ψ v)) c⁻¹ (1 - s)) * Λ' (1 - s) * L' (1 - s) := by
        have h3 : (1 - s - 1) ^ 2 = s ^ 2 := by ring
        have h4 : (1 : ℂ) - (1 - s) = s := by ring
        rw [h3, h4] at e2
        exact e2
      have e6 : ZS m μ₁ μ₂ φ₀ S x (fun v => sF (localAdelicChar ℚ v.1) (Ψ v)) c⁻¹ (1 - s) =
          (-1) ^ k * (∏ v ∈ S, gam (localAdelicChar ℚ v) (localChar c v) s) *
            (∏ v ∈ S, gam3 (localAdelicChar ℚ v) (μ₁ v * (μ₂ v)⁻¹) (localChar c v) s) * ZS m μ₁ μ₂ φ₀ S x Ψ c s := by
        have hv : ∀ v : S, Zv (m v.1) (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1))
            (fun g => W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (g * uni2 (x v)))
            (sF (localAdelicChar ℚ v.1) (Ψ v)) (localChar c⁻¹ v.1) (1 - s) =
            ((localChar ω v.1 (-1) : ℂˣ) : ℂ) * gam (localAdelicChar ℚ v.1) (localChar c v.1) s *
              gam3 (localAdelicChar ℚ v.1) (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c v.1) s *
              Zv (m v.1) (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1))
                (fun g => W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (g * uni2 (x v)))
                (Ψ v) (localChar c v.1) s := by
          intro v
          haveI := (hm v.1).1
          haveI := (hm v.1).2
          rw [localChar_inv, ← hM.mul v.1]
          exact h9 (Qv v.1) _ (hstd v.1) (m v.1) (μ₁ v.1) (μ₂ v.1) (localChar c v.1) (hM.u₁ _) (hM.u₂ _) (hu c _)
            (φ₀ v.1) (Ψ v) (hM.sb _) (hΨ v) (x v) s hs
        have p1 := Finset.prod_coe_sort S (fun v => ((localChar ω v (-1) : ℂˣ) : ℂ))
        have p2 := Finset.prod_coe_sort S (fun v => gam (localAdelicChar ℚ v) (localChar c v) s)
        have p3 := Finset.prod_coe_sort S
          (fun v => gam3 (localAdelicChar ℚ v) (μ₁ v * (μ₂ v)⁻¹) (localChar c v) s)
        rw [← hsign, ← p1, ← p2, ← p3]
        simp only [ZS]
        rw [Finset.prod_congr rfl (fun v _ => hv v), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_mul_distrib]
      have hBf : (if δ then -Complex.I else 1) * Complex.Gammaℝ (1 - s + if δ then 1 else 0) ≠ 0 := by
        refine mul_ne_zero ?_ (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
        · cases δ <;> simp
        · cases δ <;> simp <;> linarith [hs.2]
      have hgm : ∏ v ∈ S, gam (localAdelicChar ℚ v) (localChar c v) s ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun v _ => hgne v s hs
      have hs1 : s - 1 ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        simp at this
        linarith [hs.2]
      rw [hgS]
      have hre0 : 0 < (1 - s).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith [hs.2]
      exact strip_alg e1 e2' (hEfe s hs) e6 (hLfe s hs) (hXg'.2.2.2 s hs) (one_sub_two_cpow_ne hs.1)
        (one_sub_two_cpow_ne hre0) hC0
        (hXg'.2.1 s hs.1) hs1 hBf hgm
    · have hZ1' : C * GG k 1 * ZS m μ₁ μ₂ φ₀ S x Ψ c 1 ≠ 0 :=
        mul_ne_zero (mul_ne_zero hC0 (hXg'.2.1 1 (by simp))) hZ1
      have b := a1.2 hZ1'
      by_cases hc : c = 1
      · exact Or.inr (b.1 (hL1 hc))
      · obtain ⟨h0, h1⟩ := hL1' hc
        by_cases hE : E 1 = 0
        · exact Or.inr (b.2 h0 h1 hE)
        · exact Or.inl (hE1 hE hc)
  have hgSd : DifferentiableOn ℂ (gamS D c δ S) {s | Strip s} := by
    have hfun : gamS D c δ S = fun s => gamR k δ s *
        ∏ v ∈ S, gam3 (localAdelicChar ℚ v) (μ₁ v * (μ₂ v)⁻¹) (localChar c v) s := funext hgS
    rw [hfun]
    refine hXg'.2.2.1.mul (DifferentiableOn.fun_finset_prod fun v _ => ?_)
    have hd : ∀ ν : (Qv v)ˣ →* ℂˣ, IsUnit1 ν → DifferentiableOn ℂ (gam (localAdelicChar ℚ v) ν) {s | Strip s} :=
      fun ν hν => (h9g (Qv v) _ (hstd v) ν hν).1
    have hν : IsUnit1 (μ₁ v * (μ₂ v)⁻¹) := IsUnit1.mul' (hM.u₁ v) (IsUnit1.inv' (hM.u₂ v))
    exact ((hd _ (IsUnit1.mul' hν (hu c v))).mul (hd _ (hu c v))).mul (hd _ (IsUnit1.mul' (IsUnit1.inv' hν) (hu c v)))
  have hU : IsOpen {s : ℂ | 1 / 4 < s.re ∧ s.re < 3 / 4} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  refine ⟨fun s₀ h1 h2 => ?_, ?_⟩
  · obtain ⟨x, Ψ, hΨ, hZ⟩ := hex s₀ (by linarith)
    have hLf : Differentiable ℂ fun s => L' (1 - s) := hL'd.comp (differentiable_const _ |>.sub differentiable_id)
    have hne : L' (1 - (-1)) ≠ 0 := by
      have h2' := (hLs 2 (by simp)).2.2
      have h3 : (1 : ℂ) - (-1) = 2 := by norm_num
      rwa [h3]
    have hTc : ContinuousOn (ZS m μ₁ μ₂ φ₀ S x Ψ c) {s : ℂ | 1 / 4 < s.re ∧ s.re < 3 / 4} :=
      ((hZSd c x Ψ hΨ).continuousOn).mono fun s hs => by
        have := hs.1
        show 0 < s.re
        linarith
    have hΛc : ContinuousOn Λ {s : ℂ | 1 / 4 < s.re ∧ s.re < 3 / 4} :=
      hC.1.continuousOn.mono fun s hs => hs.1
    have hΛ'c : ContinuousOn (fun s => Λ' (1 - s)) {s : ℂ | 1 / 4 < s.re ∧ s.re < 3 / 4} :=
      hC'.1.continuousOn.comp (continuousOn_const.sub continuousOn_id) fun s hs => by
        have := hs.2
        show 1 / 4 < (1 - s).re
        simp only [Complex.sub_re, Complex.one_re]
        linarith
    have hgc : ContinuousOn (gamS D c δ S) {s : ℂ | 1 / 4 < s.re ∧ s.re < 3 / 4} :=
      hgSd.continuousOn.mono fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hDc : ContinuousOn (fun s => -s * Λ s - (s - 1) * gamS D c δ S s * Λ' (1 - s))
        {s : ℂ | 1 / 4 < s.re ∧ s.re < 3 / 4} :=
      (continuousOn_id.neg.mul hΛc).sub (((continuousOn_id.sub continuousOn_const).mul hgc).mul hΛ'c)
    have hz := eq_zero_of_mul_eq_zero hU (s₀ := s₀) ⟨h1, h2⟩ hLf hne hTc hZ hDc
      (fun s hs => (pack x Ψ hΨ).1 s hs.1 hs.2)
    exact sub_eq_zero.1 hz
  · obtain ⟨x, Ψ, hΨ, hZ⟩ := hex 1 (by simp)
    exact (pack x Ψ hΨ).2 hZ

end GlobalTheory.CompanionTheory.RankinSelbergLFunctionAnalytic

end
