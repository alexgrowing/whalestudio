import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCubeVolume

namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
  MeasureTheory Set Filter

noncomputable section

lemma cube_int_shift {N : ℕ} (φ : (Fin N → ℝ) → ℂ) (hφ : Continuous φ)
    (hp : ∀ (n : Fin N → ℤ) t, φ (t + fun i => (n i : ℝ)) = φ t) (s : Fin N → ℝ) :
    ∫ t in cube N, φ (t + s) = ∫ t in cube N, φ t := by
  classical
  have hcube : cube N = Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) 1 := rfl
  let b := Pi.basisFun ℝ (Fin N)
  let L := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  have hF : IsAddFundamentalDomain L (ZSpan.fundamentalDomain b) volume :=
    ZSpan.isAddFundamentalDomain b volume
  have key : ∀ g : L, ∃ n : Fin N → ℤ, (g : Fin N → ℝ) = fun i => (n i : ℝ) := fun g => by
    have hg := (b.mem_span_iff_repr_mem ℤ (g : Fin N → ℝ)).1 g.2
    choose n hn using hg
    exact ⟨n, funext fun i => by simpa [b] using (hn i).symm⟩
  haveI : Countable L := by
    choose f hf using key
    exact Function.Injective.countable (f := f) fun g₁ g₂ h => Subtype.ext (by rw [hf g₁, hf g₂, h])
  have hinv : ∀ g : L, ∀ x, φ (g +ᵥ x) = φ x := by
    intro g x
    obtain ⟨n, hgn⟩ := key g
    show φ ((g : Fin N → ℝ) + x) = φ x
    rw [hgn, add_comm]
    exact hp n x
  have hFs : IsAddFundamentalDomain L ((fun t => t - s) ⁻¹' ZSpan.fundamentalDomain b) volume :=
    hF.preimage_of_equiv (measurePreserving_sub_right volume s).quasiMeasurePreserving
      (e := id) Function.bijective_id fun g x => by
        show ((g : Fin N → ℝ) + x) - s = (g : Fin N → ℝ) + (x - s)
        exact add_sub_assoc _ _ _
  have hae : ZSpan.fundamentalDomain b =ᵐ[volume] cube N := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, hcube, volume_pi]
    exact Measure.ae_eq_set_pi fun _ _ => Ico_ae_eq_Icc
  have hpre : (fun t => t + s) ⁻¹' ((fun t => t - s) ⁻¹' ZSpan.fundamentalDomain b) =
      ZSpan.fundamentalDomain b := by
    ext t
    simp
  calc ∫ t in cube N, φ (t + s) = ∫ t in ZSpan.fundamentalDomain b, φ (t + s) :=
        setIntegral_congr_set hae.symm
    _ = ∫ t in (fun t => t + s) ⁻¹' ((fun t => t - s) ⁻¹' ZSpan.fundamentalDomain b), φ (t + s) := by
        rw [hpre]
    _ = ∫ u in (fun t => t - s) ⁻¹' ZSpan.fundamentalDomain b, φ u :=
        (measurePreserving_add_right volume s).setIntegral_preimage_emb
          (MeasurableEquiv.addRight s).measurableEmbedding _ _
    _ = ∫ u in ZSpan.fundamentalDomain b, φ u := hFs.setIntegral_eq hF hinv
    _ = ∫ t in cube N, φ t := setIntegral_congr_set hae

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {u : Fin 2 → Fin r → E} {g : ℕ} {ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
  {G : Frame X.Ψ r → ℂ}

theorem Ich_Zb (hω : X.IsLZBasis g ω)
    (hadd : ∀ b b' x, X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x)
    (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)
    (hG : DifferentiableOn ℂ G X.dom) (hper : ∀ b ∈ X.LZ g, ∀ x ∈ X.dom, G (X.Zb u b x) = G x)
    {χ : X.Ψ → Fin 2 → Fin 2 → ℂ} (hfreq : ∀ j, ∃ k : ℤ, 2 * X.pairR χ (ω j) = k)
    {b : X.Ψ → Fin 2 → Fin 2 → ℂ} (hb : IsHermFam b) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Ich X u ω G χ (X.Zb u b x) = cexp (4 * Real.pi * I * X.pairR χ b) * Ich X u ω G χ x := by
  have hωh : ∀ j, IsHermFam (ω j) := by
    intro j τ i k
    obtain ⟨β, hβ, -, hb⟩ := hω.1 j
    rw [hb]
    simp only [Data.embH]
    rw [← hβ i k, cc, NumberField.IsCMField.complexEmbedding_complexConj]
  obtain ⟨s, hs⟩ : ∃ s : Fin (4 * Fintype.card X.Ψ) → ℝ, Bv ω s = b := by
    let H : Submodule ℝ (X.Ψ → Fin 2 → Fin 2 → ℂ) :=
      { carrier := {b | IsHermFam b}
        add_mem' := fun {a c} ha hc τ i k => by
          simp only [Pi.add_apply, map_add]
          rw [ha τ i k, hc τ i k]
        zero_mem' := fun τ i k => by simp
        smul_mem' := fun r a ha τ i k => by
          simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
          rw [ha τ i k] }
    have hωH : ∀ j, ω j ∈ H := hωh
    let f : (X.Ψ → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] (X.Ψ → Fin 4 → ℝ) :=
      { toFun := fun b τ => ![(b τ 0 0).re, (b τ 1 1).re, (b τ 0 1).re, (b τ 0 1).im]
        map_add' := fun a c => by
          funext τ m
          fin_cases m <;> simp
        map_smul' := fun r a => by
          funext τ m
          fin_cases m <;> simp }
    have hinj : Function.Injective (f.comp H.subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro a ha
      have hh : IsHermFam (a : X.Ψ → Fin 2 → Fin 2 → ℂ) := a.2
      apply Subtype.ext
      funext τ i k
      show (a : X.Ψ → Fin 2 → Fin 2 → ℂ) τ i k = 0
      have e := fun m => congrFun (congrFun ha τ) m
      have e0 : (a.1 τ 0 0).re = 0 := by simpa [f] using e 0
      have e1 : (a.1 τ 1 1).re = 0 := by simpa [f] using e 1
      have e2 : (a.1 τ 0 1).re = 0 := by simpa [f] using e 2
      have e3 : (a.1 τ 0 1).im = 0 := by simpa [f] using e 3
      have i00 : (a.1 τ 0 0).im = 0 := by
        have h := congrArg Complex.im (hh τ 0 0)
        rw [Complex.conj_im] at h
        linarith
      have i11 : (a.1 τ 1 1).im = 0 := by
        have h := congrArg Complex.im (hh τ 1 1)
        rw [Complex.conj_im] at h
        linarith
      have z00 : a.1 τ 0 0 = 0 := Complex.ext (by simpa using e0) (by simpa using i00)
      have z11 : a.1 τ 1 1 = 0 := Complex.ext (by simpa using e1) (by simpa using i11)
      have z01 : a.1 τ 0 1 = 0 := Complex.ext (by simpa using e2) (by simpa using e3)
      have z10 : a.1 τ 1 0 = 0 := by rw [hh τ 0 1, z01, map_zero]
      fin_cases i <;> fin_cases k
      · exact z00
      · exact z01
      · exact z10
      · exact z11
    have hH : Module.finrank ℝ H ≤ 4 * Fintype.card X.Ψ := by
      have h := LinearMap.finrank_le_finrank_of_injective hinj
      simpa [Module.finrank_pi_fintype, Module.finrank_fin_fun, Finset.sum_const, mul_comm] using h
    have hspan : Submodule.span ℝ (Set.range ω) = H := by
      apply Submodule.eq_of_le_of_finrank_le
      · exact Submodule.span_le.2 (Set.range_subset_iff.2 hωH)
      · rw [finrank_span_eq_card hω.2.2, Fintype.card_fin]
        exact hH
    have hbH : b ∈ H := hb
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hbH
    obtain ⟨c, hc⟩ := hbH
    refine ⟨c, ?_⟩
    rw [← hc]
    funext τ i k
    simp [Bv, Finset.sum_apply, Complex.real_smul]
  subst hs
  choose k hk using hfreq
  have hLZ : ∀ n : Fin (4 * Fintype.card X.Ψ) → ℤ, Bv ω (fun i => (n i : ℝ)) ∈ X.LZ g := by
    intro n
    have hsum : ∀ S : Finset (Fin (4 * Fintype.card X.Ψ)),
        ∑ j ∈ S, ((n j : ℝ) : ℂ) • ω j ∈ X.LZ g := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        refine ⟨0, fun i k => by simp [cc], fun i k => ⟨0, isIntegral_zero, by simp⟩, ?_⟩
        funext τ i k
        simp [Data.embH]
      | insert j S hj ih =>
        rw [Finset.sum_insert hj]
        obtain ⟨β, hβ, hint, hb⟩ := hω.1 j
        obtain ⟨β', hβ', hint', hb'⟩ := ih
        simp only [cc] at hβ hβ'
        refine ⟨(n j : E) • β + β', fun i k => ?_, fun i k => ?_, ?_⟩
        · simp [cc, hβ, hβ', map_add, map_mul, map_intCast]
        · obtain ⟨γ, hγ, hγe⟩ := hint i k
          obtain ⟨γ', hγ', hγe'⟩ := hint' i k
          have hn : IsIntegral ℤ (n j : E) := by
            simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := n j)
          refine ⟨(n j : E) * γ + γ', (hn.mul hγ).add hγ', ?_⟩
          simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hγe, hγe']
          ring
        · rw [hb, hb']
          funext τ i k
          simp [Data.embH, map_add, map_mul, map_intCast]
    exact hsum Finset.univ
  have hZc : Continuous fun t : Fin (4 * Fintype.card X.Ψ) → ℝ => X.Zb u (Bv ω t) x := by
    refine continuous_pi fun τ => ?_
    show Continuous fun t => X.zmat u (Bv ω t) τ * mat x τ
    refine Continuous.matrix_mul ?_ continuous_const
    refine continuous_pi fun a => continuous_pi fun j => ?_
    simp only [Data.zmat, Matrix.of_apply, Bv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hec : Continuous fun t : Fin (4 * Fintype.card X.Ψ) → ℝ => ech ω χ t := by
    simp only [ech, pr, Bv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hcont : Continuous fun t : Fin (4 * Fintype.card X.Ψ) → ℝ => G (X.Zb u (Bv ω t) x) * ech ω χ t :=
    (hG.continuousOn.comp_continuous hZc fun t => hdomH _ (Bv_herm ω hωh t) x hx).mul hec
  have hF : ∀ (n : Fin (4 * Fintype.card X.Ψ) → ℤ) (t : Fin (4 * Fintype.card X.Ψ) → ℝ),
      (fun t => G (X.Zb u (Bv ω t) x) * ech ω χ t) (t + fun i => (n i : ℝ)) =
        (fun t => G (X.Zb u (Bv ω t) x) * ech ω χ t) t := by
    intro n t
    show G (X.Zb u (Bv ω (t + fun i => (n i : ℝ))) x) * ech ω χ (t + fun i => (n i : ℝ)) =
      G (X.Zb u (Bv ω t) x) * ech ω χ t
    rw [Bv_add, add_comm (Bv ω t), ← hadd, hper _ (hLZ n) _ (hdomH _ (Bv_herm ω hωh t) x hx),
      ech_add, ech_int (ω := ω) χ hk n, mul_one]
  have hshift := cube_int_shift _ hcont hF s
  have hinv : ech ω χ s * cexp (4 * Real.pi * I * X.pairR χ (Bv ω s)) = 1 := by
    show cexp (-(4 * Real.pi * I) * (X.pairR χ (Bv ω s) : ℂ)) *
      cexp (4 * Real.pi * I * X.pairR χ (Bv ω s)) = 1
    rw [← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  have hpt : ∀ t, G (X.Zb u (Bv ω t) (X.Zb u (Bv ω s) x)) * ech ω χ t =
      (G (X.Zb u (Bv ω (t + s)) x) * ech ω χ (t + s)) *
        cexp (4 * Real.pi * I * X.pairR χ (Bv ω s)) := by
    intro t
    rw [hadd, ← Bv_add, ech_add, mul_assoc, mul_assoc, hinv, mul_one]
  show ∫ t in cube (4 * Fintype.card X.Ψ), G (X.Zb u (Bv ω t) (X.Zb u (Bv ω s) x)) * ech ω χ t =
    cexp (4 * Real.pi * I * X.pairR χ (Bv ω s)) *
      ∫ t in cube (4 * Fintype.card X.Ψ), G (X.Zb u (Bv ω t) x) * ech ω χ t
  simp_rw [hpt]
  rw [integral_mul_const, hshift, mul_comm]

theorem Ich_bound (hω : X.IsLZBasis g ω)
    (hunit : ∀ b, IsHermFam b → X.IsUnitaryC (X.zmat u b)) (la : Wt X.Ψ r)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) {M : ℝ}
    (hM : ∀ b, IsHermFam b → X.pnorm la G (X.Zb u b x) ≤ M) :
    ‖Ich X u ω G χ x‖ * fac X la x ≤ M := by
  have hωh : ∀ j, IsHermFam (ω j) := by
    intro j τ i k
    obtain ⟨β, hβ, -, hb⟩ := hω.1 j
    rw [hb]
    simp only [Data.embH]
    rw [← hβ i k, cc, NumberField.IsCMField.complexEmbedding_complexConj]
  have hBv : ∀ t : Fin (4 * Fintype.card X.Ψ) → ℝ, IsHermFam (Bv ω t) := by
    intro t τ i k
    simp only [Bv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
    exact Finset.sum_congr rfl fun j _ => by rw [hωh j τ i k]
  have hfac : ∀ b, IsHermFam b → fac X la (X.Zb u b x) = fac X la x := by
    intro b hb
    have hd : ∀ τ i, dmin X.Gm (X.Zb u b x) τ i = dmin X.Gm x τ i := by
      intro τ i
      unfold dmin
      congr 1
      ext a c
      have hcol : ∀ a, col (mat (X.Zb u b x) τ) a =
          Matrix.mulVec (X.zmat u b τ) (col (mat x τ) a) := by
        intro a
        ext k
        show (X.zmat u b τ * mat x τ) k a = ∑ j, X.zmat u b τ k j * col (mat x τ) a j
        rw [Matrix.mul_apply]
        rfl
      simp only [gram, Matrix.of_apply]
      rw [hcol, hcol, hunit b hb τ]
    simp only [fac, hd]
  have hnn : ∀ y, 0 ≤ fac X la y := fun y =>
    Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hpn : ∀ y, X.pnorm la G y = ‖G y‖ * fac X la y := fun y => rfl
  have hech : ∀ t, ‖ech ω χ t‖ = 1 := fun t => by
    unfold ech
    rw [Complex.norm_exp]
    simp
  have hcube1 : ∀ n, volume (cube n) = 1 := fun n => by
    rw [show cube n = Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) from rfl, volume_pi,
      Measure.pi_pi]
    simp
  rcases (hnn x).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    have h1 := hM _ (hBv 0)
    rw [hpn] at h1
    exact le_trans (mul_nonneg (norm_nonneg _) (hnn _)) h1
  · have hb : ∀ t ∈ cube (4 * Fintype.card X.Ψ),
        ‖G (X.Zb u (Bv ω t) x) * ech ω χ t‖ ≤ M / fac X la x := by
      intro t _
      rw [norm_mul, hech, mul_one, le_div_iff₀ hpos, ← hfac _ (hBv t), ← hpn]
      exact hM _ (hBv t)
    have hI : ‖Ich X u ω G χ x‖ ≤ M / fac X la x * (volume (cube (4 * Fintype.card X.Ψ))).toReal :=
      norm_setIntegral_le_of_norm_le_const (by rw [hcube1]; simp) hb
    rw [hcube1, ENNReal.toReal_one, mul_one] at hI
    calc _ ≤ M / fac X la x * fac X la x := mul_le_mul_of_nonneg_right hI (hnn x)
      _ = M := div_mul_cancel₀ M hpos.ne'

theorem Ich_coeff {χ : X.Ψ → Fin 2 → Fin 2 → ℂ} {m : Fin (4 * Fintype.card X.Ψ) → ℤ}
    (hm : ∀ j, 2 * X.pairR χ (ω j) = m j) {x : Frame X.Ψ r}
    (D : C(UnitAddTorus (Fin (4 * Fintype.card X.Ψ)), ℂ))
    (hD : ∀ t, D (I2.DimB.tproj t) = G (X.Zb u (Bv ω t) x)) :
    Ich X u ω G χ x = UnitAddTorus.mFourierCoeff D m := by
  have hp : ∀ j, pr χ (ω j) = (m j : ℝ) / 2 := fun j => by
    have := hm j
    change 2 * pr χ (ω j) = _ at this
    linarith
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ m 0]
  unfold Ich
  rw [← setIntegral_congr_set (ubox_ae _)]
  have e : ∀ t : Fin (4 * Fintype.card X.Ψ) → ℝ, G (X.Zb u (Bv ω t) x) * ech ω χ t =
      UnitAddTorus.mFourier (-m) (fun i => (t i : UnitAddCircle)) •
        D (fun i => (t i : UnitAddCircle)) := by
    intro t
    rw [show (fun i => (t i : UnitAddCircle)) = I2.DimB.tproj t from rfl, hD, I2.DimB.mF_tproj,
      smul_eq_mul, mul_comm]
    congr 1
    simp only [ech, pair_Bv, hp]
    congr 1
    push_cast
    simp only [Pi.neg_apply, Int.cast_neg]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e]
  rfl

end

end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
