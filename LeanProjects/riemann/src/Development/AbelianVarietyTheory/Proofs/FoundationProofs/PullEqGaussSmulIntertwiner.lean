import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergReproducingKernelSumSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralHeisKerSumDiag
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralKerSumGraphEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTransport
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.UnitaryTheta.Constant

section General

open Complex MeasureTheory
open scoped Real ComplexConjugate

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [MeasurableSpace V] [BorelSpace V]

theorem const_eq (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (hH : IsPosHerm H) (a : V ≃ₗ[ℂ] V)
    (ha : ∀ z w, H (a z) (a w) = H z w) (hdet : LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0)
    (C : V →ₗ[ℂ] V) (hC : ∀ x, C (x - a x) = (1 / 2 : ℂ) • (x + a x))
    (A A₁ : AddSubgroup V) [DiscreteTopology A] (hfg : A.FG) (hsp : Submodule.span ℝ (A : Set V) = ⊤)
    [Finite (A₁ ⧸ A.addSubgroupOf A₁)] (hA₁ : ∀ y, a y ∈ A → y ∈ A₁)
    (hint : ∀ x ∈ A₁, ∀ y ∈ A₁, ∃ m : ℤ, (H x y).im = m)
    (α : V → ℂ) (hα : IsSemichar H A α) (hαa : ∀ y, α (a y) = α y) (hαn : ∀ y, α (-y) = α y)
    (m : ℕ) (hm : 0 < m) (hmA : ∀ x ∈ A, ∃ y ∈ A, a y ∈ A ∧ m • x = y - a y)
    (c : ℂ) (n : ℝ) (hn : 0 < n)
    (hc : ∀ z w, kerSum H A α z (a w) = c * ((n : ℂ) * ∑ᶠ q : A₁ ⧸ A.addSubgroupOf A₁,
      α ((q.out : A₁) : V) * Heisenberg₂ H ((q.out : A₁) : V) (kerSum H A α z) w)) :
    ∃ r : ℝ, 0 < r ∧ c = r * (LinearMap.det (1 - (a : V →ₗ[ℂ] V)))⁻¹ *
      ∑ᶠ q : A ⧸ (subLa m A).addSubgroupOf A, α ((q.out : A) : V) *
        cexp (-(π : ℂ) * H (C ((q.out : A) : V)) ((q.out : A) : V)) := by
  set B : V →ₗ[ℂ] V := C + (1 / 2 : ℂ) • LinearMap.id with hBdef
  have hB1 : ∀ y, B (y - a y) = y := by
    intro y
    simp only [hBdef, LinearMap.add_apply, hC, LinearMap.smul_apply, LinearMap.id_apply]
    module
  have hsurj : ∀ x, ∃ y, x = y - a y := by
    intro x
    have hu : IsUnit (1 - (a : V →ₗ[ℂ] V)) := (LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet)
    obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 hu).2 x
    exact ⟨y, by rw [← hy]; simp⟩
  have hB2 : ∀ x, B x - a (B x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hB1]
  have hCB : ∀ x, H (C x) x = I * ((H (B x) x).im : ℂ) := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hB1, hC]
    have h1 := hH.1 (a y) y
    have h2 : (H y y).im = 0 := Complex.conj_eq_iff_im.1 (hH.1 y y).symm
    simp only [map_smul, map_add, map_sub, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, ha, h1,
      smul_eq_mul]
    apply Complex.ext <;> simp [h2] <;> ring
  let Λ : AddSubgroup V := (subLa m A).comap (1 - (a : V →ₗ[ℂ] V)).toAddMonoidHom
  have hΛ : ∀ y, y ∈ Λ ↔ y - a y ∈ subLa m A := fun y => by simp [Λ]
  have hΛ' : ∀ y ∈ Λ, y ∈ A ∧ a y ∈ A := by
    intro y hy
    obtain ⟨x, hx, e⟩ := (hΛ y).1 hy
    obtain ⟨y', h1, h2, h3⟩ := hmA x hx
    have : y = y' := by
      rw [← hB1 y, ← hB1 y', ← h3, ← e]; rfl
    rw [this]; exact ⟨h1, h2⟩
  have hle : Λ ≤ A := fun y hy => (hΛ' y hy).1
  have hdisc : DiscreteTopology Λ := DiscreteTopology.of_subset (s := (A : Set V)) inferInstance hle
  have hspan : Submodule.span ℝ (Λ : Set V) = ⊤ := by
    have h1 : ∀ x ∈ Submodule.span ℝ (A : Set V), B x ∈ Submodule.span ℝ (Λ : Set V) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        have h2 : B (m • x) ∈ Λ := by
          rw [hΛ, hB2]; exact ⟨x, hx, rfl⟩
        have h3 : B x = (m : ℝ)⁻¹ • B (m • x) := by
          rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
        rw [h3]
        exact Submodule.smul_mem _ _ (Submodule.subset_span h2)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul t x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro y _
    rw [← hB1 y]
    exact h1 _ (hsp ▸ Submodule.mem_top)
  obtain ⟨k, b, hb⟩ := GlobalTheory.ThetaInter.exists_basis hdisc hspan
  have hFd : IsAddFundamentalDomain Λ (ZSpan.fundamentalDomain b) μ := by
    rw [← hb]; exact ZSpan.isAddFundamentalDomain' b μ
  have hfin : μ (ZSpan.fundamentalDomain b) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne
  have hpos : 0 < μ.real (ZSpan.fundamentalDomain b) :=
    ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero b) hfin
  haveI : Finite (A ⧸ (subLa m A).addSubgroupOf A) :=
    GlobalTheory.ThetaInter.finite_quot hfg fun x hx => ⟨m, hm, x, hx, rfl⟩
  letI := Fintype.ofFinite (A ⧸ (subLa m A).addSubgroupOf A)
  letI := Fintype.ofFinite (A₁ ⧸ A.addSubgroupOf A₁)
  obtain ⟨κ, hκ, hL⟩ := Graph.integral_kerSum_graph_eq V μ H hH a ha hdet B hB2 A Λ hle (fun y hy => (hΛ' y hy).2) α hα
    (fun y _ => hαa y) _ hFd (A ⧸ (subLa m A).addSubgroupOf A) (fun q => ((q.out : A) : V)) (fun q => (q.out : A).2) (by
      intro x hx
      have h1 : ((((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A).out : A) : V) - x ∈ subLa m A := by
        have := QuotientAddGroup.eq.1
          (Quotient.out_eq ((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A)).symm
        rw [AddSubgroup.mem_addSubgroupOf] at this
        simpa [neg_add_eq_sub] using this
      refine ⟨(((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A), ⟨B _, by rw [hΛ, hB2]; exact h1⟩), ?_, ?_⟩
      · simp only [hB2]; abel
      · rintro ⟨q, y, hy⟩ e
        simp only at e
        have hq : q = ((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A) := by
          rw [← Quotient.out_eq q]
          refine (QuotientAddGroup.eq.2 ?_).symm
          rw [AddSubgroup.mem_addSubgroupOf]
          convert (hΛ y).1 hy using 1
          simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
          rw [e]; abel
        subst hq
        refine Prod.ext rfl (Subtype.ext ?_)
        simp only
        rw [← hB1 y]
        congr 1
        exact (sub_sub_cancel _ _).symm.trans (congrArg _ e.symm))
  have hR := fun q : A₁ ⧸ A.addSubgroupOf A₁ => integral_heis_kerSum_diag V μ H hH A Λ hle α hα _ hFd hfin
    ((q.out : A₁) : V) fun y hy => hint _ (q.out : A₁).2 y (hA₁ y (hΛ' y hy).2)
  have hsum : ∫ z in ZSpan.fundamentalDomain b, kerSum H A α z (a z) * cexp (-(π : ℂ) * H z z) ∂μ =
      c * n * (μ.real (ZSpan.fundamentalDomain b) : ℂ) := by
    have e : ∀ z, kerSum H A α z (a z) * cexp (-(π : ℂ) * H z z) = c * n * ∑ q : A₁ ⧸ A.addSubgroupOf A₁,
        α ((q.out : A₁) : V) * (Heisenberg₂ H ((q.out : A₁) : V) (kerSum H A α z) z * cexp (-(π : ℂ) * H z z)) := by
      intro z
      rw [hc, finsum_eq_sum_of_fintype]
      simp only [← mul_assoc, ← Finset.sum_mul]
    simp only [e]
    rw [integral_const_mul, integral_finset_sum _ fun q _ => (hR q).1.const_mul _]
    congr 1
    rw [Finset.sum_eq_single 0]
    · have h0 := (GlobalTheory.ThetaInter.out_mem_iff (A₁ := A) (A₂ := A₁) 0).2 rfl
      rw [integral_const_mul, (hR 0).2, if_pos h0, hαn, ← mul_assoc]
      rcases hα.1 _ h0 with h | h <;> simp [h]
    · intro q _ hq
      rw [integral_const_mul, (hR q).2, if_neg (fun h => hq ((GlobalTheory.ThetaInter.out_mem_iff q).1 h)), mul_zero]
    · simp
  refine ⟨κ / (n * μ.real (ZSpan.fundamentalDomain b)), by positivity, ?_⟩
  rw [finsum_eq_sum_of_fintype]
  simp only [hCB]
  have e : ∀ t : ℂ, -(π : ℂ) * (I * t) = -((π : ℂ) * I) * t := fun t => by ring
  simp only [e]
  rw [hsum] at hL
  have h1 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : (μ.real (ZSpan.fundamentalDomain b) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast
  field_simp
  field_simp at hL
  linear_combination hL

end General

open MeasureTheory GlobalTheory.ThetaInter in

theorem pull_eq_gauss_smul_intertwiner : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → ∀ (C : VC D N N' →ₗ[ℂ] VC D N N'), (∀ x, C (x - u.symm x) = (1 / 2 : ℂ) • (x + u.symm x)) → ∀ m : ℕ, 0 < m → (∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → ∀ th ∈ ThSp D (tor0 D cc δ) A, th ≠ 0 → ∃ (c : ℂ) (r : ℝ), ‖c‖ = 1 ∧ 0 < r ∧ c = r * (LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')))⁻¹ * (∑ᶠ q : A ⧸ (subLa m A).addSubgroupOf A, al D (tor0 D cc δ) ((q.out : A) : VC D N N') * Complex.exp (-(Real.pi : ℂ) * Hf D (tor0 D cc δ) (C ((q.out : A) : VC D N N')) ((q.out : A) : VC D N N'))) ∧ (fun z => th (u.symm z)) = c • Iop D (tor0 D cc δ) A A₁ th := by
  intro D cc δ hc N N' A A₁ h₁ h₂ u hu hA hdet C hC m hm hmA th hth hne
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨f₁, s₁, d₁, c₁⟩ := klat_facts hc h₁
  obtain ⟨f₂, -, -, -⟩ := klat_facts hc h₂
  obtain ⟨l₁, -, i₁, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hc N N' A h₁
  obtain ⟨l₂, -, i₂, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hc N N' A₁ h₂
  have := klat_finite hG.1 hc.1.1 h₁ h₂ f₂
  have : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (VC D N N')).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual (isHerm_sesqOf D (tor0 D cc δ) N N') d₁ f₁
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_periodPair_idealCurveLattice D cc δ hc
  have hH := isPosHerm_formV D (tor0 D cc δ) N N' (GlobalTheory.T.latticeCovolume_pos_and_selfDual L _ hL).1
  have hα : IsSemichar (formV D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) := by
    refine ⟨c₁.1, i₁, fun x hx y hy => ?_⟩
    rw [c₁.2 x hx y hy]
    obtain ⟨k, hk⟩ := i₁ x hx y hy
    congr 1
    change Complex.exp (_ * ((Hf D _ x y).im : ℂ)) = Complex.exp (_ * ((Hf D _ x y).im : ℂ))
    rw [hk, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨k, by push_cast; ring⟩
  obtain ⟨p₁, p₂, p₃⟩ := GlobalTheory.ThetaIso.theta_transport D cc δ hc N N' A A₁ h₁ h₂ u hu hA th hth
  obtain ⟨-, q₁, q₂, q₃⟩ := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' A A₁ h₁ h₂ th hth
  have hsm : ∀ (B B' : AddSubgroup (VC D N N')) [Finite (B' ⧸ B.addSubgroupOf B')] (t : ℂ) (G : VC D N N' → ℂ),
      Iop D (tor0 D cc δ) B B' (t • G) = t • Iop D (tor0 D cc δ) B B' G := by
    intro B B' _ t G
    letI := Fintype.ofFinite (B' ⧸ B.addSubgroupOf B')
    funext z
    simp only [Iop, U, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hI : Iop D (tor0 D cc δ) A A₁ th ≠ 0 := by
    intro h
    apply hne
    rw [← q₃, h]
    funext z
    simp [Iop, U]
  obtain ⟨c, hcI⟩ := l₂ _ p₁ _ q₁ hI
  have hnorm : ‖c‖ = 1 := by
    have h1 : normSq D (tor0 D cc δ) A₁ (c • Iop D (tor0 D cc δ) A A₁ th) =
        ‖c‖ ^ 2 * normSq D (tor0 D cc δ) A₁ (Iop D (tor0 D cc δ) A A₁ th) := by
      simp only [normSq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_assoc, average_eq, integral_const_mul]
      ring
    rw [← hcI, p₂, q₂] at h1
    have h2 : ‖c‖ ^ 2 = 1 := by
      have := (p₃ hne).ne'
      field_simp at h1
      exact h1.symm
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h2, one_pow])
  have hu' : ∀ z w, Hf D (tor0 D cc δ) (u.symm z) (u.symm w) = Hf D (tor0 D cc δ) z w := fun z w => by
    rw [← hu, u.apply_symm_apply, u.apply_symm_apply]
  obtain ⟨-, k₁, k₂⟩ := KerSum.kerSum_spec _ _ hH A _ hα
  have hidx : 0 < ((A.addSubgroupOf A₁).index : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite
  obtain ⟨r, hr, hrc⟩ := const_eq volume (formV D (tor0 D cc δ) N N') hH u.symm hu' hdet C hC A A₁ f₁ s₁
    (fun y hy => by simpa using (hA _).1 hy) i₂ (al D (tor0 D cc δ)) hα (fun y => by simp only [al, hu'])
    (fun y => by simp [al, Hf]) m hm hmA c (Real.sqrt ((A.addSubgroupOf A₁).index : ℝ))⁻¹
    (inv_pos.2 (Real.sqrt_pos.2 hidx)) (by
      intro z w
      obtain ⟨t, ht⟩ := l₁ _ ⟨k₁ z, k₂ z⟩ th hth hne
      have h1 : kerSum (formV D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) z (u.symm w) =
          c * Iop D (tor0 D cc δ) A A₁ (kerSum (formV D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) z) w := by
        rw [ht, hsm]
        have := congrFun hcI w
        simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [this]; ring
      rw [h1, Iop, Complex.ofReal_inv]
      rfl)
  exact ⟨c, r, hnorm, hr, hrc, hcI⟩

end GlobalTheory.UnitaryTheta.Constant
