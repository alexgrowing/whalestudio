import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open GlobalTheory.SplitFlip

noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeAdj

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_out_ne_zero (K : Subgroup G) (hKo : IsOpen (K : Set G)) {φ : G → ℂ} (hφ : HasCompactSupport φ) :
    {q : G ⧸ K | φ q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport φ) :=
    hφ.isCompact.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset fun q hq => ?_
  exact ⟨q.out, subset_tsupport φ hq, QuotientGroup.out_eq' q⟩

variable [MeasurableSpace G] [BorelSpace G]

theorem measure_coset (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (q : G ⧸ K) :
    μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}) = μ (K : Set G) := by
  have e : (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q} = (fun h => q.out⁻¹ * h) ⁻¹' (K : Set G) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  rw [e, measure_preimage_mul]

theorem integral_eq_sum (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤) {φ : G → ℂ} (hφ : HasCompactSupport φ)
    (hr : ∀ g, ∀ k ∈ K, φ (g * k) = φ g) :
    ∫ g, φ g ∂μ = μ.real (K : Set G) • ∑ᶠ q : G ⧸ K, φ q.out := by
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hF := finite_out_ne_zero K hKo hφ
  set S : Finset (G ⧸ K) := hF.toFinset with hS
  have hmeas : ∀ q : G ⧸ K, MeasurableSet ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}) := fun q =>
    ((isOpen_discrete ({q} : Set (G ⧸ K))).preimage QuotientGroup.continuous_mk).measurableSet
  have hout : ∀ g : G, φ ((g : G ⧸ K)).out = φ g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, hr g k k.2]
  have hsum : φ = fun g => ∑ q ∈ S, ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out) g := by
    funext g
    have : ∀ q : G ⧸ K, ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out) g =
        if (g : G ⧸ K) = q then φ q.out else 0 := fun q => by
      simp [Set.indicator_apply]
    simp only [this, Finset.sum_ite_eq]
    split_ifs with h
    · exact (hout g).symm
    · have : φ ((g : G ⧸ K)).out = 0 := by
        by_contra h0
        exact h (hF.mem_toFinset.2 h0)
      rw [← hout g, this]
  have hint : ∀ q ∈ S, Integrable (((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out)) μ := by
    intro q _
    refine (integrable_indicator_iff (hmeas q)).2 (integrableOn_const ?_)
    rw [measure_coset]
    exact hfin
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun q hq => hF.mem_toFinset.2 hq)]
  conv_lhs => rw [hsum]
  rw [integral_finset_sum S hint, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hmeas q)]
  simp only [Measure.real, measure_coset]

theorem adjoint_of_inv (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (e : G → ℂ) (he : HasCompactSupport e)
    (hbi : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, e (k₁ * g * k₂) = e g)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (v w : V) (hv : ∀ k ∈ K, ρ k v = v) (hw : ∀ k ∈ K, ρ k w = w) :
    B (∑ᶠ q : G ⧸ K, e q.out • ρ q.out v) w =
      B v (∑ᶠ q : G ⧸ K, starRingEnd ℂ (e q.out⁻¹) • ρ q.out w) := by
  have hfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  have hpos : μ.real (K : Set G) ≠ 0 :=
    (ENNReal.toReal_pos (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne' hfin).ne'
  set φ₁ : G → ℂ := fun g => e g * B (ρ g v) w with hφ₁
  set φ₂ : G → ℂ := fun g => e g⁻¹ * B v (ρ g w) with hφ₂
  have hinv : ∀ g, φ₂ g = φ₁ g⁻¹ := fun g => by
    have h := hB g (ρ g⁻¹ v) w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    simp only [hφ₁, hφ₂, h]
  have he' : HasCompactSupport (fun g : G => e g⁻¹) := he.comp_homeomorph (Homeomorph.inv G)
  have hc₁ : HasCompactSupport φ₁ := he.mul_right
  have hc₂ : HasCompactSupport φ₂ := he'.mul_right
  have hr₁ : ∀ g, ∀ k ∈ K, φ₁ (g * k) = φ₁ g := fun g k hk => by
    have h1 : e (g * k) = e g := by simpa using hbi 1 K.one_mem k hk g
    simp only [hφ₁, h1, map_mul, Module.End.mul_apply, hv k hk]
  have hr₂ : ∀ g, ∀ k ∈ K, φ₂ (g * k) = φ₂ g := fun g k hk => by
    have h1 : e (g * k)⁻¹ = e g⁻¹ := by
      rw [mul_inv_rev]
      simpa using hbi k⁻¹ (K.inv_mem hk) 1 K.one_mem g⁻¹
    simp only [hφ₂, h1, map_mul, Module.End.mul_apply, hw k hk]
  have hs₁ : (Function.support fun q : G ⧸ K => e q.out • ρ q.out v).Finite :=
    (finite_out_ne_zero K hKo he).subset fun q hq h0 => hq (by simp [show e q.out = 0 from h0])
  have hs₂ : (Function.support fun q : G ⧸ K => starRingEnd ℂ (e q.out⁻¹) • ρ q.out w).Finite :=
    (finite_out_ne_zero K hKo he').subset fun q hq h0 => hq (by simp [show e q.out⁻¹ = 0 from h0])
  have l₁ : B (∑ᶠ q : G ⧸ K, e q.out • ρ q.out v) w = ∑ᶠ q : G ⧸ K, φ₁ q.out := by
    have := AddMonoidHom.map_finsum (AddMonoidHom.mk' (fun x => B x w) (by simp)) hs₁
    simpa [hφ₁] using this
  have l₂ : B v (∑ᶠ q : G ⧸ K, starRingEnd ℂ (e q.out⁻¹) • ρ q.out w) = ∑ᶠ q : G ⧸ K, φ₂ q.out := by
    have := AddMonoidHom.map_finsum (AddMonoidHom.mk' (fun x => B v x) (by simp)) hs₂
    simpa [hφ₂] using this
  have hI : ∫ g, φ₂ g ∂μ = ∫ g, φ₁ g ∂μ := by
    simp only [hinv]
    exact integral_inv_eq_self φ₁ μ
  rw [integral_eq_sum μ K hKo hfin hc₁ hr₁, integral_eq_sum μ K hKo hfin hc₂ hr₂] at hI
  rw [l₁, l₂]
  exact (smul_right_injective ℂ hpos hI).symm

end Abstract

section GeneralLinearIntegers

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isInvInvariant [MeasurableSpace F] [BorelSpace F] (μ : Measure (GL ι F)) [μ.IsHaarMeasure]
    (K : Subgroup (GL ι F)) (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F))) :
    μ.IsInvInvariant := by
  refine ⟨?_⟩
  have hc := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have hne : μ (K : Set (GL ι F)) ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hnt : μ (K : Set (GL ι F)) ≠ ⊤ := hKc.measure_lt_top.ne
  have h2 := congrArg (fun m : Measure (GL ι F) => m (K : Set (GL ι F))) hc
  have hKi : (K : Set (GL ι F))⁻¹ = K := by
    ext x
    simp
  simp only [Measure.inv_apply, hKi, Measure.coe_nnreal_smul_apply] at h2
  have h3 : ((Measure.haarScalarFactor μ.inv μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
  have h4 : Measure.haarScalarFactor μ.inv μ = 1 := by exact_mod_cast h3
  rw [hc, h4, one_smul]

end GeneralLinearIntegers

theorem hk_adjoint : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    IsHk K (hstar e) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
      (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ g v w, B (ρ g v) (ρ g w) = B v w) → ∀ v ∈ fixed ρ K, ∀ w ∈ fixed ρ K,
      B (hk ρ K e v) w = B v (hk ρ K (hstar e) w) := by
  intro F _ _ _ _ ι _ _ K e he
  obtain ⟨hKo, hKc, hc, hbi⟩ := he
  refine ⟨⟨hKo, hKc, ?_, ?_⟩, ?_⟩
  · have h1 : HasCompactSupport (fun g : GL ι F => e g⁻¹) := hc.comp_homeomorph (Homeomorph.inv _)
    exact h1.comp_left (g := starRingEnd ℂ) (map_zero _)
  · intro k₁ h₁ k₂ h₂ g
    show starRingEnd ℂ (e (k₁ * g * k₂)⁻¹) = starRingEnd ℂ (e g⁻¹)
    rw [show (k₁ * g * k₂)⁻¹ = k₂⁻¹ * g⁻¹ * k₁⁻¹ by group, hbi _ (K.inv_mem h₂) _ (K.inv_mem h₁)]
  · intro V _ _ ρ B hB v hv w hw
    borelize F
    haveI := isInvInvariant (Measure.haar : Measure (GL ι F)) K hKo hKc
    exact adjoint_of_inv Measure.haar K hKo hKc e hc hbi ρ B hB v w
      (fun k hk => by simpa using hv ⟨k, hk⟩) (fun k hk => by simpa using hw ⟨k, hk⟩)

end GlobalTheory.CompanionTheory.HeckeAdj
