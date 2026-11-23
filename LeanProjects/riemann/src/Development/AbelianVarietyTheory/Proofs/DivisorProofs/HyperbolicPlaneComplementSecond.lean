import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMonoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneUnipotentDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneLeviDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMeasureSemidirectClosedSubgroupStatement
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ConstStageFlag

open GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.GLTwo

theorem conj_mem_unip_of_isLevi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi (W₁ := W₁) H 1 h₁ m → ∀ v ∈ unip σ W H, m * v * m⁻¹ ∈ unip σ W H := by
  intro F E _ _ _ _ _ σ n n₁ W W₁ H h₁ m hm v hv
  open GlobalTheory.ThK.FlagPar in
  have hx : mat m *ᵥ incV F H.x = incV F H.x := by simpa using hm.1
  have hι : mat m * incM F H.ι = incM F H.ι * mat h₁ := hm.2.2
  have hmi : mat m⁻¹ * mat m = 1 := GlobalTheory.ThK.FlagPar.mat_inv_mul m
  have hhi : mat h₁ * mat h₁⁻¹ = 1 := by
    rw [← GlobalTheory.ThK.FlagPar.mat_mul, mul_inv_cancel, GlobalTheory.ThK.FlagPar.mat_one]
  have hxi : mat m⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hmi, Matrix.one_mulVec]
  have hιi : mat m⁻¹ * incM F H.ι = incM F H.ι * mat h₁⁻¹ := by
    calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * incM F H.ι * (mat h₁ * mat h₁⁻¹) := by rw [hhi, Matrix.mul_one]
      _ = mat m⁻¹ * (incM F H.ι * mat h₁) * mat h₁⁻¹ := by simp only [Matrix.mul_assoc]
      _ = mat m⁻¹ * (mat m * incM F H.ι) * mat h₁⁻¹ := by rw [hι]
      _ = incM F H.ι * mat h₁⁻¹ := by rw [← Matrix.mul_assoc (mat m⁻¹), hmi, Matrix.one_mul]
  have key : ∀ u : UA σ W.J, (mat u *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) →
      (mat (m * u * m⁻¹) *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat (m * u * m⁻¹) *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) := by
    rintro u ⟨h1, h2⟩
    have e : mat (m * u * m⁻¹) = mat m * mat u * mat m⁻¹ := rfl
    refine ⟨?_, fun z => ?_⟩
    · rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxi, h1, hx]
    · obtain ⟨a, ha⟩ := h2 (mat h₁⁻¹ *ᵥ z)
      refine ⟨a, ?_⟩
      rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z (mat m⁻¹), hιi,
        ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx, Matrix.mulVec_mulVec, hι,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z, hhi, Matrix.one_mulVec]
  induction hv using Subgroup.closure_induction with
  | mem u hu => exact Subgroup.subset_closure (key u hu)
  | one => simp
  | mul a b _ _ ha hb =>
    have : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
    rw [this]; exact mul_mem ha hb
  | inv a _ ha =>
    have : m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem ha

theorem constTerm_stage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      (∃ (μ : Measure (unip σ W H)) (𝓕 : Set (unip σ W H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H)) 𝓕 μ ∧ μ 𝓕 = 1) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ (f fa : UA σ W.J → ℂ), Continuous f → (∀ γ ∈ ratU σ W.J, ∀ x, f (γ * x) = f x) → IsCT H f fa →
      ∀ c'' : GAd σ (c₀ • W.J.map σ) → ℂ,
      GlobalTheory.StdPar.IsConstAlong σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))) (fun x => f ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀).symm x)) c'' →
      ∀ (μ₁ : Measure (GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S')) (𝓕₁ : Set (GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S')),
        μ₁.IsHaarMeasure → IsFundamentalDomain ((ratPts σ (c₀ • W₁.J.map σ)).subgroupOf (GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S')) 𝓕₁ μ₁ →
        μ₁ 𝓕₁ = 1 → ∀ G : UA σ W.J,
        c'' (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ G) = ∫ u in 𝓕₁, fa (M ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm (u : GAd σ (c₀ • W₁.J.map σ))) * G) ∂μ₁ := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hN₁ hN hdom M hMc hML hMr r Xf Yf hWf
    X' Y' hW' hX0 hY0 hXs S' f fa hfc hfinv hct c'' hc'' μ₁ 𝓕₁ hμ₁ h𝓕₁ h𝓕₁1 G
  have hd₁ : W₁.J.det ≠ 0 := fun h0 => hN₁.2 (by
    have e' : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e', h0, map_zero, mul_zero])
  have hHP : IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, horth, hgram⟩
  obtain ⟨M', hM'c, hM'L, -⟩ := hHP.exists_leviHom hσ hsk hd₁
  have hMM : ∀ h, M h = M' h := fun h => hHP.levi_unique hσ hsk hd₁ (hML h) (hM'L h)
  let N := GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}
  let R := GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r)))
  let H₁ := GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S'
  let s : H₁ →* GAd σ (c₀ • W.J.map σ) :=
    (toGAd hσ W.J hc₀).toMonoidHom.comp (M'.comp ((toGAd hσ W₁.J hc₀).symm.toMonoidHom.comp H₁.subtype))
  have hs : ∀ h : H₁, s h = toGAd hσ W.J hc₀ (M ((toGAd hσ W₁.J hc₀).symm h)) := fun h => by
    show toGAd hσ W.J hc₀ (M' ((toGAd hσ W₁.J hc₀).symm h.1)) = _
    rw [hMM]
  have he := (continuous_toGAd hσ W.J hc₀).1
  have hes := (continuous_toGAd hσ W.J hc₀).2
  have hes₁ := (continuous_toGAd hσ W₁.J hc₀).2
  have hsc : Continuous s := he.comp (hM'c.comp (hes₁.comp continuous_subtype_val))
  have hmemN : ∀ g : UA σ W.J, g ∈ unip σ W H ↔ toGAd hσ W.J hc₀ g ∈ N := fun g =>
    hHP.mem_unip_iff hσ hsk hd₁ hc₀ hW' (Nat.succ_pos r) hX0 g
  have hNc : IsClosed (N : Set (GAd σ (c₀ • W.J.map σ))) := GlobalTheory.StdPar.isClosed_unip {0} hcm hN hW'
  have hNR : N ≤ R := GlobalTheory.T.standardParabolicUnipotent_mono F E σ hcm n _ hN (r + 1) X' Y' hW' _ {0}
    (Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _))
  have hdec := GlobalTheory.T.skew_plane_unipotent_decomposition F E σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hN₁ hN M hMc hML hMr r Xf Yf hWf
    X' Y' hW' hX0 hY0 hXs S'
  have hR : N ⊔ s.range = R := by
    apply le_antisymm
    · refine sup_le hNR ?_
      rintro _ ⟨h, rfl⟩
      rw [hs]
      exact (hdec _).2 ⟨1, one_mem _, h.1, h.2, by rw [map_one, one_mul]⟩
    · intro g hg
      obtain ⟨v, hv, u, hu, rfl⟩ := (hdec g).1 hg
      refine mul_mem (Subgroup.mem_sup_left ((hmemN v).1 hv)) (Subgroup.mem_sup_right ⟨⟨u, hu⟩, ?_⟩)
      rw [hs]
  have hnorm : ∀ x ∈ N, ∀ h, s h * x * (s h)⁻¹ ∈ N := by
    intro x hx h
    have hv : (toGAd hσ W.J hc₀).symm x ∈ unip σ W H := (hmemN _).2 (by rw [MulEquiv.apply_symm_apply]; exact hx)
    have := (hmemN _).1 (conj_mem_unip_of_isLevi W W₁ H _ _ (hML ((toGAd hσ W₁.J hc₀).symm h)) _ hv)
    rw [hs]
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using this
  obtain ⟨p, hpc, hpu, hpr⟩ := GlobalTheory.T.skew_plane_levi_decomposition F E σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hN₁ hN M hMc hML hMr r Xf Yf hWf
    X' Y' hW' hX0 hY0 hXs S'
  have hpp : ∀ (h : H₁) (x : N) (hm : x.1 * s h ∈ R), p ⟨x.1 * s h, hm⟩ = h := fun h x hm =>
    Subtype.ext (hpu _ ((toGAd hσ W.J hc₀).symm x.1) ((hmemN _).2 (by rw [MulEquiv.apply_symm_apply]; exact x.2)) h.1 h.2
      (by show x.1 * s h = _; rw [MulEquiv.apply_symm_apply, hs]))
  have hsrat : ∀ h : H₁, h.1 ∈ ratPts σ (c₀ • W₁.J.map σ) → s h ∈ ratPts σ (c₀ • W.J.map σ) := fun h hh => by
    rw [hs, toGAd_mem_ratPts]
    apply hMr
    rw [← toGAd_mem_ratPts hσ W₁.J hc₀, MulEquiv.apply_symm_apply]
    exact hh
  have hrat : ∀ x ∈ N, ∀ h : H₁, x * s h ∈ ratPts σ (c₀ • W.J.map σ) ↔
      x ∈ ratPts σ (c₀ • W.J.map σ) ∧ h ∈ (ratPts σ (c₀ • W₁.J.map σ)).subgroupOf H₁ := by
    intro x hx h
    rw [Subgroup.mem_subgroupOf]
    have hm : x * s h ∈ R := by
      rw [← hR]; exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right ⟨h, rfl⟩)
    constructor
    · intro hr
      have hh : h.1 ∈ ratPts σ (c₀ • W₁.J.map σ) := by
        have := hpr ⟨x * s h, hm⟩ hr
        rwa [hpp h ⟨x, hx⟩ hm] at this
      refine ⟨?_, hh⟩
      have := mul_mem hr (inv_mem (hsrat h hh))
      rwa [mul_inv_cancel_right] at this
    · rintro ⟨hx', hh⟩
      exact mul_mem hx' (hsrat h hh)
  haveI : Countable (ratPts σ (c₀ • W.J.map σ)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ _
  haveI : Countable (ratPts σ (c₀ • W₁.J.map σ)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ _
  haveI : Countable ((ratPts σ (c₀ • W₁.J.map σ)).subgroupOf H₁) := GlobalTheory.SemiHaar.countable_subgroupOf _ _
  haveI : LocallyCompactSpace H₁ := (GlobalTheory.StdPar.isClosed_unip S' hcm hN₁ hWf).locallyCompactSpace
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hcm n₁ _ hN₁ r Xf Yf hWf S'

  obtain ⟨μH, 𝓕H, hμH, h𝓕H, h𝓕H1⟩ := hdom
  let e' : unip σ W H ≃* N :=
    { toFun := fun u => ⟨toGAd hσ W.J hc₀ u.1, (hmemN u.1).1 u.2⟩
      invFun := fun v => ⟨(toGAd hσ W.J hc₀).symm v.1, (hmemN _).2 (by rw [MulEquiv.apply_symm_apply]; exact v.2)⟩
      left_inv := fun u => Subtype.ext ((toGAd hσ W.J hc₀).symm_apply_apply u.1)
      right_inv := fun v => Subtype.ext ((toGAd hσ W.J hc₀).apply_symm_apply v.1)
      map_mul' := fun u v => Subtype.ext (map_mul (toGAd hσ W.J hc₀) u.1 v.1) }
  have he' : Continuous e' := (he.comp continuous_subtype_val).subtype_mk _
  have hes' : Continuous e'.symm := (hes.comp continuous_subtype_val).subtype_mk _
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI := (GlobalTheory.UnipCT.topFacts (F := F) σ W.J).1
  let t : unip σ W H ≃ₜ N := ⟨e'.toEquiv, he', hes'⟩
  let me := t.toMeasurableEquiv
  let ν : Measure N := μH.map me
  have hmp : MeasurePreserving me μH ν := ⟨me.measurable, rfl⟩
  have hmps : MeasurePreserving me.symm ν μH := hmp.symm
  haveI hν : ν.IsHaarMeasure := MulEquiv.isHaarMeasure_map μH e' he' hes'
  have hmemP : ∀ δ : (ratU σ W.J).subgroupOf (unip σ W H), e' δ.1 ∈ (ratPts σ (c₀ • W.J.map σ)).subgroupOf N := fun δ =>
    Subgroup.mem_subgroupOf.2 ((toGAd_mem_ratPts hσ W.J hc₀ δ.1.1).2 (Subgroup.mem_subgroupOf.1 δ.2))
  have hmemU : ∀ γ : (ratPts σ (c₀ • W.J.map σ)).subgroupOf N, e'.symm γ.1 ∈ (ratU σ W.J).subgroupOf (unip σ W H) :=
    fun γ => by
      refine Subgroup.mem_subgroupOf.2 ((toGAd_mem_ratPts hσ W.J hc₀ _).1 ?_)
      show toGAd hσ W.J hc₀ ((toGAd hσ W.J hc₀).symm γ.1.1) ∈ _
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_subgroupOf.1 γ.2
  let fm : (ratU σ W.J).subgroupOf (unip σ W H) → (ratPts σ (c₀ • W.J.map σ)).subgroupOf N :=
    fun δ => ⟨e' δ.1, hmemP δ⟩
  have hfb : Function.Bijective fm :=
    ⟨fun a b hab => Subtype.ext (e'.injective (congrArg Subtype.val hab)),
      fun γ => ⟨⟨e'.symm γ.1, hmemU γ⟩, Subtype.ext (e'.apply_symm_apply γ.1)⟩⟩
  have hfd : IsFundamentalDomain ((ratPts σ (c₀ • W.J.map σ)).subgroupOf N) (me.symm ⁻¹' 𝓕H) ν :=
    h𝓕H.preimage_of_equiv hmps.quasiMeasurePreserving hfb fun δ x => by
      show e'.symm (e' δ.1 * x) = δ.1 * e'.symm x
      rw [map_mul, e'.symm_apply_apply]
  have hmass : ν (me.symm ⁻¹' 𝓕H) = 1 := by
    rw [show ν = μH.map me from rfl, me.map_apply, show me ⁻¹' (me.symm ⁻¹' 𝓕H) = 𝓕H from by ext; simp, h𝓕H1]
  haveI := hμ₁
  obtain ⟨κ, 𝓡, hκ, h𝓡, h𝓡1, hint⟩ := GlobalTheory.T.quotient_measure_semidirect_closed_subgroup (GAd σ (c₀ • W.J.map σ)) H₁ N R s hNc hsc hnorm hR ⟨p, hpc, hpp⟩
    (ratPts σ (c₀ • W.J.map σ)) ((ratPts σ (c₀ • W₁.J.map σ)).subgroupOf H₁) hrat K hK hcov μ₁ 𝓕₁ h𝓕₁ h𝓕₁1
    ν (me.symm ⁻¹' 𝓕H) hfd hmass
  let φ : GAd σ (c₀ • W.J.map σ) → ℂ := fun x => f ((toGAd hσ W.J hc₀).symm (x * toGAd hσ W.J hc₀ G))
  have hφc : Continuous φ := hfc.comp (hes.comp (continuous_id.mul continuous_const))
  have hφb : ∃ C, ∀ x ∈ R, ‖φ x‖ ≤ C := by
    obtain ⟨K'', hK'', hcov''⟩ := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hcm n _ hN (r + 1) X' Y' hW' (insert 0 (S'.map (Fin.succEmb r)))
    obtain ⟨C, hC⟩ := hK''.exists_bound_of_continuousOn ((hφc.comp continuous_subtype_val).continuousOn)
    refine ⟨C, fun x hx => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hcov'' ⟨x, hx⟩
    have hγr : (toGAd hσ W.J hc₀).symm γ.1 ∈ ratU σ W.J := by
      rw [← toGAd_mem_ratPts hσ W.J hc₀, MulEquiv.apply_symm_apply]; exact Subgroup.mem_subgroupOf.1 hγ
    have h2 := hC _ hγK
    have h3 : φ ((γ * ⟨x, hx⟩ : R) : GAd σ (c₀ • W.J.map σ)) = φ x := by
      simp only [φ, Subgroup.coe_mul, mul_assoc, map_mul, hfinv _ hγr]
    rw [← h3]; exact h2
  refine (hc'' κ 𝓡 hκ h𝓡 h𝓡1 (toGAd hσ W.J hc₀ G)).trans ((hint φ hφc hφb).trans ?_)
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  calc ∫ m in me.symm ⁻¹' 𝓕H, φ (m.1 * s h) ∂ν
      = ∫ m in me.symm ⁻¹' 𝓕H, (fun y => φ ((me y).1 * s h)) (me.symm m) ∂ν := by simp
    _ = ∫ y in 𝓕H, φ ((me y).1 * s h) ∂μH := hmps.setIntegral_preimage_emb me.symm.measurableEmbedding (fun y => φ ((me y).1 * s h)) 𝓕H
    _ = ∫ y in 𝓕H, f (y.1 * (M ((toGAd hσ W₁.J hc₀).symm h) * G)) ∂μH := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show f ((toGAd hσ W.J hc₀).symm (toGAd hσ W.J hc₀ y.1 * s h * toGAd hσ W.J hc₀ G)) = _
        rw [hs, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply, mul_assoc]
    _ = fa (M ((toGAd hσ W₁.J hc₀).symm h) * G) := (hct μH 𝓕H hμH h𝓕H h𝓕H1 _).symm

end GlobalTheory.ConstStageFlag
