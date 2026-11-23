import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentRadicalEqLeviMulUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneUnipotentDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneLeviDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMeasureSemidirectClosedSubgroup
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.CuspTransfer

open GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.GLTwo

theorem levi_one_conj_mem_unip : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi (W₁ := W₁) H 1 h₁ m → ∀ v ∈ unip σ W H, m * v * m⁻¹ ∈ unip σ W H := by
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

theorem setIntegral_eq_zero_of_semi {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (N R : Subgroup G) (s : H →* G) (hN : IsClosed (N : Set G)) (hRc : IsClosed (R : Set G)) (hs : Continuous s)
    (hnorm : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) (hR : N ⊔ s.range = R) (hRdec : ∀ z ∈ R, ∃ x ∈ N, ∃ h : H, z = x * s h)
    (hp : ∃ p : R → H, Continuous p ∧ ∀ (h : H) (n : N) (hm : n.1 * s h ∈ R), p ⟨n.1 * s h, hm⟩ = h)
    (Γ : Subgroup G) [Countable Γ] (Λ : Subgroup H) [Countable Λ] (hrat : ∀ n ∈ N, ∀ h, n * s h ∈ Γ ↔ n ∈ Γ ∧ h ∈ Λ)
    (K : Set H) (hK : IsCompact K) (hcov : ∀ h, ∃ δ ∈ Λ, δ * h ∈ K)
    (μ₁ : Measure H) [μ₁.IsHaarMeasure] (𝓕₁ : Set H) (h𝓕₁ : IsFundamentalDomain Λ 𝓕₁ μ₁) (h𝓕₁1 : μ₁ 𝓕₁ = 1)
    (ν : Measure N) [ν.IsHaarMeasure] (𝓐 : Set N) (h𝓐 : IsFundamentalDomain (Γ.subgroupOf N) 𝓐 ν) (h𝓐1 : ν 𝓐 = 1)
    (φ : G → ℂ) (hφc : Continuous φ) {d : ℕ} (f : Fin d → H → ℂ) (c : ℂ) (b : Fin d → ℂ) (hfc : ∀ i, Continuous (f i))
    (hf : ∀ i, ∀ δ ∈ Λ, ∀ h, f i (δ * h) = f i h) (hf0 : ∀ i, ∫ h in 𝓕₁, f i h ∂μ₁ = 0)
    (hval : ∀ x ∈ N, ∀ h, φ (x * s h) = c * ∑ i, f i h * b i)
    (μ : Measure R) [μ.IsHaarMeasure] (𝓕 : Set R) (h𝓕 : IsFundamentalDomain (Γ.subgroupOf R) 𝓕 μ) :
    ∫ x in 𝓕, φ x ∂μ = 0 := by
  obtain ⟨κ, 𝓡, hκ, h𝓡, -, hint⟩ := GlobalTheory.semiHaar_exists_fd_setIntegral G H N R s hN hs hnorm hR hp Γ Λ hrat K hK hcov
    μ₁ 𝓕₁ h𝓕₁ h𝓕₁1 ν 𝓐 h𝓐 h𝓐1
  have hφinv : ∀ γ ∈ R, γ ∈ Γ → ∀ z ∈ R, φ (γ * z) = φ z := by
    intro γ hγ hγr z hz
    obtain ⟨x, hx, δ, rfl⟩ := hRdec γ hγ
    obtain ⟨x', hx', h, rfl⟩ := hRdec z hz
    have e : x * s δ * (x' * s h) = x * (s δ * x' * (s δ)⁻¹) * s (δ * h) := by rw [map_mul]; group
    rw [e, hval _ (mul_mem hx (hnorm x' hx' δ)), hval _ hx']
    simp only [hf _ δ ((hrat x hx δ).1 hγr).2]
  have hb : ∀ g : H → ℂ, Continuous g → (∀ δ ∈ Λ, ∀ h, g (δ * h) = g h) → ∃ C, ∀ h, ‖g h‖ ≤ C := fun g hg hg' => by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
    refine ⟨C, fun h => ?_⟩
    obtain ⟨δ, hδ, hδK⟩ := hcov h
    rw [← hg' δ hδ h]
    exact hC _ hδK
  have hφb : ∃ C, ∀ x ∈ R, ‖φ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hb (fun h => c * ∑ i, f i h * b i) (by fun_prop) fun δ hδ h => by simp only [hf _ δ hδ]
    refine ⟨C, fun z hz => ?_⟩
    obtain ⟨x, hx, h, rfl⟩ := hRdec z hz
    rw [hval x hx]
    exact hC h
  have hψi : ∀ i, IntegrableOn (f i) 𝓕₁ μ₁ := by
    intro i
    obtain ⟨C, hC⟩ := hb (f i) (hfc i) (hf i)
    exact Measure.integrableOn_of_bounded (M := C) (by rw [h𝓕₁1]; exact ENNReal.one_ne_top) (hfc i).aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have hzero : ∫ x in 𝓡, φ x ∂κ = 0 := by
    rw [hint φ hφc hφb]
    have e : ∀ h : H, ∫ x in 𝓐, φ (x.1 * s h) ∂ν = c * ∑ i, f i h * b i := fun h => by
      have : (fun x : N => φ (x.1 * s h)) = fun _ => c * ∑ i, f i h * b i := funext fun x => hval x.1 x.2 h
      rw [this]
      simp [Measure.real, h𝓐1]
    simp only [e]
    rw [integral_const_mul, integral_finset_sum _ fun i _ => (hψi i).mul_const _, Finset.sum_eq_zero, mul_zero]
    intro i _
    rw [integral_mul_const, hf0, zero_mul]
  haveI : LocallyCompactSpace R := hRc.locallyCompactSpace
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (Γ.subgroupOf R) := GlobalTheory.SemiHaar.countable_subgroupOf _ _
  have hc := Measure.isMulLeftInvariant_eq_smul μ κ
  have h𝓡' : IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μ :=
    h𝓡.mono (by rw [hc]; exact Measure.smul_absolutelyContinuous)
  rw [h𝓕.setIntegral_eq h𝓡' (f := fun x : R => φ x) fun γ x =>
    hφinv γ.1.1 γ.1.2 (Subgroup.mem_subgroupOf.1 γ.2) x.1 x.2, hc, Measure.restrict_smul, integral_smul_nnreal_measure,
    hzero, smul_zero]

theorem exists_eq_insert_succ {r : ℕ} {S' : Finset (Fin r)} {S : Finset (Fin (r + 1))}
    (h : insert 0 (S'.map (Fin.succEmb r)) ⊂ S) : ∃ T : Finset (Fin r), S' ⊂ T ∧ S = insert 0 (T.map (Fin.succEmb r)) := by
  have h0 : (0 : Fin (r + 1)) ∈ S := h.1 (Finset.mem_insert_self _ _)
  have e : S = insert 0 ((Finset.univ.filter fun i : Fin r => i.succ ∈ S).map (Fin.succEmb r)) := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [h0]
    · simp [Fin.succ_ne_zero]
  refine ⟨_, ?_, e⟩
  refine Finset.ssubset_iff_subset_ne.2 ⟨fun i hi => ?_, fun h' => h.ne ?_⟩
  · simpa using h.1 (Finset.mem_insert_of_mem (Finset.mem_map_of_mem (Fin.succEmb r) hi))
  · rw [h']; exact e.symm

theorem isConstAlong_zero_of_isInd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ χ : Chr F E, (∀ t : Eˣ, χ (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) = 1) → Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K₁ →
      ∀ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K' →
      ∀ (Kc : Set (GAd σ (c₀ • W.J.map σ))) (d : ℕ) (ψs : Fin d → GAd σ (c₀ • W₁.J.map σ) → ℂ) (a : Fin d → GAd σ (c₀ • W.J.map σ) → ℂ) (Ψ : GAd σ (c₀ • W.J.map σ) → ℂ),
      GlobalTheory.ThK.CuspTransfer.IsInd hσ W W₁ H hc₀ X' M χ Kc ψs a Ψ →
      (∀ i, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ (ψs i)) →
      (IsCompact Kc ∧ (1 : GAd σ (c₀ • W.J.map σ)) ∈ Kc ∧ ∀ k ∈ Kc, ∀ k' ∈ K', k * k' ∈ Kc) → Continuous Ψ → ∀ S : Finset (Fin (r + 1)), (insert 0 (S'.map (Fin.succEmb r))) ⊂ S → GlobalTheory.StdPar.IsConstAlong σ (c₀ • W.J.map σ) X' S Ψ 0 := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hN₁ hN M hMc hML hMr r Xf Yf hWf
    X' Y' hW' hX0 hY0 hXs S' χ _ _ K₁ _ K' _ Kc d ψs a Ψ hind hcusp _ hΨc S hS
  obtain ⟨T, hT, rfl⟩ := exists_eq_insert_succ hS
  have hd₁ : W₁.J.det ≠ 0 := fun h0 => hN₁.2 (by
    have e' : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e', h0, map_zero, mul_zero])
  have hHP : IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, horth, hgram⟩
  obtain ⟨M', hM'c, hM'L, -⟩ := hHP.exists_leviHom hσ hsk hd₁
  have hMM : ∀ h, M h = M' h := fun h => hHP.levi_unique hσ hsk hd₁ (hML h) (hM'L h)
  let N := GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}
  let R := GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (T.map (Fin.succEmb r)))
  let H₁ := GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf T
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
  have hNR : N ≤ R := GlobalTheory.StdPar.unip_mono_of_subset F E σ hcm n _ hN (r + 1) X' Y' hW' _ {0}
    (Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _))
  have hdec := GlobalTheory.T.skew_plane_unipotent_decomposition F E σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hN₁ hN M hMc hML hMr r Xf Yf hWf
    X' Y' hW' hX0 hY0 hXs T
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
    have := (hmemN _).1 (levi_one_conj_mem_unip W W₁ H _ _ (hML ((toGAd hσ W₁.J hc₀).symm h)) _ hv)
    rw [hs]
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using this
  obtain ⟨p, hpc, hpu, hpr⟩ := GlobalTheory.T.skew_plane_levi_decomposition F E σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hN₁ hN M hMc hML hMr r Xf Yf hWf
    X' Y' hW' hX0 hY0 hXs T
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
  haveI : LocallyCompactSpace H₁ := (GlobalTheory.StdPar.isClosed_unip T hcm hN₁ hWf).locallyCompactSpace
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hcm n₁ _ hN₁ r Xf Yf hWf T
  obtain ⟨μ₁, 𝓕₁, hμ₁, h𝓕₁, h𝓕₁1⟩ := GlobalTheory.T.unipotent_radical_fundamental_domain F E σ hcm n₁ _ hN₁ r Xf Yf hWf T
  obtain ⟨ν, 𝓐, hν, h𝓐, h𝓐1⟩ := GlobalTheory.T.unipotent_radical_fundamental_domain F E σ hcm n _ hN (r + 1) X' Y' hW' {0}
  intro μ 𝓕 hμ h𝓕 _ g
  obtain ⟨u, hu, t, m, y, k, hk, hm, rfl⟩ := hind.1 g
  obtain ⟨hMmul, hMcomm⟩ := GlobalTheory.LeviPlaneHom.levi_section_hom F E σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀
    hN₁ hN M hML

  have hval : ∀ x ∈ N, ∀ h : H₁, Ψ (x * s h * (u * toGAd hσ W.J hc₀ m * emb hσ W W₁ hc₀ M y * k)) =
      (χ t : ℂ) * ∑ i, ψs i (h.1 * y) * a i k := by
    intro x hx h
    rw [← hind.2 (x * (s h * u * (s h)⁻¹)) (mul_mem hx (hnorm u hu h)) t m (h.1 * y) k hk hm]
    congr 1
    have e1 : emb hσ W W₁ hc₀ M (h.1 * y) = s h * emb hσ W W₁ hc₀ M y := by
      rw [hs]; unfold emb; rw [map_mul, hMmul, map_mul]
    have e2 : toGAd hσ W.J hc₀ m * s h = s h * toGAd hσ W.J hc₀ m := by
      rw [hs, ← map_mul, ← map_mul, hMcomm t m hm]
    rw [e1]
    calc x * s h * (u * toGAd hσ W.J hc₀ m * emb hσ W W₁ hc₀ M y * k)
        = x * (s h * u * (s h)⁻¹) * (s h * toGAd hσ W.J hc₀ m) * emb hσ W W₁ hc₀ M y * k := by group
      _ = _ := by rw [← e2]; group

  have hψ : ∀ i, ∀ δ : H₁, δ.1 ∈ ratPts σ (c₀ • W₁.J.map σ) → ∀ z, ψs i (δ.1 * z) = ψs i z := by
    intro i δ hδ z
    obtain ⟨m', hm', hm'', v, hv, e⟩ := GlobalTheory.T.rational_unipotentRadical_eq_levi_mul_unipotent F E σ hcm n₁ _ hN₁ r Xf Yf hWf S' T hT.1 δ.1 hδ δ.2
    rw [e, mul_assoc, (hcusp i).1.leftM m' hm' hm'', (hcusp i).1.leftN v hv]
  have hRdec : ∀ z ∈ R, ∃ x ∈ N, ∃ h : H₁, z = x * s h := fun z hz => by
    obtain ⟨v, hv, w, hw, rfl⟩ := (hdec z).1 hz
    exact ⟨_, (hmemN v).1 hv, ⟨w, hw⟩, by rw [hs]⟩
  exact (setIntegral_eq_zero_of_semi N R s hNc (GlobalTheory.StdPar.isClosed_unip _ hcm hN hW') hsc hnorm hR hRdec ⟨p, hpc, hpp⟩
    (ratPts σ (c₀ • W.J.map σ)) ((ratPts σ (c₀ • W₁.J.map σ)).subgroupOf H₁) hrat K hK hcov μ₁ 𝓕₁ h𝓕₁ h𝓕₁1 ν 𝓐 h𝓐 h𝓐1
    (fun x => Ψ (x * (u * toGAd hσ W.J hc₀ m * emb hσ W W₁ hc₀ M y * k))) (hΨc.comp (continuous_id.mul continuous_const))
    (fun i h => ψs i (h.1 * y)) (χ t : ℂ) (fun i => a i k)
    (fun i => (hcusp i).1.cont.comp (continuous_subtype_val.mul continuous_const))
    (fun i δ hδ h => (congrArg (ψs i) (mul_assoc δ.1 h.1 y)).trans (hψ i δ (Subgroup.mem_subgroupOf.1 hδ) _))
    (fun i => ((hcusp i).2 T hT μ₁ 𝓕₁ hμ₁ h𝓕₁ h𝓕₁1 y).symm) hval μ 𝓕 h𝓕).symm

end GlobalTheory.ThK.CuspTransfer

end
