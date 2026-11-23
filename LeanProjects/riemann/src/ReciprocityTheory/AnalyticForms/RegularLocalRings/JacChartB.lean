import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne

namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt

open MvPolynomial IsLocalRing

noncomputable section

section

variable {n : ℕ} (p : Fin n → ℂ) (K : Ideal (MvPolynomial (Fin n) ℂ)) [IsLocalRing (locR K p)]

theorem lin_mem_max (i : Fin n) : psi p K (X i - C (p i)) ∈ maximalIdeal (locR K p) :=
  (psi_mem_max_iff (K := K) (p := p) (le_ptIdeal_of_nontrivial (K := K) (p := p)) _).mpr
  (by rw [ptI, RingHom.mem_ker]; simp)

def Phi : (Fin n → ℂ) →ₗ[ℂ] CotangentSpace (locR K p) where
  toFun c := ∑ i, c i • (maximalIdeal (locR K p)).toCotangent ⟨_, lin_mem_max p K i⟩
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

theorem algebraMap_eq_psi (c : ℂ) : algebraMap ℂ (locR K p) c = psi p K (C c) := by
  rfl

theorem toCot_psi {a : MvPolynomial (Fin n) ℂ} (ha : a ∈ ptI p)
    (hm : psi p K a ∈ maximalIdeal (locR K p)) :
    (maximalIdeal (locR K p)).toCotangent ⟨psi p K a, hm⟩ = Phi p K (gradP p a) := by
  have hK : K ≤ ptI p := le_ptIdeal_of_nontrivial (K := K) (p := p)
  have ha0 : eval p a = 0 := by rw [ptI, RingHom.mem_ker] at ha; exact ha
  have ht := taylor p a
  rw [ha0, C_0, sub_zero] at ht
  have hsq := psi_mem_sq (K := K) (p := p) hK ht
  have hmem : ∀ i, psi p K (C (gradP p a i)) * psi p K (X i - C (p i)) ∈ maximalIdeal (locR K p) :=
    fun i => (maximalIdeal (locR K p)).mul_mem_left _ (lin_mem_max p K i)
  have e : Phi p K (gradP p a) = (maximalIdeal (locR K p)).toCotangent
      ⟨∑ i, psi p K (C (gradP p a i)) * psi p K (X i - C (p i)),
        (maximalIdeal (locR K p)).sum_mem fun i _ => hmem i⟩ := by
    have e2 : (⟨∑ i, psi p K (C (gradP p a i)) * psi p K (X i - C (p i)),
        (maximalIdeal (locR K p)).sum_mem fun i _ => hmem i⟩ : maximalIdeal (locR K p)) =
        ∑ i, psi p K (C (gradP p a i)) • (⟨psi p K (X i - C (p i)), lin_mem_max p K i⟩ :
          maximalIdeal (locR K p)) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, smul_eq_mul]
    rw [e2, map_sum]
    simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← algebraMap_eq_psi, algebraMap_smul]
  rw [e, Ideal.toCotangent_eq]
  simpa [map_sub, map_sum, map_mul] using hsq

theorem ker_Phi : LinearMap.ker (Phi p K) = jacS K p := by
  have hK : K ≤ ptI p := le_ptIdeal_of_nontrivial (K := K) (p := p)
  apply le_antisymm
  · intro c hc
    rw [LinearMap.mem_ker] at hc
    set l : MvPolynomial (Fin n) ℂ := ∑ i, C (c i) * (X i - C (p i)) with hl
    have hl0 : eval p l = 0 := by simp [hl]
    have hlI : l ∈ ptI p := by rw [ptI, RingHom.mem_ker]; exact hl0
    have hgl : gradP p l = c := by
      rw [hl, grad_sum]
      ext j
      simp [grad_mul, grad_C, grad_lin, Pi.single_apply, Finset.sum_apply]
    have hpl : psi p K l ∈ maximalIdeal (locR K p) :=
      (psi_mem_max_iff (K := K) (p := p) hK l).mpr hlI
    have h0 : (maximalIdeal (locR K p)).toCotangent ⟨psi p K l, hpl⟩ = 0 := by
      rw [toCot_psi p K hlI hpl, hgl, hc]
    rw [Ideal.toCotangent_eq_zero] at h0
    obtain ⟨s, hs, hsl⟩ := exists_of_psi_mem_sq (K := K) (p := p) hK h0
    obtain ⟨q, hq, k, hk, hqk⟩ := Submodule.mem_sup.mp hsl
    have hg : gradP p (s * l) = eval p s • c := by
      rw [grad_mul, hgl, hl0, zero_smul, add_zero]
    have hg2 : gradP p (s * l) = gradP p k := by
      rw [← hqk, grad_add, grad_eq_zero_of_mem_sq p hq, zero_add]
    have hs0 : eval p s ≠ 0 := fun h => hs (by rw [ptI, RingHom.mem_ker]; exact h)
    have hmemk : gradP p k ∈ jacS K p := Submodule.subset_span ⟨k, hk, rfl⟩
    have hc' : c = (eval p s)⁻¹ • gradP p k := by
      rw [← hg2, hg, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [hc']
    exact Submodule.smul_mem _ _ hmemk
  · rw [jacS, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hfI := hK hf
    have hpf : psi p K f ∈ maximalIdeal (locR K p) := (psi_mem_max_iff (K := K) (p := p) hK f).mpr hfI
    rw [← toCot_psi p K hfI hpf, Ideal.toCotangent_eq_zero]
    have h0 : psi p K f = 0 := by
      simp only [psi, RingHom.comp_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hf)
    show psi p K f ∈ maximalIdeal (locR K p) ^ 2
    rw [h0]
    exact zero_mem _

theorem Phi_surjective : Function.Surjective (Phi p K) := by
  have hK : K ≤ ptI p := le_ptIdeal_of_nontrivial (K := K) (p := p)
  intro v
  obtain ⟨⟨x, hx⟩, rfl⟩ := (maximalIdeal (locR K p)).toCotangent_surjective v
  obtain ⟨a, s, ha, hs, hxs⟩ := exists_of_mem_max (K := K) (p := p) hK hx
  have hsu : IsUnit (psi p K s) := by
    by_contra h
    exact hs ((psi_mem_max_iff (K := K) (p := p) hK s).mp ((IsLocalRing.mem_maximalIdeal _).mpr h))
  obtain ⟨u, hu⟩ := hsu
  have hpa : psi p K a ∈ maximalIdeal (locR K p) := (psi_mem_max_iff (K := K) (p := p) hK a).mpr ha
  have hxe : x = (↑u⁻¹ : locR K p) * psi p K a := by
    rw [← hxs, ← hu, mul_comm x, ← mul_assoc, Units.inv_mul, one_mul]
  have hr : (↑u⁻¹ : locR K p) - algebraMap ℂ (locR K p) (evRing K hK (↑u⁻¹ : locR K p)) ∈
      maximalIdeal (locR K p) := by
    rw [← ker_evRing (K := K) (p := p) hK, RingHom.mem_ker, map_sub, algebraMap_eq_psi, evRing_psi,
      eval_C, sub_self]
  refine ⟨(evRing K hK (↑u⁻¹ : locR K p)) • gradP p a, ?_⟩
  rw [map_smul, ← toCot_psi p K ha hpa, ← algebraMap_smul (locR K p), ← map_smul, Ideal.toCotangent_eq]
  simp only [SetLike.val_smul, smul_eq_mul]
  rw [hxe, ← sub_mul, pow_two]
  exact Ideal.mul_mem_mul (by rw [← neg_sub]; exact neg_mem hr) hpa

theorem finrank_cot_complex :
    Module.finrank ℂ (CotangentSpace (locR K p)) + Module.finrank ℂ (jacS K p) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (Phi p K)
  rw [LinearMap.range_eq_top.mpr (Phi_surjective p K), finrank_top, ker_Phi, Module.finrank_fin_fun] at h
  exact h

instance : IsScalarTower ℂ (ResidueField (locR K p)) (CotangentSpace (locR K p)) := by
  refine IsScalarTower.of_algebraMap_smul fun c y => ?_
  rw [IsScalarTower.algebraMap_apply ℂ (locR K p) (ResidueField (locR K p)),
    algebraMap_smul, algebraMap_smul]

theorem finrank_residueField : Module.finrank ℂ (ResidueField (locR K p)) = 1 := by
  have hK : K ≤ ptI p := le_ptIdeal_of_nontrivial (K := K) (p := p)
  rw [finrank_eq_one_iff_of_nonzero' (1 : ResidueField (locR K p)) one_ne_zero]
  intro w
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective w
  refine ⟨evRing K hK x, ?_⟩
  rw [Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply ℂ (locR K p) (ResidueField (locR K p)),
    IsLocalRing.ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ker_evRing (K := K) (p := p) hK, RingHom.mem_ker, map_sub, algebraMap_eq_psi, evRing_psi, eval_C,
    sub_self]

theorem finrank_cot_eq :
    Module.finrank (ResidueField (locR K p)) (CotangentSpace (locR K p))
      + Module.finrank ℂ (jacS K p) = n := by
  have h := finrank_cot_complex p K
  haveI : Module.Free ℂ (ResidueField (locR K p)) := Module.Free.of_divisionRing ℂ _
  haveI : Module.Free (ResidueField (locR K p)) (CotangentSpace (locR K p)) :=
    Module.Free.of_divisionRing (ResidueField (locR K p)) _
  rw [← Module.finrank_mul_finrank ℂ (ResidueField (locR K p)) (CotangentSpace (locR K p)),
    finrank_residueField, one_mul] at h
  exact h

end

variable {n : ℕ}

theorem isNoetherianRing_locPt (p : Fin n → ℂ) : IsNoetherianRing (localization₂ p) :=
  IsLocalization.isNoetherianRing (ptI p).primeCompl _ inferInstance

theorem locRing_isLocalRing_isNoetherian' (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) : IsLocalRing (locR K p) ∧ IsNoetherianRing (locR K p) := by
  haveI := isNoetherianRing_locPt p
  have hK : K ≤ ptI p := fun h hh => by rw [ptI, RingHom.mem_ker]; exact hp h hh
  have hle : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (localization₂ p)) K ≤ IsLocalRing.maximalIdeal (localization₂ p) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hK
  have hne : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (localization₂ p)) K ≠ ⊤ :=
    fun h => (IsLocalRing.maximalIdeal.isMaximal (localization₂ p)).ne_top (top_le_iff.mp (h ▸ hle))
  haveI : Nontrivial (locR K p) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, inferInstance⟩

theorem exists_jacobian_cut' (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (e : ℕ)
    [IsRegularLocalRing (locR K p)] (he : ringKrullDim (locR K p) = e) :
    e ≤ n ∧ ∃ F : Fin (n - e) → MvPolynomial (Fin n) ℂ, (∀ i, F i ∈ K) ∧
      LinearIndependent ℂ (fun i => gradP p (F i)) ∧
      ∃ h : MvPolynomial (Fin n) ℂ, eval p h ≠ 0 ∧ ∀ g ∈ K, h * g ∈ Ideal.span (Set.range F) := by
  have hK := le_ptIdeal_of_nontrivial (p := p) K
  have hcot : Module.finrank (ResidueField (locR K p)) (CotangentSpace (locR K p)) = e := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace (locR K p)).mp inferInstance
    rw [he] at this
    exact_mod_cast this
  have h2 := finrank_cot_eq p K
  rw [hcot] at h2
  refine ⟨by omega, ?_⟩

  obtain ⟨κ, a, -, hspan, hli⟩ :=
    exists_linearIndependent' ℂ (fun k : K => gradP p (k : MvPolynomial (Fin n) ℂ))
  have : Finite κ := hli.finite
  have : Fintype κ := Fintype.ofFinite κ
  have hj : Submodule.span ℂ (Set.range fun k : K => gradP p (k : MvPolynomial (Fin n) ℂ)) =
      jacS K p := by
    rw [jacS]; congr 1; ext v; simp
  have hcard : Fintype.card κ = n - e := by
    have := finrank_span_eq_card hli
    rw [hspan, hj] at this
    omega
  let σ : Fin (n - e) ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let F : Fin (n - e) → MvPolynomial (Fin n) ℂ := fun i => (a (σ i) : MvPolynomial (Fin n) ℂ)
  have hFK : ∀ i, F i ∈ K := fun i => (a (σ i)).2
  have hFli : LinearIndependent ℂ (fun i => gradP p (F i)) := hli.comp σ σ.injective
  refine ⟨F, hFK, hFli, ?_⟩

  set J : Ideal (MvPolynomial (Fin n) ℂ) := Ideal.span (Set.range F) with hJ
  have hJK : J ≤ K := Ideal.span_le.mpr (Set.range_subset_iff.mpr hFK)
  obtain ⟨hJloc, hJnoeth⟩ := locRing_isLocalRing_isNoetherian' J p
    (fun h hh => mem_ptIdeal.mp (hK (hJK hh)))
  have hJcot := finrank_cot_eq p J
  have hJrank : n - e ≤ Module.finrank ℂ (jacS J p) := by
    let v : Fin (n - e) → jacS J p := fun i =>
      ⟨gradP p (F i), Submodule.subset_span ⟨F i, Ideal.subset_span ⟨i, rfl⟩, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp (jacS J p).subtype hFli
    simpa using hv.fintype_card_le_finrank
  have hmapJK : Ideal.map (algebraMap _ (localization₂ p)) J ≤ Ideal.map (algebraMap _ (localization₂ p)) K :=
    Ideal.map_mono hJK
  have hdimKJ : ringKrullDim (locR K p) ≤ ringKrullDim (locR J p) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hmapJK)
  have hdimJ : ringKrullDim (locR J p) ≤
      Module.finrank (ResidueField (locR J p)) (CotangentSpace (locR J p)) := by
    rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact ringKrullDim_le_spanFinrank_maximalIdeal _
  have hcotJ : Module.finrank (ResidueField (locR J p)) (CotangentSpace (locR J p)) ≤ e := by
    omega
  have hDJ : ringKrullDim (locR J p) = e := by
    apply le_antisymm
    · exact hdimJ.trans (by exact_mod_cast hcotJ)
    · rw [← he]; exact hdimKJ
  have hreg : IsRegularLocalRing (locR J p) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hDJ]
    exact_mod_cast hcotJ
  have hdom : IsDomain (locR J p) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _

  have hmapEq : Ideal.map (algebraMap _ (localization₂ p)) K = Ideal.map (algebraMap _ (localization₂ p)) J := by
    by_contra hne
    set 𝔞 : Ideal (locR J p) :=
      (Ideal.map (algebraMap _ (localization₂ p)) K).map (Ideal.Quotient.mk _) with h𝔞
    have h𝔞ne : 𝔞 ≠ ⊥ := by
      intro hbot
      rw [h𝔞, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hbot
      exact hne (le_antisymm hbot hmapJK)
    obtain ⟨x, hx𝔞, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞ne
    have hxnz : x ∈ nonZeroDivisors (locR J p) := mem_nonZeroDivisors_of_ne_zero hx0
    have hd1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hxnz
    have hle𝔞 : Ideal.span {x} ≤ 𝔞 := (Ideal.span_singleton_le_iff_mem _).mpr hx𝔞
    have hd2 : ringKrullDim (locR J p ⧸ 𝔞) ≤ ringKrullDim (locR J p ⧸ Ideal.span {x}) :=
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle𝔞)
    have hd3 : ringKrullDim (locR J p ⧸ 𝔞) = ringKrullDim (locR K p) :=
      ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hmapJK)
    rw [hd3, he] at hd2
    rw [hDJ] at hd1
    have : ((e : WithBot ℕ∞) + 1 ≤ e) := (add_le_add hd2 le_rfl).trans hd1
    have h' : (((e + 1 : ℕ) : WithBot ℕ∞) ≤ ((e : ℕ) : WithBot ℕ∞)) := by exact_mod_cast this
    have := WithBot.coe_le_coe.mp h'
    norm_cast at this
    omega

  have hloc : ∀ g ∈ K, ∃ s, s ∉ ptI p ∧ s * g ∈ J := fun g hg =>
    exists_mul_mem_of_algebraMap_mem p (hmapEq ▸ Ideal.mem_map_of_mem _ hg)
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian K : K.FG)
  have hG' : ∀ g ∈ G, ∃ s, s ∉ ptI p ∧ s * g ∈ J := fun g hg =>
    hloc g (hG ▸ Ideal.subset_span hg)
  choose! t ht using hG'
  refine ⟨∏ g ∈ G, t g, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun g hg h0 => (ht g hg).1 (mem_ptIdeal.mpr h0)
  · intro g hg
    rw [← hG] at hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase G t hx, mul_comm (t x), mul_assoc]
      exact J.mul_mem_left _ (ht x hx).2
    | zero => rw [mul_zero]; exact J.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact J.add_mem hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_left_comm]; exact J.mul_mem_left _ hx

end

end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
