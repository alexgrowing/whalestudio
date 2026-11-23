import Mathlib
import GroundTheory.LocalFields.LubinTateTowerMaps
import GroundTheory.LocalFields.ExamplesLaurent

noncomputable section

open IntermediateField Topology Filter

namespace GroundTheory.LocalField

open ValuativeRel

section Finite

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem exists_le_of_finiteDimensional {F : ℕ → IntermediateField K L} (hF : Monotone F)
    {E : IntermediateField K L} [FiniteDimensional K E] (hE : ∀ x ∈ E, ∃ n, x ∈ F n) :
    ∃ n, E ≤ F n := by
  classical
  let b := Module.finBasis K E
  choose N hN using fun i => hE (b i) (b i).2
  refine ⟨Finset.univ.sup N, fun x hx => ?_⟩
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : L) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    exact h.symm
  rw [hx']
  exact sum_mem fun i _ =>
    IntermediateField.smul_mem _ (hF (Finset.le_sup (Finset.mem_univ i)) (hN i))

end Finite

section UnitsTopology

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem exists_maximalIdeal_pow_subset {A : Set 𝒪[K]} (hA : A ∈ 𝓝 (1 : 𝒪[K])) :
    ∃ n, ∀ y : 𝒪[K], y - 1 ∈ 𝓂[K] ^ n → y ∈ A := by
  have h0 : (fun z => z + 1) ⁻¹' A ∈ 𝓝 (0 : 𝒪[K]) := by
    have h := (continuous_add_const (1 : 𝒪[K])).continuousAt (x := 0)
    rw [ContinuousAt, zero_add] at h
    exact h hA
  obtain ⟨γ, -, hγ⟩ := (EqualChar.hasBasis_nhds_zero_integer K).mem_iff.mp h0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ1 : valuation K (ϖ : K) < 1 :=
    valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ1 γ
  refine ⟨n, fun y hy => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy
  obtain ⟨c, hc⟩ := hy
  have hc1 : valuation K (c : K) ≤ 1 := c.2
  have hmem : y - 1 ∈ EqualChar.ballIdeal K γ := by
    rw [EqualChar.mem_ballIdeal]
    calc valuation K ((y - 1 : 𝒪[K]) : K) = valuation K (ϖ : K) ^ n * valuation K (c : K) := by
          rw [hc]; push_cast; rw [map_mul, map_pow]
      _ ≤ valuation K (ϖ : K) ^ n := mul_le_of_le_one_right' hc1
      _ < γ := hn
  simpa using hγ hmem

theorem FormalGroup.unitsMk_eq_one_iff {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} {u : 𝒪[K]ˣ} :
    FormalGroup.unitsMk π n u = 1 ↔ u ∈ unitFiltration K n := by
  rw [mem_unitFiltration, ← Units.val_eq_one, FormalGroup.coe_unitsMk, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]

theorem isOpen_unitFiltration (n : ℕ) : IsOpen (unitFiltration K n : Set 𝒪[K]ˣ) := by
  have h : (unitFiltration K n : Set 𝒪[K]ˣ) = (fun u : 𝒪[K]ˣ => (u : 𝒪[K]) - 1) ⁻¹'
      ((IsLocalRing.maximalIdeal 𝒪[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := rfl
  rw [h]
  exact (IsLocalRing.isOpen_maximalIdeal_pow 𝒪[K] n).preimage
    (Units.continuous_val.sub continuous_const)

theorem exists_unitFiltration_subset {t : Set 𝒪[K]ˣ} (ht : t ∈ 𝓝 1) :
    ∃ n, (unitFiltration K n : Set 𝒪[K]ˣ) ⊆ t := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, mem_comap] at ht
  obtain ⟨s, hs, hst⟩ := ht
  have hs' : s ∈ 𝓝 ((1 : 𝒪[K]), (1 : 𝒪[K]ᵐᵒᵖ)) := by
    rw [Prod.mk_one_one]
    rwa [map_one] at hs
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hs'
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : 𝒪[K]) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_subset (inter_mem hA hB')
  refine ⟨n, fun u hu => hst (hAB ?_)⟩
  exact ⟨(hn u hu).1, (hn _ (inv_mem (show u ∈ unitFiltration K n from hu))).2⟩

end UnitsTopology

namespace FormalGroup

theorem eq_zero_of_forall_pow_dvd {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {π : 𝒪[K]} (hπ : Irreducible π) {x : 𝒪[K]}
    (h : ∀ n, π ^ n ∣ x) : x = 0 := by
  by_contra hx
  obtain ⟨k, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  obtain ⟨c, hc⟩ := h (k + 1)
  have h1 : (w : 𝒪[K]) * π ^ k = (π * c) * π ^ k := by rw [hc]; ring
  have h2 := mul_right_cancel₀ (pow_ne_zero k hπ.ne_zero) h1
  exact hπ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ w.isUnit))

section Limit

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}

variable (Ω) in

def lubinTateLimit (hπ : Irreducible π) : IntermediateField K Ω :=
  ⨆ n, lubinTateField Ω hπ (isLubinTateSeries_ltPoly π) n

theorem monotone_lubinTateField (hf : IsLubinTateSeries π f) :
    Monotone (lubinTateField Ω hπ hf) :=
  fun _ _ h => lubinTateField_mono hπ hf h

variable [IsSepClosed Ω]

theorem lubinTateLimit_eq (hf : IsLubinTateSeries π f) :
    lubinTateLimit Ω hπ = ⨆ n, lubinTateField Ω hπ hf n := by
  simp_rw [lubinTateLimit, lubinTateField_eq hπ (isLubinTateSeries_ltPoly π) hf]

theorem lubinTateField_le_lubinTateLimit (hf : IsLubinTateSeries π f) (n : ℕ) :
    lubinTateField Ω hπ hf n ≤ lubinTateLimit Ω hπ := by
  rw [lubinTateLimit_eq hπ hf]
  exact le_iSup (fun n => lubinTateField Ω hπ hf n) n

theorem mem_lubinTateLimit_iff (hf : IsLubinTateSeries π f) {x : Ω} :
    x ∈ lubinTateLimit Ω hπ ↔ ∃ n, x ∈ lubinTateField Ω hπ hf n := by
  rw [lubinTateLimit_eq hπ hf, ← SetLike.mem_coe,
    IntermediateField.coe_iSup_of_directed (monotone_lubinTateField hπ hf).directed_le]
  simp only [Set.mem_iUnion, SetLike.mem_coe]

instance isGalois_lubinTateLimit : IsGalois K (lubinTateLimit Ω hπ) := by
  unfold lubinTateLimit
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

theorem lubinTateLimit_ext (hf : IsLubinTateSeries π f)
    {σ σ' : lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ}
    (h : ∀ n, lubinTateChar hπ hf n (lubinTateField_le_lubinTateLimit hπ hf n) σ =
      lubinTateChar hπ hf n (lubinTateField_le_lubinTateLimit hπ hf n) σ') : σ = σ' :=
  algEquiv_ext_of_restrictAut (lubinTateField_le_lubinTateLimit hπ hf)
    (fun _ hx => (mem_lubinTateLimit_iff hπ hf).mp hx)
    fun n => (lubinTateGalEquiv hπ hf n).injective (h n)

theorem exists_lubinTateLimitAut (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) :
    ∃ σ : lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ, ∀ n,
      restrictAut (lubinTateField_le_lubinTateLimit hπ hf n) σ =
        (lubinTateGalEquiv hπ hf n).symm (unitsMk π n u) :=
  exists_algEquiv_of_compatible (monotone_lubinTateField hπ hf)
    (lubinTateField_le_lubinTateLimit hπ hf) (fun _ hx => (mem_lubinTateLimit_iff hπ hf).mp hx) _
    fun m n h => by
      apply (lubinTateGalEquiv hπ hf m).injective
      rw [lubinTateGalEquiv_restrictAut hπ hf h, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, unitsReduce_unitsMk]

def lubinTateLimitAut (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) :
    lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ :=
  Classical.choose (exists_lubinTateLimitAut hπ hf u)

theorem lubinTateChar_lubinTateLimitAut (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) (n : ℕ) :
    lubinTateChar hπ hf n (lubinTateField_le_lubinTateLimit hπ hf n)
      (lubinTateLimitAut (Ω := Ω) hπ hf u) = unitsMk π n u := by
  rw [lubinTateChar, MonoidHom.comp_apply, lubinTateLimitAut,
    Classical.choose_spec (exists_lubinTateLimitAut hπ hf u) n]
  exact MulEquiv.apply_symm_apply _ _

def lubinTateLimitAutHom (hf : IsLubinTateSeries π f) :
    𝒪[K]ˣ →* (lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ) where
  toFun := lubinTateLimitAut hπ hf
  map_one' := lubinTateLimit_ext hπ hf fun n => by
    rw [lubinTateChar_lubinTateLimitAut, map_one, map_one]
  map_mul' u v := lubinTateLimit_ext hπ hf fun n => by
    rw [map_mul (lubinTateChar hπ hf n _), lubinTateChar_lubinTateLimitAut,
      lubinTateChar_lubinTateLimitAut, lubinTateChar_lubinTateLimitAut, map_mul]

theorem lubinTateLimitAutHom_injective (hf : IsLubinTateSeries π f) :
    Function.Injective (lubinTateLimitAutHom (Ω := Ω) hπ hf) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h : ∀ n, unitsMk π n u = 1 := fun n => by
    rw [← lubinTateChar_lubinTateLimitAut (Ω := Ω) hπ hf u n]
    change lubinTateChar hπ hf n _ (lubinTateLimitAutHom hπ hf u) = 1
    rw [hu, map_one]
  apply Units.ext
  rw [Units.val_one, ← sub_eq_zero]
  refine eq_zero_of_forall_pow_dvd hπ fun n => ?_
  have := congrArg Units.val (h n)
  rw [coe_unitsMk, Units.val_one, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at this
  exact this

theorem lubinTateLimitAutHom_surjective (hf : IsLubinTateSeries π f) :
    Function.Surjective (lubinTateLimitAutHom (Ω := Ω) hπ hf) := by
  intro σ
  set a : ∀ n, (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ := fun n =>
    lubinTateChar hπ hf n (lubinTateField_le_lubinTateLimit hπ hf n) σ with ha_def
  have ha : ∀ m n (h : m ≤ n), unitsReduce π h (a n) = a m := fun m n h =>
    (lubinTateChar_reduce hπ hf h (lubinTateField_le_lubinTateLimit hπ hf n) σ).symm
  choose r hr using fun n => Ideal.Quotient.mk_surjective (a n : 𝒪[K] ⧸ Ideal.span {π ^ n})
  have hI : ∀ n, ((IsLocalRing.maximalIdeal 𝒪[K]) ^ n • ⊤ : Submodule 𝒪[K] 𝒪[K]) =
      Ideal.span {π ^ n} := by
    intro n
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  have hcomp : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[K]) 𝒪[K] := by
    let := IsTopologicalAddGroup.rightUniformSpace K
    have := isUniformAddGroup_of_addCommGroup (G := K)
    infer_instance
  have hrm : ∀ {m n : ℕ}, m ≤ n →
      r m ≡ r n [SMOD ((IsLocalRing.maximalIdeal 𝒪[K]) ^ m • ⊤ : Submodule 𝒪[K] 𝒪[K])] := by
    intro m n h
    rw [hI, SModEq.sub_mem, ← Ideal.Quotient.eq, hr m, ← ha m n h,
      coe_unitsReduce π h (a n) (r n) (hr n)]
  obtain ⟨c, hc⟩ := hcomp.toIsPrecomplete.prec hrm
  have hcn : ∀ n, Ideal.Quotient.mk (Ideal.span {π ^ n}) c = a n := fun n => by
    have := hc n
    rw [hI, SModEq.sub_mem, ← Ideal.Quotient.eq, hr n] at this
    exact this.symm
  have hcu : IsUnit c := by
    by_contra hnu
    have : Nontrivial (𝒪[K] ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.nontrivial_iff.mpr (by
      rw [Ne, Ideal.span_singleton_eq_top, pow_one]
      exact hπ.not_isUnit)
    have hm : c ∈ Ideal.span {π ^ 1} := by
      rw [pow_one, ← hπ.maximalIdeal_eq]
      exact hnu
    have h1 := hcn 1
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm] at h1
    exact (a 1).ne_zero h1.symm
  refine ⟨hcu.unit, lubinTateLimit_ext hπ hf fun n => ?_⟩
  change lubinTateChar hπ hf n _ (lubinTateLimitAut hπ hf hcu.unit) = a n
  rw [lubinTateChar_lubinTateLimitAut]
  exact Units.ext (hcn n)

theorem restrictAut_lubinTateLimitAut_eq_one_iff (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) (n : ℕ) :
    restrictAut (lubinTateField_le_lubinTateLimit hπ hf n) (lubinTateLimitAut (Ω := Ω) hπ hf u) = 1
      ↔ u ∈ unitFiltration K n := by
  rw [← unitsMk_eq_one_iff hπ, ← lubinTateChar_lubinTateLimitAut (Ω := Ω) hπ hf u n, lubinTateChar,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

theorem lubinTateLimitAutHom_apply (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) :
    lubinTateLimitAutHom (Ω := Ω) hπ hf u = lubinTateLimitAut hπ hf u := rfl

theorem mem_fixingSubgroup_restrict_iff (hf : IsLubinTateSeries π f) (n : ℕ)
    (σ : lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ) :
    σ ∈ (IntermediateField.restrict (lubinTateField_le_lubinTateLimit hπ hf n)).fixingSubgroup ↔
      restrictAut (lubinTateField_le_lubinTateLimit hπ hf n) σ = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [restrictAut_apply, AlgEquiv.one_apply]
    exact congrArg Subtype.val (h _ ((mem_restrict _ _).mpr x.2))
  · intro h x hx
    apply Subtype.ext
    have h2 := restrictAut_apply (lubinTateField_le_lubinTateLimit hπ hf n) σ
      ⟨x, (mem_restrict _ x).mp hx⟩
    rw [h, AlgEquiv.one_apply] at h2
    exact h2.symm

theorem continuous_lubinTateLimitAutHom (hf : IsLubinTateSeries π f) :
    Continuous (lubinTateLimitAutHom (Ω := Ω) hπ hf) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K _ s).mp hs
  obtain ⟨N, hN⟩ := exists_le_of_finiteDimensional
    (F := fun n => IntermediateField.restrict (lubinTateField_le_lubinTateLimit (Ω := Ω) hπ hf n))
    (fun _ _ h x hx => (mem_restrict _ x).mpr (lubinTateField_mono hπ hf h ((mem_restrict _ x).mp hx)))
    (E := E) fun x _ => by
      obtain ⟨n, hn⟩ := (mem_lubinTateLimit_iff hπ hf).mp x.2
      exact ⟨n, (mem_restrict _ x).mpr hn⟩
  refine Filter.mem_map.mpr
    (mem_of_superset ((isOpen_unitFiltration N).mem_nhds (one_mem _)) fun u hu => hEs ?_)
  rw [SetLike.mem_coe, lubinTateLimitAutHom_apply]
  refine IntermediateField.fixingSubgroup_antitone hN ?_
  rw [mem_fixingSubgroup_restrict_iff]
  exact (restrictAut_lubinTateLimitAut_eq_one_iff (Ω := Ω) hπ hf u N).mpr hu

def lubinTateLimitGalEquiv (hf : IsLubinTateSeries π f) :
    𝒪[K]ˣ ≃ₜ* (lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ) :=
  let e := MulEquiv.ofBijective (lubinTateLimitAutHom (Ω := Ω) hπ hf)
    ⟨lubinTateLimitAutHom_injective hπ hf, lubinTateLimitAutHom_surjective hπ hf⟩
  { e with
    continuous_toFun := continuous_lubinTateLimitAutHom hπ hf
    continuous_invFun := by
      refine continuous_of_continuousAt_one e.symm ?_
      rw [ContinuousAt, map_one]
      intro t ht
      obtain ⟨N, hN⟩ := exists_unitFiltration_subset ht
      have : FiniteDimensional K
          (IntermediateField.restrict (lubinTateField_le_lubinTateLimit (Ω := Ω) hπ hf N)) :=
        (restrictAlgEquiv (lubinTateField_le_lubinTateLimit (Ω := Ω) hπ hf N)).toLinearEquiv.finiteDimensional
      refine Filter.mem_map.mpr (mem_of_superset ((IntermediateField.restrict
        (lubinTateField_le_lubinTateLimit (Ω := Ω) hπ hf N)).fixingSubgroup_isOpen.mem_nhds
          (one_mem _)) fun σ hσ => hN ?_)
      obtain ⟨u, rfl⟩ := e.surjective σ
      show e.symm (e u) ∈ _
      rw [e.symm_apply_apply, SetLike.mem_coe,
        ← restrictAut_lubinTateLimitAut_eq_one_iff (Ω := Ω) hπ hf u N,
        ← mem_fixingSubgroup_restrict_iff]
      exact hσ }

theorem lubinTateLimitGalEquiv_apply' (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) :
    lubinTateLimitGalEquiv (Ω := Ω) hπ hf u = lubinTateLimitAut hπ hf u := rfl

theorem lubinTateChar_lubinTateLimitGalEquiv (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) (n : ℕ) :
    lubinTateChar hπ hf n (lubinTateField_le_lubinTateLimit hπ hf n)
      (lubinTateLimitGalEquiv (Ω := Ω) hπ hf u) = unitsMk π n u :=
  lubinTateChar_lubinTateLimitAut hπ hf u n

theorem lubinTateLimitGalEquiv_apply (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ) {n : ℕ}
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) :
    ((lubinTateLimitGalEquiv hπ hf u
      ⟨x.val, lubinTateField_le_lubinTateLimit hπ hf n (val_mem_lubinTateField hπ hf hx)⟩ :
        lubinTateLimit Ω hπ) : Ω) = ((u : 𝒪[K]) • x).val :=
  lubinTateChar_spec hπ hf _ _ hx (u : 𝒪[K]) (by
    rw [lubinTateChar_lubinTateLimitGalEquiv, coe_unitsMk])

theorem lubinTateLimitGalEquiv_eq_iff (hf : IsLubinTateSeries π f) (u : 𝒪[K]ˣ)
    (σ : lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ) :
    lubinTateLimitGalEquiv hπ hf u = σ ↔
      ∀ (n : ℕ) (x : IdealPoint Ω (lubinTateFormalGroup hπ hf)) (hx : x ∈ lubinTateTorsion Ω hf n),
        ((σ ⟨x.val, lubinTateField_le_lubinTateLimit hπ hf n (val_mem_lubinTateField hπ hf hx)⟩ :
          lubinTateLimit Ω hπ) : Ω) = ((u : 𝒪[K]) • x).val := by
  constructor
  · rintro rfl n x hx
    exact lubinTateLimitGalEquiv_apply hπ hf u hx
  · intro h
    refine lubinTateLimit_ext hπ hf fun n => Units.ext ?_
    rw [lubinTateChar_lubinTateLimitGalEquiv, coe_unitsMk,
      lubinTateChar_eq_of_apply hπ hf _ σ _ fun x hx => h n x hx]

theorem lubinTateLimitGalEquiv_eq (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) :
    lubinTateLimitGalEquiv (Ω := Ω) hπ hf = lubinTateLimitGalEquiv hπ hg := by
  ext u : 1
  refine lubinTateLimit_ext hπ hg fun n => ?_
  rw [← lubinTateChar_eq hπ hf hg (lubinTateField_le_lubinTateLimit hπ hf n),
    lubinTateChar_lubinTateLimitGalEquiv, lubinTateChar_lubinTateLimitGalEquiv]

end Limit

end FormalGroup

end GroundTheory.LocalField
