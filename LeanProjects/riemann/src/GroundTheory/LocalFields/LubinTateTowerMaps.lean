import Mathlib
import GroundTheory.LocalFields.LubinTatePrimitive

noncomputable section

open IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel

section Restrict

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

def restrictAutFun {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F] (σ : E ≃ₐ[K] E) :
    F ≃ₐ[K] F :=
  AlgHom.restrictNormal' ((E.val.comp (σ : E →ₐ[K] E)).comp (inclusion h)) F

theorem restrictAutFun_apply {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F]
    (σ : E ≃ₐ[K] E) (x : F) : ((restrictAutFun h σ x : F) : Ω) = σ ⟨x, h x.2⟩ := by
  have := AlgHom.restrictNormal_commutes ((E.val.comp (σ : E →ₐ[K] E)).comp (inclusion h)) F x
  simp only [restrictAutFun, AlgHom.restrictNormal', AlgEquiv.coe_ofBijective]
  exact this

def restrictAut {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F] :
    (E ≃ₐ[K] E) →* (F ≃ₐ[K] F) where
  toFun := restrictAutFun h
  map_one' := AlgEquiv.ext fun x => Subtype.ext (by rw [restrictAutFun_apply]; rfl)
  map_mul' σ τ := AlgEquiv.ext fun x => Subtype.ext (by
    rw [AlgEquiv.mul_apply, restrictAutFun_apply, restrictAutFun_apply]
    have : (⟨(restrictAutFun h τ x : Ω), h (restrictAutFun h τ x).2⟩ : E) = τ ⟨x, h x.2⟩ :=
      Subtype.ext (restrictAutFun_apply h τ x)
    rw [this]
    rfl)

theorem restrictAut_apply {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F]
    (σ : E ≃ₐ[K] E) (x : F) : ((restrictAut h σ x : F) : Ω) = σ ⟨x, h x.2⟩ :=
  restrictAutFun_apply h σ x

theorem restrictAut_restrictAut {E F G : IntermediateField K Ω} (h₁ : F ≤ E) (h₂ : G ≤ F)
    [Normal K F] [Normal K G] (σ : E ≃ₐ[K] E) :
    restrictAut h₂ (restrictAut h₁ σ) = restrictAut (h₂.trans h₁) σ :=
  AlgEquiv.ext fun x => Subtype.ext (by
    rw [restrictAut_apply, restrictAut_apply, restrictAut_apply])

theorem restrictAut_self {E : IntermediateField K Ω} [Normal K E] (σ : E ≃ₐ[K] E) :
    restrictAut le_rfl σ = σ :=
  AlgEquiv.ext fun x => Subtype.ext (by rw [restrictAut_apply])

theorem algEquiv_ext_of_restrictAut {ι : Type*} {F : ι → IntermediateField K Ω}
    [∀ n, Normal K (F n)] {E : IntermediateField K Ω} (hle : ∀ n, F n ≤ E)
    (hE : ∀ x ∈ E, ∃ n, x ∈ F n) {σ σ' : E ≃ₐ[K] E}
    (h : ∀ n, restrictAut (hle n) σ = restrictAut (hle n) σ') : σ = σ' := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  obtain ⟨n, hn⟩ := hE x x.2
  have := congrArg (fun τ : F n ≃ₐ[K] F n => ((τ ⟨x, hn⟩ : F n) : Ω)) (h n)
  simp only [restrictAut_apply] at this
  exact this

theorem exists_algEquiv_of_compatible {F : ℕ → IntermediateField K Ω} (hF : Monotone F)
    [∀ n, Normal K (F n)] {E : IntermediateField K Ω} [Algebra.IsAlgebraic K E]
    (hle : ∀ n, F n ≤ E) (hE : ∀ x ∈ E, ∃ n, x ∈ F n) (τ : ∀ n, F n ≃ₐ[K] F n)
    (hτ : ∀ m n (h : m ≤ n), restrictAut (hF h) (τ n) = τ m) :
    ∃ σ : E ≃ₐ[K] E, ∀ n, restrictAut (hle n) σ = τ n := by
  have hτ' : ∀ i j (x : Ω) (hi : x ∈ F i) (hj : x ∈ F j),
      ((τ i ⟨x, hi⟩ : F i) : Ω) = ((τ j ⟨x, hj⟩ : F j) : Ω) := by
    intro i j x hi hj
    rcases le_total i j with h | h
    · rw [← hτ i j h, restrictAut_apply]
    · rw [← hτ j i h, restrictAut_apply]
  let S : ℕ → Subalgebra K Ω := fun n => (F n).toSubalgebra
  have hS : Monotone S := fun _ _ h => hF h
  let f : ∀ n, S n →ₐ[K] Ω := fun n => (F n).val.comp (τ n : F n →ₐ[K] F n)
  have hf : ∀ (i j : ℕ) (h : S i ≤ S j), f i = (f j).comp (Subalgebra.inclusion h) := by
    intro i j h
    ext x
    exact hτ' i j x x.2 (h x.2)
  have hT : E.toSubalgebra ≤ iSup S := fun x hx => by
    obtain ⟨n, hn⟩ := hE x hx
    exact (le_iSup S n) hn
  let g := Subalgebra.iSupLift S hS.directed_le f hf E.toSubalgebra hT
  have hg : ∀ (x : E) (n : ℕ) (hn : (x : Ω) ∈ F n), g x = ((τ n ⟨x, hn⟩ : F n) : Ω) :=
    fun x n hn => Subalgebra.iSupLift_of_mem (K := S) x hn
  have hgE : ∀ x : E, g x ∈ E := fun x => by
    obtain ⟨n, hn⟩ := hE x x.2
    rw [hg x n hn]
    exact hle n (τ n ⟨x, hn⟩).2
  let g' : E →ₐ[K] E := g.codRestrict E.toSubalgebra hgE
  refine ⟨AlgEquiv.ofBijective g' (Algebra.IsAlgebraic.algHom_bijective _), fun n => ?_⟩
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [restrictAut_apply, AlgEquiv.ofBijective_apply]
  exact hg ⟨x, hle n x.2⟩ n x.2

end Restrict

namespace FormalGroup

section Reduce

variable {K : Type*} [Field K] [ValuativeRel K]

def unitsReduce (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) :
    (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ →* (𝒪[K] ⧸ Ideal.span {π ^ m})ˣ :=
  Units.map (Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π h))).toMonoidHom

theorem coe_unitsReduce (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) (u : (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ)
    (a : 𝒪[K]) (ha : Ideal.Quotient.mk _ a = (u : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    (unitsReduce π h u : 𝒪[K] ⧸ Ideal.span {π ^ m}) = Ideal.Quotient.mk _ a := by
  rw [unitsReduce, Units.coe_map, ← ha]
  exact Ideal.Quotient.factor_mk _ a

def unitsMk (π : 𝒪[K]) (n : ℕ) : 𝒪[K]ˣ →* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  Units.map (Ideal.Quotient.mk (Ideal.span {π ^ n})).toMonoidHom

theorem coe_unitsMk (π : 𝒪[K]) (n : ℕ) (u : 𝒪[K]ˣ) :
    (unitsMk π n u : 𝒪[K] ⧸ Ideal.span {π ^ n}) = Ideal.Quotient.mk _ (u : 𝒪[K]) := rfl

theorem unitsReduce_unitsMk (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) (u : 𝒪[K]ˣ) :
    unitsReduce π h (unitsMk π n u) = unitsMk π m u :=
  Units.ext (coe_unitsReduce π h _ _ rfl)

end Reduce

section Char

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}

theorem algEquiv_psEval_coe {E : IntermediateField K Ω} [FiniteDimensional K E]
    (τ : E ≃ₐ[K] E) (φ : PowerSeries 𝒪[K]) (z : E) (hz : valuation Ω (z : Ω) < 1)
    (hmem : psEval φ (fun _ => (z : Ω)) ∈ E) :
    ((τ ⟨psEval φ (fun _ => (z : Ω)), hmem⟩ : E) : Ω) = psEval φ (fun _ => ((τ z : E) : Ω)) := by
  have h1 : (⟨psEval φ (fun _ => (z : Ω)), hmem⟩ : E) = psEval φ (fun _ => z) :=
    Subtype.ext (psEval_coe E φ (fun _ => z) fun _ => hz)
  have hτ : valuation Ω ((τ z : E) : Ω) < 1 := by
    rw [valuation_coe_lt_one_iff, valuation_algEquiv_apply_of_isAlgebraic,
      ← valuation_coe_lt_one_iff]
    exact hz
  rw [h1, algEquiv_psEval τ φ (fun _ => z) fun _ => by rw [← valuation_coe_lt_one_iff]; exact hz]
  exact (psEval_coe E φ (fun _ => τ z) fun _ => hτ).symm

variable [IsSepClosed Ω]

def lubinTateChar (hf : IsLubinTateSeries π f) (n : ℕ) {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) : (E ≃ₐ[K] E) →* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  (lubinTateGalEquiv hπ hf n).toMonoidHom.comp (restrictAut hE)

theorem lubinTateChar_spec (hf : IsLubinTateSeries π f) {n : ℕ} {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E)
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) (a : 𝒪[K])
    (ha : Ideal.Quotient.mk _ a = (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    ((σ ⟨x.val, hE (val_mem_lubinTateField hπ hf hx)⟩ : E) : Ω) = (a • x).val :=
  (restrictAut_apply hE σ ⟨x.val, val_mem_lubinTateField hπ hf hx⟩).symm.trans
    (lubinTateGalEquiv_spec hf n (restrictAut hE σ) x hx a ha)

theorem lubinTateChar_eq_of_apply (hf : IsLubinTateSeries π f) {n : ℕ} {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E) (a : 𝒪[K])
    (h : ∀ (x) (hx : x ∈ lubinTateTorsion Ω (hπ := hπ) hf n),
      ((σ ⟨x.val, hE (val_mem_lubinTateField hπ hf hx)⟩ : E) : Ω) = (a • x).val) :
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n}) = Ideal.Quotient.mk _ a := by
  obtain ⟨l, hl, hann, -⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})
  have h1 := lubinTateChar_spec hπ hf hE σ hl b hb
  rw [h l hl] at h1
  have h2 : b • l = a • l := (IdealPoint.ext h1).symm
  rw [← hb, Ideal.Quotient.eq, ← hann, sub_smul, sub_eq_zero]
  exact h2

theorem lubinTateChar_reduce (hf : IsLubinTateSeries π f) {m n : ℕ} (hmn : m ≤ n)
    {E : IntermediateField K Ω} (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E) :
    lubinTateChar hπ hf m ((lubinTateField_mono hπ hf hmn).trans hE) σ =
      unitsReduce π hmn (lubinTateChar hπ hf n hE σ) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})
  apply Units.ext
  rw [coe_unitsReduce π hmn _ a ha, lubinTateChar_eq_of_apply hπ hf _ σ a]
  intro x hx
  exact lubinTateChar_spec hπ hf hE σ (lubinTateTorsion_mono hπ hf hmn hx) a ha

theorem lubinTateGalEquiv_restrictAut (hf : IsLubinTateSeries π f) {m n : ℕ} (hmn : m ≤ n)
    (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) :
    lubinTateGalEquiv hπ hf m (restrictAut (lubinTateField_mono hπ hf hmn) σ) =
      unitsReduce π hmn (lubinTateGalEquiv hπ hf n σ) := by
  have := lubinTateChar_reduce hπ hf hmn le_rfl σ
  simp only [lubinTateChar, MonoidHom.coe_comp, Function.comp_apply, restrictAut_self] at this
  exact this

theorem lubinTateChar_eq (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g) {n : ℕ}
    {E : IntermediateField K Ω} (hEf : lubinTateField Ω hπ hf n ≤ E)
    (hEg : lubinTateField Ω hπ hg n ≤ E) (σ : E ≃ₐ[K] E) :
    lubinTateChar hπ hf n hEf σ = lubinTateChar hπ hg n hEg σ := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (lubinTateChar hπ hf n hEf σ : 𝒪[K] ⧸ Ideal.span {π ^ n})
  apply Units.ext
  rw [← ha, lubinTateChar_eq_of_apply hπ hg hEg σ a]
  intro y hy
  obtain ⟨x, rfl⟩ := (lubinTatePointEquiv hg hf).surjective y
  have hx : x ∈ lubinTateTorsion Ω hf n := (lubinTatePointEquiv_mem_torsion_iff hg hf n x).mp hy
  set τ := restrictAut hEf σ
  have hyF : (lubinTatePointEquiv hg hf x).val ∈ lubinTateField Ω hπ hf n :=
    val_mem_lubinTateField_of_mem hπ hf hg hy
  have h1 : ((σ ⟨(lubinTatePointEquiv hg hf x).val, hEg (val_mem_lubinTateField hπ hg hy)⟩ : E) : Ω)
      = ((τ ⟨(lubinTatePointEquiv hg hf x).val, hyF⟩ : lubinTateField Ω hπ hf n) : Ω) :=
    (restrictAut_apply hEf σ ⟨_, hyF⟩).symm
  rw [h1]
  have h2 := algEquiv_psEval_coe τ (lubinTateHom hπ hg hf 1).toPowerSeries
    ⟨x.val, val_mem_lubinTateField hπ hf hx⟩ x.valuation_lt_one hyF
  refine h2.trans ?_
  rw [← map_smul, lubinTatePointEquiv_val]
  congr 2
  funext _
  rw [restrictAut_apply]
  exact lubinTateChar_spec hπ hf hEf σ hx a ha

end Char

end FormalGroup

end GroundTheory.LocalField
