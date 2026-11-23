import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FunKerSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.RationalityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DescPf

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem galAct_tmul {K₂ : Type*} [Field K₂] [Algebra K K₂] (σ : K₂ ≃ₐ[K] K₂) (a : K₂) (v : V) :
    galAct σ (a ⊗ₜ[K] v) = σ a ⊗ₜ[K] v := rfl

theorem lTensor_mkQ_galAct {K₂ : Type*} [Field K₂] [Algebra K K₂] (U : Submodule K V)
    (σ : K₂ ≃ₐ[K] K₂) (x : K₂ ⊗[K] V) :
    LinearMap.lTensor K₂ U.mkQ (galAct σ x) =
      LinearMap.rTensor (V ⧸ U) σ.toLinearMap (LinearMap.lTensor K₂ U.mkQ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => rfl
  | add y z hy hz => simp only [map_add, hy, hz]

theorem galAct_mem_baseSpan {K₂ : Type*} [Field K₂] [Algebra K K₂] (U : Submodule K V)
    (σ : K₂ ≃ₐ[K] K₂) {x : K₂ ⊗[K] V} (hx : x ∈ baseSpan K₂ U) : galAct σ x ∈ baseSpan K₂ U := by
  rw [mem_baseSpan_iff] at hx ⊢
  rw [lTensor_mkQ_galAct, hx, map_zero]

theorem mem_of_one_tmul_mem_baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) {v : V}
    (h : (1 : F) ⊗ₜ[K] v ∈ baseSpan F U) : v ∈ U := by
  rw [mem_baseSpan_iff] at h
  simp only [LinearMap.lTensor_tmul, Submodule.mkQ_apply] at h
  have hinj : Function.Injective (fun q : V ⧸ U => (1 : F) ⊗ₜ[K] q) := by
    have h1 : Function.Injective (LinearMap.rTensor (V ⧸ U) (Algebra.linearMap K F)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K F).injective
    intro q q' hq
    have : LinearMap.rTensor (V ⧸ U) (Algebra.linearMap K F) ((1 : K) ⊗ₜ[K] q) =
        LinearMap.rTensor (V ⧸ U) (Algebra.linearMap K F) ((1 : K) ⊗ₜ[K] q') := by
      simpa using hq
    have := h1 this
    simpa using congrArg (TensorProduct.lid K (V ⧸ U)) this
  have : (Submodule.Quotient.mk v : V ⧸ U) = 0 := hinj (by simpa using h)
  exact (Submodule.Quotient.mk_eq_zero U).mp this

end SlopeTestRemainingChoices

theorem funKer_holds : FunKerStatement := by
  intro K Ω V _ _ _ _ _ _ _ U _ Wc FF hWle hdef hkill hdet hconj
  classical
  obtain ⟨K₁, hK₁, ρ, c, hc, hdesc, hspan, hfinW, hrank⟩ :=
    rationality_holds K Ω V U Wc FF hWle hdef hkill hdet
  have hK₁def : ∀ i, DefinedOver (c i) K₁ := fun i => (hc i).2
  have hckill : ∀ i, Wc ≤ LinearMap.ker (c i) := fun i => hkill _ (hc i).1
  choose φ hφ using fun i => exists_ratFun (hK₁def i)

  have hDfd : FiniteDimensional K₁ (baseSpan K₁ U) := finiteDimensional_baseSpan K₁ U
  have hEfd : FiniteDimensional Ω (baseSpan Ω U) := finiteDimensional_baseSpan Ω U
  set D := baseSpan K₁ U with hDdef
  set E := baseSpan Ω U with hEdef
  let Φ1 : D →ₗ[K₁] (Fin ρ → K₁) := LinearMap.pi fun i => φ i ∘ₗ D.subtype
  have hdescD : descend K₁ Wc ≤ D := by rw [hdesc]; exact inf_le_left
  have hker1 : LinearMap.ker Φ1 = (descend K₁ Wc).comap D.subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    rw [hdesc, Submodule.mem_inf, Submodule.mem_iInf]
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    constructor
    · intro h
      refine ⟨x.2, fun i => ?_⟩
      rw [← hφ i]
      have := congrFun h i
      simp only [Φ1, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        Pi.zero_apply] at this
      rw [this, map_zero]
    · rintro ⟨-, h⟩
      funext i
      simp only [Φ1, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        Pi.zero_apply]
      apply (algebraMap K₁ Ω).injective
      rw [hφ i, map_zero]; exact h i
  have hfinker : Module.finrank K₁ (LinearMap.ker Φ1) = Module.finrank K₁ (descend K₁ Wc) := by
    rw [hker1]; exact (Submodule.comapSubtypeEquivOfLe hdescD).finrank_eq
  have hsurj1 : LinearMap.range Φ1 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ1
    rw [hfinker, finrank_baseSpan K₁ U] at h1
    rw [Module.finrank_fin_fun]
    omega
  have hd : ∀ j : Fin ρ, ∃ dj : D, Φ1 dj = Pi.single j 1 := fun j => by
    have : Pi.single j (1 : K₁) ∈ LinearMap.range Φ1 := hsurj1 ▸ Submodule.mem_top
    exact this
  choose d hd using hd
  let ΦΩ : E →ₗ[Ω] (Fin ρ → Ω) := LinearMap.pi fun i => c i ∘ₗ E.subtype
  have hdE : ∀ j, inclT K₁ V (d j : K₁ ⊗[K] V) ∈ E := fun j => inclT_mem_baseSpan K₁ U _ (d j).2
  have hΦd : ∀ j, ΦΩ ⟨_, hdE j⟩ = Pi.single j 1 := by
    intro j
    funext i
    have h := congrFun (hd j) i
    simp only [Φ1, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
    simp only [ΦΩ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [← hφ i, h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hsurjΩ : LinearMap.range ΦΩ = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun Ω (Fin ρ)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    exact ⟨_, hΦd j⟩
  have hWcE : Wc.comap E.subtype ≤ LinearMap.ker ΦΩ := by
    intro y hy
    rw [LinearMap.mem_ker]
    funext i
    simp only [ΦΩ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      Pi.zero_apply]
    exact hckill i hy
  have hkerΩ : Wc.comap E.subtype = LinearMap.ker ΦΩ := by
    apply Submodule.eq_of_le_of_finrank_eq hWcE
    have h1 := LinearMap.finrank_range_add_finrank_ker ΦΩ
    rw [hsurjΩ, finrank_top, Module.finrank_fin_fun, finrank_baseSpan Ω U] at h1
    rw [(Submodule.comapSubtypeEquivOfLe hWle).finrank_eq, ← hfinW]
    omega
  have hcut : ∀ y ∈ E, (∀ i, c i y = 0) → y ∈ Wc := by
    intro y hy h
    have : (⟨y, hy⟩ : E) ∈ LinearMap.ker ΦΩ := by
      rw [LinearMap.mem_ker]; funext i; exact h i
    rw [← hkerΩ] at this
    exact this

  have : FiniteDimensional K K₁ := hK₁

  let bK := Module.finBasis K K₁
  let q : Polynomial K := ∏ k, minpoly K ((bK k : K₁) : Ω)
  have hint : ∀ k, IsIntegral K ((bK k : K₁) : Ω) := fun k =>
    (IsIntegral.of_finite K (bK k)).map (IsScalarTower.toAlgHom K K₁ Ω)
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => minpoly.ne_zero (hint k)
  let K₂ : IntermediateField K Ω := IntermediateField.adjoin K (q.rootSet Ω)
  have hsplit : (q.map (algebraMap K Ω)).Splits := IsAlgClosed.splits _
  have : Polynomial.IsSplittingField K K₂ q :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have : FiniteDimensional K K₂ := Polynomial.IsSplittingField.finiteDimensional K₂ q
  have : Normal K K₂ := Normal.of_isSplittingField q
  have : Algebra.IsSeparable K K₂ := inferInstance
  have : IsGalois K K₂ := {}
  have hK12 : K₁ ≤ K₂ := by
    intro x hx
    have hxb := (bK.sum_repr ⟨x, hx⟩)
    have hx' : x = ∑ k, bK.repr ⟨x, hx⟩ k • ((bK k : K₁) : Ω) := by
      have := congrArg K₁.val.toLinearMap hxb
      rw [map_sum] at this
      simp only [map_smul] at this
      exact this.symm
    rw [hx']
    refine K₂.toSubalgebra.toSubmodule.sum_mem fun k _ => K₂.toSubalgebra.toSubmodule.smul_mem _ ?_
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hq0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_finsetProd]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [← Polynomial.aeval_def]; exact minpoly.aeval K _)
  have hK₂def : ∀ i, DefinedOver (c i) K₂ := fun i => (hK₁def i).mono hK12
  have hstab : ∀ σ : K₂ ≃ₐ[K] K₂, ∀ x ∈ descend K₂ Wc, galAct σ x ∈ descend K₂ Wc := by
    intro σ x hx
    have hxW : inclT K₂ V x ∈ Wc := hx
    have hxU : x ∈ baseSpan K₂ U := mem_baseSpan_of_inclT K₂ U x (hWle hxW)
    show inclT K₂ V (galAct σ x) ∈ Wc
    refine hcut _ (inclT_mem_baseSpan K₂ U _ (galAct_mem_baseSpan U σ hxU)) fun i => ?_
    exact hconj (c i) (hc i).1 K₂ inferInstance inferInstance (hK₂def i) σ x hx
  have hGD := galoisDescent_holds K K₂ V (descend K₂ Wc) hstab
  set W := kPoints (descend K₂ Wc) with hWdef
  have hWU : W ≤ U := by
    intro v hv
    have h1 : (1 : K₂) ⊗ₜ[K] v ∈ descend K₂ Wc := hv
    have h2 : inclT K₂ V ((1 : K₂) ⊗ₜ[K] v) ∈ Wc := h1
    exact mem_of_one_tmul_mem_baseSpan K₂ U (mem_baseSpan_of_inclT K₂ U _ (hWle h2))

  let ι : K₁ ⊗[K] V →ₗ[K] K₂ ⊗[K] V :=
    LinearMap.rTensor V (IntermediateField.inclusion hK12).toLinearMap
  have hι : ∀ x, inclT K₂ V (ι x) = inclT K₁ V x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  have hK1W : ∀ x : K₁ ⊗[K] V, inclT K₁ V x ∈ Wc ↔ x ∈ baseSpan K₁ W := by
    intro x
    constructor
    · intro hx
      have h1 : ι x ∈ descend K₂ Wc := by show inclT K₂ V (ι x) ∈ Wc; rw [hι]; exact hx
      rw [hGD] at h1
      have h2 := inclT_mem_baseSpan K₂ W _ h1
      rw [hι] at h2
      exact mem_baseSpan_of_inclT K₁ W x h2
    · intro hx
      have h1 := inclT_mem_baseSpan K₁ W x hx
      rw [← hι] at h1 ⊢
      have h2 : ι x ∈ baseSpan K₂ W := mem_baseSpan_of_inclT K₂ W _ h1
      rw [← hGD] at h2
      exact h2
  have hWc : baseSpan Ω W = Wc := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, hw, rfl⟩
      have : (1 : K₂) ⊗ₜ[K] w ∈ descend K₂ Wc := hw
      exact this
    · rw [← hspan]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact inclT_mem_baseSpan K₁ W x ((hK1W x).mp hx)
  have hWfd : FiniteDimensional K W := Submodule.finiteDimensional_of_le hWU
  have hdescW : descend K₁ Wc = baseSpan K₁ W := by
    ext x; exact hK1W x
  refine ⟨W, hWU, hWc, K₁, hK₁, ρ, c, hc, fun x hx => ?_, ?_⟩
  · constructor
    · intro h
      have : x ∈ descend K₁ Wc := by
        rw [hdesc, Submodule.mem_inf, Submodule.mem_iInf]
        exact ⟨hx, fun i => h i⟩
      rw [hdescW] at this; exact this
    · intro h i
      have : inclT K₁ V x ∈ Wc := (hK1W x).mpr h
      exact hckill i this
  · rw [← hrank, hdescW, finrank_baseSpan K₁ W]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
