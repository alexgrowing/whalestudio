import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

noncomputable section

open NumberField IsDedekindDomain
open scoped Pointwise

namespace PositivityTheory.Pf1.CLGD.K.CMDescent

section Restrict

variable (F : Type*) {E Ω : Type*} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω]
  [IsScalarTower F E Ω]

abbrev res : (Ω ≃ₐ[E] Ω) →* (Ω ≃ₐ[F] Ω) := AlgEquiv.restrictScalarsHom F

@[simp] theorem res_apply (σ : Ω ≃ₐ[E] Ω) (x : Ω) : res F σ x = σ x := rfl

def liftE (τ : Ω ≃ₐ[F] Ω) (h : ∀ e : E, τ (algebraMap E Ω e) = algebraMap E Ω e) : Ω ≃ₐ[E] Ω :=
  { τ.toRingEquiv with commutes' := h }

@[simp] theorem res_liftE (τ : Ω ≃ₐ[F] Ω) (h : ∀ e : E, τ (algebraMap E Ω e) = algebraMap E Ω e) :
    res F (liftE F τ h) = τ := AlgEquiv.ext fun _ ↦ rfl

theorem exists_finiteDimensional_fixingSubgroup_le {K L : Type*} [Field K] [Field L] [Algebra K L]
    (N : Subgroup (L ≃ₐ[K] L)) (hN : IsOpen (N : Set (L ≃ₐ[K] L))) :
    ∃ M : IntermediateField K L, FiniteDimensional K M ∧ M.fixingSubgroup ≤ N := by
  have h1 : (N : Set (L ≃ₐ[K] L)) ∈ nhds 1 := hN.mem_nhds N.one_mem
  obtain ⟨M, hM, hle⟩ := (krullTopology_mem_nhds_one_iff K L _).1 h1
  exact ⟨M, hM, hle⟩

end Restrict

section Descend

variable (F : Type*) {E Ω : Type*} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω]
  [IsScalarTower F E Ω]

theorem res_smul (σ : Ω ≃ₐ[E] Ω) (A : ValuationSubring Ω) : res F σ • A = σ • A := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ← map_inv]
  rfl

theorem res_mem_decompositionSubgroup {σ : Ω ≃ₐ[E] Ω} {A : ValuationSubring Ω}
    (h : σ ∈ A.decompositionSubgroup E) : res F σ ∈ A.decompositionSubgroup F := by
  have h1 : σ • A = A := h
  show res F σ • A = A
  rw [res_smul, h1]

theorem exists_finiteDimensional_res_le [FiniteDimensional F E] (M : IntermediateField F Ω) [FiniteDimensional F M]
    (hint : ∀ x : Ω, IsIntegral F x → IsIntegral E x) :
    ∃ M' : IntermediateField E Ω, FiniteDimensional E M' ∧
      ∀ σ ∈ M'.fixingSubgroup, res F σ ∈ M.fixingSubgroup := by
  classical
  let b := Module.finBasis F M
  let S : Set Ω := Set.range fun i ↦ ((b i : M) : Ω)
  have hSf : Finite S := Set.finite_range _ |>.to_subtype
  refine ⟨IntermediateField.adjoin E S, ?_, ?_⟩
  · refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨i, rfl⟩
    exact hint _ ((IsIntegral.of_finite F (b i)).map M.val)
  · intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro y hy
    have hb : ∀ i, res F σ ((b i : M) : Ω) = ((b i : M) : Ω) := fun i ↦
      hσ _ (IntermediateField.subset_adjoin E S ⟨i, rfl⟩)
    have key : ((res F σ).toLinearMap).comp M.val.toLinearMap = M.val.toLinearMap :=
      b.ext fun i ↦ by simpa using hb i
    have := LinearMap.congr_fun key ⟨y, hy⟩
    simpa using this

theorem continuous_res [FiniteDimensional F E] (hint : ∀ x : Ω, IsIntegral F x → IsIntegral E x) :
    Continuous (res F (E := E) (Ω := Ω)) := by
  refine continuous_of_continuousAt_one (res F) ?_
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hM, hMs⟩ := hs
  obtain ⟨M', hM', hM'le⟩ := exists_finiteDimensional_res_le F M hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  exact ⟨M', hM', fun σ hσ ↦ hMs (hM'le σ hσ)⟩

end Descend

section Descend2

variable (F : Type*) {E Ω : Type*} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω]
  [IsScalarTower F E Ω]

theorem descend [FiniteDimensional F E] (hint : ∀ x : Ω, IsIntegral F x → IsIntegral E x)
    (Y : IntermediateField F Ω) (hYE : ∀ e : E, algebraMap E Ω e ∈ Y)
    (Hp : Subgroup (Ω ≃ₐ[F] Ω)) [Hp.Normal] (hHo : IsOpen (Hp : Set (Ω ≃ₐ[F] Ω)))
    (hHs : Group.IsSolvable ((Ω ≃ₐ[F] Ω) ⧸ Hp)) (hsup : Hp ⊔ Y.fixingSubgroup = ⊤)
    (N : Subgroup (Ω ≃ₐ[E] Ω)) (hN : ∀ σ : Ω ≃ₐ[E] Ω, res F σ ∈ Y.fixingSubgroup → σ ∈ N) :
    IsOpen ((Hp.comap (res F (E := E) (Ω := Ω)) : Subgroup (Ω ≃ₐ[E] Ω)) : Set (Ω ≃ₐ[E] Ω)) ∧
      Group.IsSolvable ((Ω ≃ₐ[E] Ω) ⧸ Hp.comap (res F (E := E) (Ω := Ω))) ∧ Hp.comap (res F (E := E) (Ω := Ω)) ⊔ N = ⊤ := by
  refine ⟨hHo.preimage (continuous_res F hint), ?_, ?_⟩
  · let φ : (Ω ≃ₐ[E] Ω) →* (Ω ≃ₐ[F] Ω) ⧸ Hp := (QuotientGroup.mk' Hp).comp (res F)
    have hker : φ.ker = Hp.comap (res F (E := E) (Ω := Ω)) := by
      ext σ
      simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    exact Group.isSolvable_of_isSolvable_injective (f := (QuotientGroup.kerLift φ).comp
      (QuotientGroup.quotientMulEquivOfEq hker.symm).toMonoidHom)
      ((QuotientGroup.kerLift_injective φ).comp (QuotientGroup.quotientMulEquivOfEq hker.symm).injective)
  · rw [eq_top_iff]
    intro g _
    have hg : res F g ∈ Hp ⊔ Y.fixingSubgroup := hsup ▸ Subgroup.mem_top _
    obtain ⟨h, hh, n, hn, hhn⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    have hnE : ∀ e : E, n (algebraMap E Ω e) = algebraMap E Ω e := fun e ↦
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hn _ (hYE e)
    let n' := liftE F n hnE
    have hn' : n' ∈ N := hN n' (by rw [res_liftE]; exact hn)
    have hgn : g * n'⁻¹ ∈ Hp.comap (res F (E := E) (Ω := Ω)) := by
      rw [Subgroup.mem_comap, map_mul, map_inv, res_liftE, ← hhn, mul_inv_cancel_right]
      exact hh
    have := Subgroup.mul_mem_sup hgn hn'
    simpa using this

end Descend2

section Conj

open ComplexConjugate Polynomial

theorem conj_mem_range {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (j : Ω →+* ℂ)
    (hj : ∀ x : F, conj (j (algebraMap F Ω x)) = j (algebraMap F Ω x)) (x : Ω) :
    ∃ y : Ω, j y = conj (j x) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  set p := minpoly F x with hp
  set p' : Polynomial Ω := p.map (algebraMap F Ω) with hp'
  have hp'0 : p' ≠ 0 := (minpoly.monic hx).map _ |>.ne_zero
  have hcard : p'.roots.card = p'.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroots := roots_map_of_injective_of_card_eq_natDegree j.injective hcard
  have hq0 : p'.map j ≠ 0 := ((minpoly.monic hx).map _ |>.map j).ne_zero
  have hcoef : (p'.map j).map (starRingEnd ℂ) = p'.map j := by
    simp only [hp', Polynomial.map_map]
    refine congrArg (fun f : F →+* ℂ => Polynomial.map f p) ?_
    ext r
    simpa using hj r
  have hroot : (p'.map j).IsRoot (conj (j x)) := by
    have h0 : (p'.map j).eval (j x) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hp', Polynomial.eval_map_algebraMap, hp, minpoly.aeval,
        map_zero]
    have := congrArg (starRingEnd ℂ) h0
    rw [map_zero, ← Polynomial.eval_map_apply, hcoef] at this
    exact this
  have hmem : conj (j x) ∈ (p'.map j).roots := (Polynomial.mem_roots hq0).2 hroot
  rw [← hroots, Multiset.mem_map] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  exact ⟨y, hy⟩

theorem exists_conj {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (j : Ω →+* ℂ)
    (hj : ∀ x : F, conj (j (algebraMap F Ω x)) = j (algebraMap F Ω x)) :
    ∃ c : Ω ≃ₐ[F] Ω, ∀ x, j (c x) = conj (j x) := by
  choose g hg using conj_mem_range j hj
  let f : Ω →ₐ[F] Ω :=
    { toFun := g
      map_one' := j.injective (by simp [hg])
      map_mul' := fun x y ↦ j.injective (by rw [hg, map_mul, map_mul, map_mul, hg, hg])
      map_zero' := j.injective (by simp [hg])
      map_add' := fun x y ↦ j.injective (by rw [hg, map_add, map_add, map_add, hg, hg])
      commutes' := fun r ↦ j.injective (by rw [hg, hj]) }
  have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  exact ⟨AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective f), fun x ↦ hg x⟩

end Conj

section CM

open ComplexConjugate

theorem isTotallyReal_fixedField {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F]
    (Hp : Subgroup (Ω ≃ₐ[F] Ω)) (hc : ∀ (c : Ω ≃ₐ[F] Ω) (j : Ω →+* ℂ), (∀ x, j (c x) = conj (j x)) → c ∈ Hp) :
    IsTotallyReal (IntermediateField.fixedField Hp) := by
  let K := IntermediateField.fixedField Hp
  constructor
  intro v
  let φ : K →+* ℂ := v.embedding
  let _ : Algebra K ℂ := φ.toAlgebra
  have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := F) K
  let j : Ω →+* ℂ := (IsAlgClosed.lift : Ω →ₐ[K] ℂ).toRingHom
  have hjK : ∀ y : K, j (y : Ω) = φ y := fun y ↦ (IsAlgClosed.lift : Ω →ₐ[K] ℂ).commutes y
  have hjF : ∀ x : F, conj (j (algebraMap F Ω x)) = j (algebraMap F Ω x) := by
    intro x
    have hr := IsTotallyReal.isReal (InfinitePlace.mk (j.comp (algebraMap F Ω)))
    rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff] at hr
    have := RingHom.congr_fun hr x
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  obtain ⟨c, hcj⟩ := exists_conj j hjF
  have hcH : c ∈ Hp := hc c j hcj
  rw [← v.mk_embedding, InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
  ext y
  rw [ComplexEmbedding.conjugate_coe_eq]
  show conj (φ y) = φ y
  rw [← hjK, ← hcj]
  congr 1
  exact (IntermediateField.mem_fixedField_iff _ _).1 y.2 c hcH

theorem cm_of_descend (F : Type*) {E Ω : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω]
    [CharZero Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω] [IsScalarTower F E Ω] [IsTotallyReal F] [IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] [IsAlgClosure F Ω] [IsAlgClosure E Ω]
    (Hp : Subgroup (Ω ≃ₐ[F] Ω)) (hHo : IsOpen (Hp : Set (Ω ≃ₐ[F] Ω)))
    (hc : ∀ (c : Ω ≃ₐ[F] Ω) (j : Ω →+* ℂ), (∀ x, j (c x) = conj (j x)) → c ∈ Hp)
    (Y : IntermediateField F Ω) (hYE : ∀ e : E, algebraMap E Ω e ∈ Y) (hsup : Hp ⊔ Y.fixingSubgroup = ⊤) :
    FiniteDimensional E (IntermediateField.fixedField (Hp.comap (res F (E := E) (Ω := Ω)))) ∧
      IsCMField (IntermediateField.fixedField (Hp.comap (res F (E := E) (Ω := Ω)))) := by
  classical
  have : IsGalois F Ω := inferInstance
  have : IsGalois E Ω := inferInstance
  have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hint : ∀ x : Ω, IsIntegral F x → IsIntegral E x := fun x hx ↦ hx.tower_top
  set H := Hp.comap (res F (E := E) (Ω := Ω)) with hH
  have hHo' : IsOpen (H : Set (Ω ≃ₐ[E] Ω)) := hHo.preimage (continuous_res F hint)
  let Hc : ClosedSubgroup (Ω ≃ₐ[E] Ω) := ⟨H, Subgroup.isClosed_of_isOpen H hHo'⟩
  have hfixH : (IntermediateField.fixedField H).fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField Hc
  have hfin : FiniteDimensional E (IntermediateField.fixedField H) :=
    (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfixH]; exact hHo')
  refine ⟨hfin, ?_⟩
  let Hpc : ClosedSubgroup (Ω ≃ₐ[F] Ω) := ⟨Hp, Subgroup.isClosed_of_isOpen Hp hHo⟩
  have hfixHp : (IntermediateField.fixedField Hp).fixingSubgroup = Hp := InfiniteGalois.fixingSubgroup_fixedField Hpc
  set Ep := IntermediateField.fixedField Hp with hEp
  set E' := IntermediateField.fixedField H with hE'
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  obtain ⟨α, hα⟩ : ∃ α : E, α ∉ Set.range (algebraMap F E) := by
    by_contra! h
    have hbt : (⊥ : IntermediateField F E) = ⊤ := by
      rw [eq_top_iff]; intro x _; rw [IntermediateField.mem_bot]; exact h x
    rw [IntermediateField.bot_eq_top_iff_finrank_eq_one, h2] at hbt
    norm_num at hbt
  have htop : IntermediateField.adjoin F {α} = ⊤ := by
    have := (IntermediateField.isSimpleOrder_of_finrank_prime F E (h2 ▸ Nat.prime_two)).eq_bot_or_eq_top
      (IntermediateField.adjoin F {α})
    refine this.resolve_left fun h ↦ hα ?_
    have hm : α ∈ IntermediateField.adjoin F {α} := IntermediateField.mem_adjoin_simple_self F α
    rw [h, IntermediateField.mem_bot] at hm
    exact hm
  have hαint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hfixE : ∀ σ : Ω ≃ₐ[F] Ω, σ (algebraMap E Ω α) = algebraMap E Ω α →
      ∀ e : E, σ (algebraMap E Ω e) = algebraMap E Ω e := by
    intro σ hσ e
    have hadj : Algebra.adjoin F {α} = ⊤ := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun x hx ↦ ?_), htop,
        IntermediateField.top_toSubalgebra]
      rw [Set.mem_singleton_iff.1 hx]; exact hαint.isAlgebraic
    have := AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := (σ : Ω →ₐ[F] Ω).comp (IsScalarTower.toAlgHom F E Ω))
      (φ₂ := IsScalarTower.toAlgHom F E Ω) (by
        intro x hx; rw [Set.mem_singleton_iff.1 hx]; simpa using hσ)
    simpa using congrArg (fun f ↦ f e) this
  set a := algebraMap E Ω α with ha
  have haEp : a ∉ Ep := by
    intro haE
    have hle : Hp ⊔ Y.fixingSubgroup ≤ MulAction.stabilizer (Ω ≃ₐ[F] Ω) a := by
      refine sup_le (fun σ hσ ↦ ?_) (fun σ hσ ↦ ?_)
      · rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
        exact (IntermediateField.mem_fixedField_iff _ _).1 haE σ hσ
      · rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ a (hYE α)
    have hall : ∀ σ : Ω ≃ₐ[F] Ω, σ a = a := by
      intro σ
      have := hle (hsup ▸ Subgroup.mem_top σ)
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed a).2 hall
    apply hα
    refine ⟨y, (algebraMap E Ω).injective ?_⟩
    rw [← IsScalarTower.algebraMap_apply, hy]
  have haF : IsIntegral F a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  have haint : IsIntegral Ep a := haF.tower_top
  have hdegF : (minpoly F a).natDegree = 2 := by
    rw [ha, ← IsScalarTower.toAlgHom_apply F E Ω, minpoly.algHom_eq _ (algebraMap E Ω).injective,
      ← IntermediateField.adjoin.finrank hαint, htop, IntermediateField.finrank_top', h2]
  have hdeg : (minpoly Ep a).natDegree = 2 := by
    have hdvd := minpoly.dvd_map_of_isScalarTower F Ep a
    have hle : (minpoly Ep a).natDegree ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd ((minpoly.monic haF).map (algebraMap F Ep)).ne_zero
      rwa [Polynomial.natDegree_map, hdegF] at this
    have hne1 : (minpoly Ep a).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]
      rintro ⟨y, hy⟩
      exact haEp (by rw [← hy]; exact y.2)
    have hpos := minpoly.natDegree_pos haint
    omega
  have hfinrank : Module.finrank Ep (IntermediateField.adjoin Ep {a}) = 2 := by
    rw [IntermediateField.adjoin.finrank haint, hdeg]
  have hEpE' : ∀ y ∈ Ep, y ∈ E' := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff] at hy ⊢
    intro σ hσ
    exact hy (res F σ) hσ
  have haE' : a ∈ E' := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ _
    exact σ.commutes α
  have hset : ∀ x : Ω, x ∈ E' ↔ x ∈ IntermediateField.adjoin Ep {a} := by
    intro x
    constructor
    · intro hx
      let L₁ := (IntermediateField.adjoin Ep {a}).restrictScalars F
      have hx' : x ∈ IntermediateField.fixedField L₁.fixingSubgroup := by
        rw [IntermediateField.mem_fixedField_iff]
        intro σ hσ
        have hσEp : σ ∈ Hp := by
          rw [← hfixHp, IntermediateField.mem_fixingSubgroup_iff]
          intro y hy
          exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ y
            (IntermediateField.algebraMap_mem (IntermediateField.adjoin Ep {a}) (⟨y, hy⟩ : Ep))
        have hσa : σ a = a := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ a
          (IntermediateField.mem_adjoin_simple_self Ep a)
        have hσE := hfixE σ hσa
        have hmem : liftE F σ hσE ∈ H := by
          rw [hH, Subgroup.mem_comap, res_liftE]; exact hσEp
        exact (IntermediateField.mem_fixedField_iff _ _).1 hx _ hmem
      rwa [InfiniteGalois.fixedField_fixingSubgroup] at hx'
    · intro hx
      let K' : IntermediateField Ep Ω := E'.toSubfield.toIntermediateField (fun y ↦ hEpE' y.1 y.2)
      have hle : IntermediateField.adjoin Ep {a} ≤ K' := IntermediateField.adjoin_simple_le_iff.2 haE'
      exact hle hx
  let ι : Ep →+* E' :=
    { toFun := fun y ↦ ⟨y, hEpE' y y.2⟩, map_one' := rfl, map_mul' := fun _ _ ↦ rfl, map_zero' := rfl,
      map_add' := fun _ _ ↦ rfl }
  let _ : Algebra Ep E' := ι.toAlgebra
  let jeq : IntermediateField.adjoin Ep {a} ≃+* E' :=
    { toFun := fun y ↦ ⟨y, (hset y).2 y.2⟩, invFun := fun y ↦ ⟨y, (hset y).1 y.2⟩,
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl, map_mul' := fun _ _ ↦ rfl, map_add' := fun _ _ ↦ rfl }
  have hq : Module.finrank Ep E' = 2 := by
    rw [← hfinrank]
    exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl Ep) jeq (by ext; rfl)).symm
  have : IsTotallyReal Ep := isTotallyReal_fixedField Hp hc
  have : FiniteDimensional ℚ E' := Module.Finite.trans E E'
  have : Algebra.IsIntegral ℚ E' := Algebra.IsIntegral.of_finite ℚ E'
  have : IsTotallyComplex E' := isTotallyComplex_of_algebra E E'
  have : Algebra.IsQuadraticExtension Ep E' := { toFree := Module.Free.of_divisionRing Ep E', finrank_eq_two' := hq }
  exact IsCMField.ofCMExtension Ep E'

end CM

section Gen

theorem exists_injective_fin {α : Type*} : ∀ (n : ℕ) (P : Fin n → α → Prop),
    (∀ i (S : Set α), S.Finite → ∃ a ∉ S, P i a) → ∀ S₀ : Set α, S₀.Finite →
    ∃ f : Fin n → α, Function.Injective f ∧ ∀ i, f i ∉ S₀ ∧ P i (f i)
  | 0, _, _, _, _ => ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | n + 1, P, h, S₀, hS₀ => by
    obtain ⟨f, hf, hfP⟩ := exists_injective_fin n (fun i => P i.succ) (fun i => h i.succ) S₀ hS₀
    obtain ⟨a, ha, haP⟩ := h 0 (S₀ ∪ Set.range f) (hS₀.union (Set.finite_range f))
    refine ⟨Fin.cons a f, Fin.cons_injective_iff.2 ⟨fun h' => ha (Or.inr h'), hf⟩, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨fun h' => ha (Or.inl h'), haP⟩
    · simpa only [Fin.cons_succ] using hfP j

theorem exists_injective_avoid {α ι : Type*} [Finite ι] (P : ι → α → Prop)
    (h : ∀ i (S : Set α), S.Finite → ∃ a ∉ S, P i a) (S₀ : Set α) (hS₀ : S₀.Finite) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∉ S₀ ∧ P i (f i) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨f, hf, hP⟩ := exists_injective_fin n (fun k => P (e.symm k)) (fun k => h _) S₀ hS₀
  refine ⟨f ∘ e, hf.comp e.injective, fun i => ?_⟩
  simpa using hP (e i)

end Gen

section Sgn

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem aut_eq_one_or (g : E ≃ₐ[maximalRealSubfield E] E) : g = 1 ∨ g = IsCMField.complexConj E := by
  have hg : g ∈ Subgroup.zpowers (IsCMField.complexConj E) := by
    rw [IsCMField.zpowers_complexConj_eq_top]; exact Subgroup.mem_top g
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [← zpow_mod_orderOf, IsCMField.orderOf_complexConj]
  push_cast
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]

theorem complexConj_mul_self : IsCMField.complexConj E * IsCMField.complexConj E = 1 := by
  ext x; simp

open Classical in

def sgn : (E ≃ₐ[maximalRealSubfield E] E) →* ℂˣ where
  toFun g := if g = 1 then 1 else -1
  map_one' := if_pos rfl
  map_mul' g h := by
    have hc := IsCMField.complexConj_ne_one E
    rcases aut_eq_one_or E g with rfl | rfl <;> rcases aut_eq_one_or E h with rfl | rfl <;>
      simp [hc, complexConj_mul_self]

theorem sgn_eq_one_iff (g : E ≃ₐ[maximalRealSubfield E] E) : sgn E g = 1 ↔ g = 1 := by
  classical
  simp only [sgn, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    intro h'
    have := congrArg Units.val h'
    norm_num at this

end Sgn

end PositivityTheory.Pf1.CLGD.K.CMDescent

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC PositivityTheory.Pf1.CLGD.DescRes

namespace PositivityTheory.Pf1.CLGD.K.CMDescent

open ComplexConjugate

theorem real_on {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] (j : Ω →+* ℂ)
    (x : F) : conj (j (algebraMap F Ω x)) = j (algebraMap F Ω x) := by
  have hr := IsTotallyReal.isReal (InfinitePlace.mk (j.comp (algebraMap F Ω)))
  rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff] at hr
  have := RingHom.congr_fun hr x
  simpa [ComplexEmbedding.conjugate_coe_eq] using this

variable {F E Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Field Ω]
  [Algebra F E] [Algebra E Ω] [Algebra F Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsAlgClosure F Ω] [CharZero Ω]

theorem split_of (hFE : ∀ f : F, algebraMap F E f ∈ maximalRealSubfield E)
    (ψ : G F Ω →* ℂˣ) (hψo : IsOpen (ψ.ker : Set (G F Ω)))
    (hψc : ∀ (c : G F Ω) (j : Ω →+* ℂ), (∀ x, j (c x) = conj (j x)) → ψ c = 1)
    (A : ValuationSubring Ω)
    (hψA : ∀ σ ∈ Dec (F := F) A, ψ σ = 1 → ∀ e : E, σ (algebraMap E Ω e) = algebraMap E Ω e)
    (X : CMExt E Ω) (hX : (resG E (E' := X.M) (Ω := Ω)).range = ψ.ker.comap (res F (E := E) (Ω := Ω)))
    (w' : HeightOneSpectrum (𝓞 X.M)) (hw' : IsPlaceOver A w') : IsSplitAt w' := by
  classical
  by_contra hns
  let M := X.M
  let P := maximalRealSubfield M
  let c := IsCMField.complexConj M
  let cO := IsCMField.ringOfIntegersComplexConj M
  have hcc : ∀ m : M, c (c m) = m := IsCMField.complexConj_apply_apply M
  have hcO : ∀ x : 𝓞 M, ((cO x : 𝓞 M) : M) = c x := IsCMField.coe_ringOfIntegersComplexConj M
  have hcOO : ∀ x : 𝓞 M, cO (cO x) = x := fun x => RingOfIntegers.ext (by rw [hcO, hcO, hcc])

  let u : HeightOneSpectrum (𝓞 M) :=
    { asIdeal := w'.asIdeal.comap cO
      isPrime := Ideal.IsPrime.comap cO
      ne_bot := by
        intro h
        apply w'.ne_bot
        rw [eq_bot_iff]
        intro x hx
        have hx' : cO x ∈ w'.asIdeal.comap cO := by rw [Ideal.mem_comap, hcOO]; exact hx
        rw [h, Ideal.mem_bot] at hx'
        rw [Ideal.mem_bot, ← hcOO x, hx', map_zero] }
  have hu : u = w' := by
    by_contra hne
    refine hns ⟨u, hne, ?_⟩
    ext x
    show cO (algebraMap (𝓞 P) (𝓞 M) x) ∈ w'.asIdeal ↔ algebraMap (𝓞 P) (𝓞 M) x ∈ w'.asIdeal
    rw [cO.commutes]
  have hmem : ∀ x : 𝓞 M, cO x ∈ w'.asIdeal ↔ x ∈ w'.asIdeal := fun x =>
    Eq.to_iff (congrArg (fun v : HeightOneSpectrum (𝓞 M) => x ∈ v.asIdeal) hu)

  haveI : IsScalarTower P M Ω := inferInstance
  haveI : IsAlgClosure P Ω := IsAlgClosure.ofAlgebraic P M Ω
  haveI : Normal P Ω := IsAlgClosure.normal P Ω
  let τ : Ω ≃ₐ[P] Ω := c.liftNormal Ω
  have hτ : ∀ m : M, τ (algebraMap M Ω m) = algebraMap M Ω (c m) := fun m => AlgEquiv.liftNormal_commutes c Ω m
  have hA' : IsPlaceOver (τ • A) w' := by
    intro x
    rw [ReciprocityTheory.Gal.smul_valuation_lt_one_iff]
    have : (τ⁻¹ : Ω ≃ₐ[P] Ω) (algebraMap M Ω x) = algebraMap M Ω ((cO x : 𝓞 M) : M) := by
      rw [hcO, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, hτ, hcc]
    rw [this, hw' (cO x), hmem]
  obtain ⟨ρ, hρ⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver (F := M) hw' hA'
  let ρP : Ω ≃ₐ[P] Ω := ρ.restrictScalars P
  let σ : Ω ≃ₐ[P] Ω := ρP⁻¹ * τ
  have hσA : σ • A = A := by
    have h1 : ρP • A = ρ • A := by
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    rw [mul_smul, ← hρ, ← h1, inv_smul_smul]
  have hσM : ∀ m : M, σ (algebraMap M Ω m) = algebraMap M Ω (c m) := by
    intro m
    show ρP⁻¹ (τ (algebraMap M Ω m)) = _
    rw [hτ, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact (ρ.commutes (c m)).symm

  have hPF : ∀ f : F, ∃ p : P, algebraMap F Ω f = algebraMap P Ω p := by
    intro f
    refine ⟨⟨algebraMap E M (algebraMap F E f), ?_⟩, ?_⟩
    · rw [mem_maximalRealSubfield_iff]
      intro φ
      have h := hFE f
      rw [mem_maximalRealSubfield_iff] at h
      exact h (φ.comp (algebraMap E M))
    · show algebraMap F Ω f = algebraMap M Ω (algebraMap E M (algebraMap F E f))
      rw [← IsScalarTower.algebraMap_apply E M Ω, ← IsScalarTower.algebraMap_apply F E Ω]
  let σF : G F Ω :=
    { σ.toRingEquiv with
      commutes' := fun f => by
        obtain ⟨p, hp⟩ := hPF f
        show σ (algebraMap F Ω f) = algebraMap F Ω f
        rw [hp]; exact σ.commutes p }
  have hσFD : σF ∈ Dec (F := F) A := by
    have h1 : σF • A = σ • A := by
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    exact ReciprocityTheory.Gal.mem_Dec.2 (h1.trans hσA)

  have hfix : ∀ x ∈ IntermediateField.fixedField ψ.ker, σF x = x := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hM' : ∀ ρ' : G M Ω, ρ' x = x := by
      intro ρ'
      have h1 : resG E ρ' ∈ (resG E (E' := M) (Ω := Ω)).range := ⟨ρ', rfl⟩
      rw [hX, Subgroup.mem_comap] at h1
      exact hx _ h1
    obtain ⟨y, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := M) x).2 hM'
    have hy : y ∈ P := by
      rw [mem_maximalRealSubfield_iff]
      intro φ
      letI : Algebra M ℂ := φ.toAlgebra
      haveI : Algebra.IsAlgebraic M Ω := IsAlgClosure.isAlgebraic
      let j : Ω →+* ℂ := (IsAlgClosed.lift : Ω →ₐ[M] ℂ).toRingHom
      have hj : j (algebraMap M Ω y) = φ y := (IsAlgClosed.lift : Ω →ₐ[M] ℂ).commutes y
      obtain ⟨c', hc'⟩ := exists_conj (F := F) j (real_on j)
      have h1 : c' ∈ ψ.ker := hψc c' j hc'
      have h2 := hc' (algebraMap M Ω y)
      rw [hx c' h1, hj] at h2
      exact h2.symm
    show σ (algebraMap M Ω y) = algebraMap M Ω y
    exact σ.commutes (⟨y, hy⟩ : P)
  have hker : σF ∈ ψ.ker := by
    have hcl : IsClosed (ψ.ker : Set (G F Ω)) := Subgroup.isClosed_of_isOpen _ hψo
    have hfs := InfiniteGalois.fixingSubgroup_fixedField (⟨ψ.ker, hcl⟩ : ClosedSubgroup (G F Ω))
    exact hfs.le ((IntermediateField.mem_fixingSubgroup_iff _ _).2 hfix)
  have hE := hψA σF hσFD hker
  let σE : G E Ω := liftE F σF hE
  have hσE : σE ∈ (resG E (E' := M) (Ω := Ω)).range := by
    rw [hX, Subgroup.mem_comap, res_liftE]; exact hker
  obtain ⟨ρ', hρ'⟩ := hσE
  apply IsCMField.complexConj_ne_one M
  ext m
  have h1 := hσM m
  have h2 : σ (algebraMap M Ω m) = algebraMap M Ω m := by
    have e := congrArg (fun g : G E Ω => g (algebraMap M Ω m)) hρ'
    exact e.symm.trans (ρ'.commutes m)
  rw [AlgEquiv.one_apply]
  exact (algebraMap M Ω).injective (h1.symm.trans h2)

end PositivityTheory.Pf1.CLGD.K.CMDescent

namespace PositivityTheory.Pf1.CLGD.K

open ComplexConjugate CMDescent

theorem cm_descent_avoiding_field : SimplePoleRescaling := by
  unfold SimplePoleRescaling FieldSplit
  intro hK1 E Ω _ _ _ _ _ _ A w hA N hNn hNo
  classical
  let F := maximalRealSubfield E
  haveI : IsAlgClosure F Ω := IsAlgClosure.ofAlgebraic F E Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hint : ∀ x : Ω, IsIntegral F x → IsIntegral E x := fun x hx ↦ hx.tower_top

  obtain ⟨K₁, hK₁, hK₁N⟩ := CMDescent.exists_finiteDimensional_fixingSubgroup_le N hNo
  let Y₀ : IntermediateField F Ω := K₁.restrictScalars F
  haveI : IsScalarTower F E K₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hK₁F : Module.Finite F K₁ := Module.Finite.trans E K₁
  haveI : FiniteDimensional F Y₀ := hK₁F
  let Y := IntermediateField.normalClosure F Y₀ Ω
  haveI : FiniteDimensional F Y := normalClosure.is_finiteDimensional F Y₀ Ω
  haveI : IsGalois F Y := IsGalois.normalClosure F Y₀ Ω
  have hY₀Y : Y₀ ≤ Y := IntermediateField.le_normalClosure Y₀
  have hYE : ∀ e : E, algebraMap E Ω e ∈ Y := fun e ↦ hY₀Y (K₁.algebraMap_mem e)
  have hNY : ∀ σ : Ω ≃ₐ[E] Ω, CMDescent.res F σ ∈ Y.fixingSubgroup → σ ∈ N := by
    intro σ hσ
    refine hK₁N ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ ?_)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x (hY₀Y hx)

  let ε : G F Ω →* ℂˣ := (sgn E).comp (AlgEquiv.restrictNormalHom E)
  have hε : ∀ σ : G F Ω, ε σ = 1 ↔ ∀ e : E, σ (algebraMap E Ω e) = algebraMap E Ω e := by
    intro σ
    have key : ∀ e, algebraMap E Ω (AlgEquiv.restrictNormalHom E σ e) = σ (algebraMap E Ω e) :=
      fun e => AlgEquiv.restrictNormal_commutes σ E e
    rw [MonoidHom.comp_apply, sgn_eq_one_iff]
    constructor
    · intro h e
      rw [← key, h, AlgEquiv.one_apply]
    · intro h
      exact AlgEquiv.ext fun e => (algebraMap E Ω).injective (by rw [key, h e, AlgEquiv.one_apply])
  have hεo : IsOpen (ε.ker : Set (G F Ω)) :=
    Subgroup.isOpen_mono (fun σ hσ => MonoidHom.mem_ker.2 ((hε σ).2 fun e =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (hYE e))) (IntermediateField.fixingSubgroup_isOpen Y)

  let v : HeightOneSpectrum (𝓞 F) := w.under (𝓞 F)
  have hAv : IsPlaceOver A v := fun x => hA (algebraMap (𝓞 F) (𝓞 E) x)

  have hcheb : ∀ (g : Y ≃ₐ[F] Y) (S : Set (HeightOneSpectrum (𝓞 F))), S.Finite →
      ∃ p ∉ S, ∃ B : ValuationSubring Ω, IsPlaceOver B p ∧
        ∃ σ ∈ Dec (F := F) B, AlgEquiv.restrictNormalHom Y σ = g := by
    intro g S hS
    obtain ⟨p, hp, -, B, hB, -, σ, hσ, hg⟩ := GlobalTheory.Published.chebotarevDegreeOne' F Ω Y g S hS
    exact ⟨p, hp, B, hB, σ, hσ.1, hg⟩
  obtain ⟨f, hfi, hf⟩ := exists_injective_avoid
    (fun (g : Y ≃ₐ[F] Y) p => ∃ B : ValuationSubring Ω, IsPlaceOver B p ∧
      ∃ σ ∈ Dec (F := F) B, AlgEquiv.restrictNormalHom Y σ = g)
    (fun g S hS => hcheb g S hS) {v} (Set.finite_singleton v)
  choose B hB σg hσgD hσg using fun g => (hf g).2

  let S := Option (Y ≃ₐ[F] Y)
  let vS : S → HeightOneSpectrum (𝓞 F) := fun s => s.elim v f
  let AS : S → ValuationSubring Ω := fun s => s.elim A B
  have hvS : Function.Injective vS := by
    rintro (_ | g) (_ | g') h
    · rfl
    · change v = f g' at h
      exact ((hf g').1 (Set.mem_singleton_iff.2 h.symm)).elim
    · change f g = v at h
      exact ((hf g).1 (Set.mem_singleton_iff.2 h)).elim
    · change f g = f g' at h
      exact congrArg some (hfi h)
  have hAS : ∀ s, IsPlaceOver (AS s) (vS s) := by
    rintro (_ | g)
    · exact hAv
    · exact hB g
  let χ : ∀ s, Dec (F := F) (AS s) →* ℂˣ := fun s =>
    Option.rec (motive := fun s => Dec (F := F) (AS s) →* ℂˣ) (ε.comp (Dec (F := F) A).subtype) (fun _ => 1) s
  have hχ : ∀ s, IsOpen ((χ s).ker : Set (Dec (F := F) (AS s))) := by
    rintro (_ | g)
    · have e : (((ε.comp (Dec (F := F) A).subtype).ker : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) =
          Subtype.val ⁻¹' (ε.ker : Set (G F Ω)) := by
        ext x; simp [MonoidHom.mem_ker]
      show IsOpen (((ε.comp (Dec (F := F) A).subtype).ker : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A))
      rw [e]
      exact hεo.preimage continuous_subtype_val
    · show IsOpen (((1 : Dec (F := F) (B g) →* ℂˣ).ker : Subgroup _) : Set (Dec (F := F) (B g)))
      rw [MonoidHom.ker_one, Subgroup.coe_top]
      exact isOpen_univ
  obtain ⟨ψ, hψo, hψχ, hψR⟩ := hK1 F Ω S vS AS hvS hAS χ hχ
  have hψc : ∀ (c : G F Ω) (j : Ω →+* ℂ), (∀ x, j (c x) = conj (j x)) → ψ c = 1 := fun c j hj =>
    hψR _ (IsTotallyReal.isReal _) c ⟨j, hj, rfl⟩
  have hψA : ∀ σ ∈ Dec (F := F) A, ψ σ = 1 → ∀ e : E, σ (algebraMap E Ω e) = algebraMap E Ω e := by
    intro σ hσ h1
    have h2 : ψ σ = ε σ := hψχ none ⟨σ, hσ⟩
    rw [h1] at h2
    exact (hε σ).1 h2.symm
  have hsup : ψ.ker ⊔ Y.fixingSubgroup = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : ψ (σg (AlgEquiv.restrictNormalHom Y x)) = 1 :=
      hψχ (some (AlgEquiv.restrictNormalHom Y x)) ⟨_, hσgD _⟩
    have h2 : (σg (AlgEquiv.restrictNormalHom Y x))⁻¹ * x ∈ Y.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, hσg, inv_mul_cancel]
    have := Subgroup.mul_mem_sup (MonoidHom.mem_ker.2 h1) h2
    simpa using this
  have hsolv : Group.IsSolvable (G F Ω ⧸ ψ.ker) := isSolvable_of_comm fun a b =>
    QuotientGroup.kerLift_injective ψ (by rw [map_mul, map_mul, mul_comm])
  obtain ⟨hHo, -, hHsup⟩ := descend F hint Y hYE ψ.ker hψo hsolv hsup N hNY
  refine ⟨ψ.ker.comap (CMDescent.res F), ⟨inferInstance, hHo, ?_, ?_⟩, hHsup, ?_, ?_⟩
  ·
    let φ : G E Ω →* ℂˣ := ψ.comp (CMDescent.res F)
    have hφ : ∀ x, x ∈ ψ.ker.comap (CMDescent.res F) ↔ φ x = 1 := fun x => by
      simp [φ, MonoidHom.mem_ker]
    have hfinq : Finite (G E Ω ⧸ φ.ker) := by
      rw [← MonoidHom.comap_ker]
      exact Subgroup.quotient_finite_of_isOpen _ hHo
    haveI : Finite φ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).toEquiv
    haveI : IsCyclic φ.range := isCyclic_subgroup_units φ.range
    obtain ⟨⟨z, g, rfl⟩, hgen⟩ := IsCyclic.exists_generator (α := φ.range)
    refine ⟨g, eq_top_iff.2 fun x _ => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨φ x, x, rfl⟩)
    have hk' : φ g ^ k = φ x := by simpa using congrArg Subtype.val hk
    have hmem : x * (g ^ k)⁻¹ ∈ ψ.ker.comap (CMDescent.res F) := by
      rw [hφ, map_mul, map_inv, map_zpow, hk', mul_inv_cancel]
    have := Subgroup.mul_mem_sup hmem (Subgroup.zpow_mem_zpowers g k)
    simpa using this
  ·
    intro L hL
    let Hp : Subgroup (G F Ω) := ψ.ker ⊔ L.fixingSubgroup.map (CMDescent.res F)
    have hHp : Hp.comap (CMDescent.res F) = L.fixingSubgroup := by
      apply le_antisymm
      · intro x hx
        rw [Subgroup.mem_comap] at hx
        obtain ⟨k, hk, m, hm, hkm⟩ := Subgroup.mem_sup_of_normal_left.1 hx
        obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hm
        have h1 : x * l⁻¹ ∈ ψ.ker.comap (CMDescent.res F) := by
          rw [Subgroup.mem_comap, map_mul, map_inv, ← hkm, mul_inv_cancel_right]
          exact hk
        have := L.fixingSubgroup.mul_mem (hL h1) hl
        simpa using this
      · intro x hx
        exact Subgroup.mem_comap.2 (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ hx))
    have hsupp : Hp ⊔ Y.fixingSubgroup = ⊤ := by
      rw [eq_top_iff, ← hsup]
      exact sup_le_sup_right le_sup_left _
    have hcm := (cm_of_descend F Hp (Subgroup.isOpen_mono le_sup_left hψo)
      (fun c j hj => Subgroup.mem_sup_left (MonoidHom.mem_ker.2 (hψc c j hj))) Y hYE hsupp).2
    rw [hHp, InfiniteGalois.fixedField_fixingSubgroup] at hcm
    exact hcm
  ·
    intro σ hσ
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    have h1 : CMDescent.res F σ ∈ Dec (F := F) A := res_mem_decompositionSubgroup F hσ
    have h2 : ψ (CMDescent.res F σ) = ε (CMDescent.res F σ) := hψχ none ⟨CMDescent.res F σ, h1⟩
    rw [h2, hε]
    intro e
    exact σ.commutes e
  ·
    intro X hX w' hw'
    exact split_of (F := F) (fun f => f.2) ψ hψo hψc A hψA X hX w' hw'
end PositivityTheory.Pf1.CLGD.K
