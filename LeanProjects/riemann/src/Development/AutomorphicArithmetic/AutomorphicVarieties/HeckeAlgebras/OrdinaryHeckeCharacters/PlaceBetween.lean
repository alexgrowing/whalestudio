import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwiningGlOfUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.under (𝓞 K) = v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

open scoped Pointwise in
private theorem place_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (g : G F Ω) {A : ValuationSubring Ω}
    {v : W.Plc F} (h : IsPlaceOver A v) : IsPlaceOver (g • A) v := fun x => by
  have e : ∀ y : Ω, (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 :=
    UpperTheory.V.val_lt_one (σ := g.toRingEquiv) (fun _ => ValuationSubring.smul_mem_pointwise_smul_iff (g := g))
  rw [← h x, ← e, AlgEquiv.commutes]

open scoped Pointwise in
private theorem w_split {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} (V : s.Lev) (v : Vl l L) : IsSplitAt (s.w v.1) := by
  have hc : s.c ∉ (W.resP L Ω).range := fun h => by
    have h1 := (V.hη _).2 h
    rw [V.η_c] at h1
    exact absurd h1 (by decide)
  obtain ⟨u, hu, hu'⟩ := place_between (L := L) (place_smul s.c (s.hA v.1))
  by_cases h : u = s.w v.1
  · exfalso
    subst h
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (s.hw v.1) hu
    have h2 : s.c⁻¹ * W.resP L Ω σ ∈ Dec (F := Lp L) (s.A v.1) := by
      change (s.c⁻¹ * W.resP L Ω σ) • s.A v.1 = s.A v.1
      have h3 : W.resP L Ω σ • s.A v.1 = s.c • s.A v.1 := hσ
      rw [mul_smul, h3, inv_smul_smul]
    have h4 := s.split v.1 (Or.inl v.2) h2
    have h5 := mul_mem h4 (inv_mem (⟨σ, rfl⟩ : W.resP L Ω σ ∈ (W.resP L Ω).range))
    rw [mul_inv_cancel_right] at h5
    exact hc (inv_mem_iff.1 h5)
  · exact ⟨u, h, hu'.trans (w_under s v.1).symm⟩

section Grp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private theorem cLoc_conj {w u : Plc L} (hw : IsSplitAt w)
    (x : UA L n) (h1 : cLoc w x = 1) (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) : cLoc u x = 1 := by
  have h2 : GlobalTheory.DefU.LocRet.ret w n x = 1 :=
    GlobalTheory.SplitPts.eq_one_of_cLoc hw _ ((GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl x).trans h1)
  have h3 : cLoc u (GlobalTheory.DefU.LocRet.ret w n x : UA L n) = cLoc u x := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq hu x
  rw [← h3, h2]
  exact map_one _

private theorem mem_inf_of {x : UA L n} (h : ∀ u, cLoc u x = 1) : x ∈ infU L n :=
  Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext L fun u => by
    have := congrArg (fun g : GL (Fin n) (u.adicCompletion L) => g.val i j) (h u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    by_cases hij : i = j <;> simp [hij])

private theorem cLoc_inf {x : UA L n} (h : x ∈ infU L n) (u : Plc L) : cLoc u x = 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := h
  have e : cLoc u x = Matrix.GeneralLinearGroup.map (pLoc L u) (Matrix.GeneralLinearGroup.map (pFin L) x.1) := Units.ext rfl
  rw [e, h1, map_one]

private theorem exists_fin : ∃ p : UA L n → finU L n, Continuous p ∧ p 1 = 1 ∧ ∀ x u, cLoc u (p x : UA L n) = cLoc u x := by
  have hfin : Continuous (finGL L n) :=
    Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
      (continuous_const.prodMk continuous_id : Continuous fun x : Af L => ((0, x) : InfiniteAdeleRing L × Af L))))
  refine ⟨fun x => ⟨⟨finGL L n (Matrix.GeneralLinearGroup.map (pFin L) x.1),
    GlobalTheory.SplitPts.finGL_mem_UA _ fun u => GlobalTheory.SplitPts.comp_eq x u⟩, MonoidHom.mem_ker.2 (pInf_finGL _)⟩,
    Continuous.subtype_mk (Continuous.subtype_mk
      (hfin.comp (GlobalTheory.DefU.continuous_map_pFin.comp continuous_subtype_val)) _) _, ?_, fun x u => ?_⟩
  · refine Subtype.ext (Subtype.ext ?_)
    change finGL L n (Matrix.GeneralLinearGroup.map (pFin L) 1) = 1
    rw [map_one, map_one]
  · exact (GlobalTheory.SplitPts.cLoc_finGL u _ _).trans (Units.ext rfl)

private theorem exists_adjust {V : Type} (w : V → Plc L) (hw : ∀ v, IsSplitAt (w v))
    (hi : Function.Injective fun v => (w v).under (𝓞 (Lp L))) (x : UA L n) (b : ∀ v, GLw n (w v)) (t : Finset V) :
    ∃ k : finU L n, (∀ u : Plc L, (∀ v, u.under (𝓞 (Lp L)) ≠ (w v).under (𝓞 (Lp L))) → cLoc u (k : UA L n) = cLoc u x) ∧
      ∀ v ∈ t, cLoc (w v) (k : UA L n) = b v := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    obtain ⟨p, -, -, hp⟩ := exists_fin (L := L) (n := n)
    exact ⟨p x, fun u _ => hp x u, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  | insert a t ha ih =>
    obtain ⟨k, h1, h2⟩ := ih
    let z := GlobalTheory.SplitPts.locPt (hw a) ((cLoc (w a) (k : UA L n))⁻¹ * b a)
    have hz : ∀ u : Plc L, u.under (𝓞 (Lp L)) ≠ (w a).under (𝓞 (Lp L)) → cLoc u z.1 = 1 := fun u hu =>
      GlobalTheory.DefU.LocRet.mem_locU_ne z.2 hu
    refine ⟨k * ⟨z.1, (Subgroup.mem_inf.1 z.2).1⟩, fun u hu => ?_, fun v hv => ?_⟩
    · rw [Subgroup.coe_mul, map_mul, hz u (hu a), mul_one, h1 u hu]
    · rw [Subgroup.coe_mul, map_mul]
      by_cases hva : v = a
      · subst hva
        rw [GlobalTheory.SplitPts.cLoc_locPt, mul_inv_cancel_left]
      · rw [hz _ fun h => hva (hi h), mul_one, h2 v ((Finset.mem_insert.1 hv).resolve_left hva)]

private theorem cEmb_rat {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : Plc L) (j : w.adicCompletion L →+* Qbar l)
    {γ : UA L n} (h : γ ∈ ratU L n) :
    cEmb (ι.toRingHom.comp (j.comp (algebraMap L _))) γ = Matrix.GeneralLinearGroup.map (ι.toRingHom.comp j) (cLoc w γ) := by
  obtain ⟨δ, hδ⟩ := h
  refine Units.ext (Matrix.ext fun a b => ?_)
  have e : γ.1.val a b = algebraMap L (Ad L) (δ.val a b) :=
    (congrArg (fun g : GA L n => g.val a b) hδ).symm
  change coord _ (pInf L (γ.1.val a b)) = ι (j (pLoc L w (pFin L (γ.1.val a b))))
  rw [e, coord_algebraMap]
  rfl

end Grp

private theorem cont_multi {ι X : Type} [Finite ι] [TopologicalSpace X] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] [∀ i, FiniteDimensional ℂ (M i)] (m : MultilinearMap ℂ M ℂ) (y : ∀ i, X → M i)
    (hy : ∀ i (ℓ : Module.Dual ℂ (M i)), Continuous fun x => ℓ (y i x)) : Continuous fun x => m fun i => y i x := by
  classical
  haveI := Fintype.ofFinite ι
  let b := fun i => Module.finBasis ℂ (M i)
  have e : (fun x => m fun i => y i x) = fun x => ∑ r : ∀ i, Fin (Module.finrank ℂ (M i)),
      (∏ i, (b i).coord (r i) (y i x)) • m fun i => b i (r i) := by
    funext x
    have h1 : (fun i => y i x) = fun i => ∑ j, (b i).coord j (y i x) • b i j :=
      funext fun i => ((b i).sum_repr (y i x)).symm
    rw [h1, m.map_sum]
    exact Finset.sum_congr rfl fun r _ => m.map_smul_univ _ _
  rw [e]
  exact continuous_finset_sum _ fun r _ => (continuous_finset_prod _ fun i _ => hy i _).smul continuous_const

private theorem cont_sq (n : ℕ) (mu : DomWeight n) (f : nablaSq ℂ n mu) (ℓ : Module.Dual ℂ (nablaSq ℂ n mu)) :
    Continuous fun g : GL (Fin n) ℂ => ℓ (GlobalTheory.Branching.sqRep ℂ n mu g f) := by
  obtain ⟨P, hP⟩ := GlobalTheory.Branching.exists_coef_sqRep n mu f ℓ
  simp only [hP]
  refine (Units.continuous_val.matrix_det.zpow₀ _ fun g : GL (Fin n) ℂ => Or.inl (Matrix.GeneralLinearGroup.det g).ne_zero).mul
    ((MvPolynomial.continuous_eval P).comp (continuous_pi fun x => Units.continuous_val.matrix_elem x.1 x.2))

private theorem fd_sq (n : ℕ) (mu : DomWeight n) : FiniteDimensional ℂ (nablaSq ℂ n mu) :=
  haveI : Finite (Formalism.GradedWeylDivisibility.ssIdx n n mu.natW) := (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  Module.Finite.of_basis ((Module.Basis.span (Formalism.GradedWeylDivisibility.sSBasis ℂ n n mu.natW).choose_spec.1.1).map
    (LinearEquiv.ofEq _ _ (Formalism.GradedWeylDivisibility.sSBasis ℂ n n mu.natW).choose_spec.1.2.1))

private theorem cont_cEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) :
    Continuous (cEmb (E := E) (n := n) τ) := by
  have h1 : Continuous (coord (E := E) τ) := by
    unfold coord
    split_ifs
    · exact continuous_apply _
    · exact Complex.continuous_conj.comp (continuous_apply _)
  have h2 : Continuous (pInf E) := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  exact (Continuous.units_map _ (continuous_id.matrix_map h1)).comp
    ((Continuous.units_map _ (continuous_id.matrix_map h2)).comp continuous_subtype_val)

private theorem aut_coef {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {X : Type} [AddCommGroup X]
    [Module ℂ X] [FiniteDimensional ℂ X] (R : UA E n →* Module.End ℂ X) (F : UA E n → X)
    (hfin : ∀ k ∈ finU E n, R k = 1) (hcont : ∀ (u : X) (ℓ : Module.Dual ℂ X), Continuous fun g => ℓ (R g u))
    (hinf : ∀ y ∈ infU E n, ∀ g, F (g * y) = F g) (hrat : ∀ γ ∈ ratU E n, ∀ g, F (γ * g) = R γ (F g))
    (hsm : ∀ᶠ y in nhds (1 : UA E n), ∀ g, F (g * y) = F g) (ℓ : Module.Dual ℂ X) :
    IsAutFormU fun g => ℓ (R g⁻¹ (F g)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g0 => ?_
    have hc : Continuous fun g : UA E n => ℓ (R g⁻¹ (F g0)) := (hcont (F g0) ℓ).comp continuous_inv
    refine hc.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA E n => g0⁻¹ * g) (nhds g0) (nhds 1) := by
      have : Continuous fun g : UA E n => g0⁻¹ * g := continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using this.tendsto g0
    filter_upwards [ht.eventually hsm] with g hg
    have e := hg g0
    rw [mul_inv_cancel_left] at e
    rw [e]
  · intro γ hγ g
    rw [hrat γ hγ g, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  · refine GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds ((RU E n).comp (finU E n).subtype) _ ?_
    filter_upwards [(continuous_subtype_val.tendsto (1 : finU E n)).eventually hsm] with k hk
    funext g
    change ℓ (R (g * (k : UA E n))⁻¹ (F (g * k))) = ℓ (R g⁻¹ (F g))
    rw [hk g, mul_inv_rev, map_mul, hfin _ ((finU E n).inv_mem k.2), one_mul]
  · let C : Module.Dual ℂ X →ₗ[ℂ] (UA E n → ℂ) :=
      { toFun := fun μ g => μ (R g⁻¹ (F g))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range C) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨ℓ ∘ₗ R (k : UA E n)⁻¹, ?_⟩
    funext g
    change ℓ (R (k : UA E n)⁻¹ (R g⁻¹ (F g))) = ℓ (R (g * (k : UA E n))⁻¹ (F (g * k)))
    rw [hinf _ k.2 g, mul_inv_rev, map_mul, Module.End.mul_apply]

private theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {X H : Type} [AddCommGroup X]
    [Module ℂ X] [FiniteDimensional ℂ X] [Group H] (R : UA E n →* Module.End ℂ X) (J : UA E n →* H)
    (hfin : ∀ k ∈ finU E n, R k = 1) (hcont : ∀ (u : X) (ℓ : Module.Dual ℂ X), Continuous fun g => ℓ (R g u))
    (hker : ∀ x, J x = 1 ↔ x ∈ infU E n) (hs : Function.Surjective J) :
    (∀ F : H → X, (∀ (ℓ : Module.Dual ℂ X) g, ℓ (R g⁻¹ (F (J g))) = 0) → F = 0) ∧
    (∀ F : H → X, (∀ γ ∈ ratU E n, ∀ g, F (J γ * g) = R γ (F g)) → IsOpen {k : finU E n | ∀ g, F (g * J k) = F g} →
      ∀ ℓ : Module.Dual ℂ X, IsAutFormU fun g => ℓ (R g⁻¹ (F (J g)))) ∧
    ∀ Φ : Module.Dual ℂ X →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) →
      (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (ℓ ∘ₗ R x⁻¹)) →
      ∃ F : H → X, (∀ γ ∈ ratU E n, ∀ g, F (J γ * g) = R γ (F g)) ∧ ∀ ℓ g, ℓ (R g⁻¹ (F (J g))) = Φ ℓ g := by
  have hRR : ∀ g u, R g (R g⁻¹ u) = u := fun g u => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hRR' : ∀ g u, R g⁻¹ (R g u) = u := fun g u => by simpa using hRR g⁻¹ u
  refine ⟨fun F h => funext fun y => ?_, fun F hF ho ℓ => ?_, fun Φ h1 h2 => ?_⟩
  · obtain ⟨g, rfl⟩ := hs y
    have h0 : R g⁻¹ (F (J g)) = 0 := (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => h ℓ g
    rw [← hRR g (F (J g)), h0, map_zero]
    rfl
  · refine aut_coef R (fun g => F (J g)) hfin hcont (fun y hy g => ?_) (fun γ hγ g => ?_) ?_ ℓ
    · simp only [map_mul, (hker y).2 hy, mul_one]
    · simp only [map_mul, hF γ hγ]
    · obtain ⟨p, hp, hp1, hp2⟩ := exists_fin (L := E) (n := n)
      have hn : {k : finU E n | ∀ g, F (g * J k) = F g} ∈ nhds (p 1) := ho.mem_nhds (by
        intro g
        rw [hp1]
        simp)
      filter_upwards [(hp.tendsto 1).eventually hn] with y hy g
      have e : J ((p y : UA E n)⁻¹ * y) = 1 := (hker _).2 (mem_inf_of fun u => by
        rw [map_mul, map_inv, hp2, inv_mul_cancel])
      rw [map_mul, map_inv, inv_mul_eq_one] at e
      rw [map_mul, ← e]
      exact hy _
  · let Ψ : UA E n → X := fun g => (Module.evalEquiv ℂ X).symm ((LinearMap.proj g).comp Φ)
    have hΨ : ∀ g (ℓ : Module.Dual ℂ X), ℓ (Ψ g) = Φ ℓ g := fun g ℓ => Module.apply_evalEquiv_symm_apply ℂ X ℓ _
    have ext : ∀ u v : X, (∀ ℓ : Module.Dual ℂ X, ℓ u = ℓ v) → u = v := fun u v h =>
      sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => by rw [map_sub, h, sub_self])
    have key : ∀ g g', J g = J g' → R g (Ψ g) = R g' (Ψ g') := fun g g' h => by
      have hx : g⁻¹ * g' ∈ infU E n := (hker _).1 (by rw [map_mul, map_inv, h, inv_mul_cancel])
      obtain ⟨x, rfl⟩ : ∃ x, g' = g * x := ⟨g⁻¹ * g', (mul_inv_cancel_left _ _).symm⟩
      rw [inv_mul_cancel_left] at hx
      have e : Ψ (g * x) = R x⁻¹ (Ψ g) := ext _ _ fun ℓ => by
        rw [hΨ]
        exact (congrFun (h2 ℓ x hx) g).trans (hΨ g (ℓ ∘ₗ R x⁻¹)).symm
      rw [e, map_mul, Module.End.mul_apply, hRR]
    choose σ hσ using hs
    refine ⟨fun y => R (σ y) (Ψ (σ y)), fun γ hγ y => ?_, fun ℓ g => ?_⟩
    · have e : Ψ (γ * σ y) = Ψ (σ y) := ext _ _ fun ℓ => by rw [hΨ, hΨ, (h1 ℓ).left γ hγ]
      simp only
      rw [key (σ (J γ * y)) (γ * σ y) (by rw [hσ, map_mul, hσ]), e, map_mul, Module.End.mul_apply]
    · simp only
      rw [key (σ (J g)) g (hσ _), hRR', hΨ]

theorem UpperTheory.V.Hi.formU :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ ι : Qbar l ≃+* ℂ, ∀ (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ J : UA L n → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1), (∀ x, J x = ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x)) →
    (∀ F ∈ (hset Q τ₀).X.AF ξ, (∀ ℓ, toForm ι e F ℓ = 0) → F = 0) ∧ (∀ F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ, F ∈ (hset Q τ₀).X.AF ξ → IsOpen {k : finU L n | ∀ g, F (g * J k) = F g} → ∀ ℓ, IsAutFormU (toForm ι e F ℓ)) ∧ (∀ (F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) ℓ (x : UA L n), RU L n x (toForm ι e F ℓ) = toForm ι e (fun g => F (g * J x)) (ℓ ∘ₗ infRep ι lam x⁻¹)) ∧ Function.Surjective (fun k : finU L n => J k) ∧ ∀ Φ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU L n, RU L n x (Φ ℓ) = Φ (ℓ ∘ₗ infRep ι lam x⁻¹)) → ∃ F ∈ (hset Q τ₀).X.AF ξ, ∀ ℓ, toForm ι e F ℓ = Φ ℓ := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V Q c m τ₀ ι lam d e ξ hξ J hJ
  let J' : UA L n →* Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) :=
    MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))
  obtain rfl : J = J' := funext hJ
  haveI : FiniteDimensional ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) :=
    e.finiteDimensional
  haveI : Finite V.frame.Vl := @Finite.of_fintype _ V.frame.finV
  haveI : ∀ v : V.frame.Vl, Finite (W.Emb l (s.w v.1)) := fun v => GlobalTheory.HeckeGal.finite_contEmb _
  have hsp : ∀ v : V.frame.Vl, IsSplitAt (s.w v.1) := fun v => w_split V v
  have hl : ∀ u : Plc L, ((l : ℕ) : 𝓞 L) ∈ u.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.under (𝓞 (Lp L))).asIdeal := fun u => by
    change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ u.asIdeal
    rw [map_natCast]
  have hsurj : Function.Surjective fun k : finU L n => J' k := by
    rintro ⟨a, b⟩
    obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective a
    haveI := V.frame.finV
    obtain ⟨k, h1, h2⟩ := exists_adjust (fun v : V.frame.Vl => s.w v.1) hsp
      (fun v v' h => Subtype.ext ((w_under s v.1).symm.trans (h.trans (w_under s v'.1)))) x b Finset.univ
    refine ⟨k, Prod.ext (Subtype.ext (funext fun u => h1 u.1 fun v h => u.2 ?_)) (funext fun v => h2 v (Finset.mem_univ v))⟩
    rw [hl, h, w_under]
    exact v.2
  have hker : ∀ x, J' x = 1 ↔ x ∈ infU L n := fun x => by
    refine ⟨fun h => mem_inf_of fun u => ?_, fun h => Prod.ext (Subtype.ext (funext fun u => cLoc_inf h u.1))
      (funext fun v => cLoc_inf h _)⟩
    by_cases hu : ((l : ℕ) : 𝓞 L) ∈ u.asIdeal
    · let v : V.frame.Vl := ⟨u.under (𝓞 (Lp L)), (hl u).1 hu⟩
      exact cLoc_conj (hsp v) x (congrFun (congrArg Prod.snd h) v) (w_under s v.1).symm
    · exact congrFun (congrArg (fun y => y.1.1) h) ⟨u, hu⟩
  have hfin : ∀ k ∈ finU L n, infRep (V := V) ι lam k = 1 := fun k hk => by
    have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
      change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
      rw [MonoidHom.mem_ker.1 hk, map_one]
    change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
      GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
    simp only [h1, map_one]
    exact map_one _
  have hcont : ∀ u (ℓ : Module.Dual ℂ _), Continuous fun g => ℓ (infRep (V := V) ι lam g u) := fun u ℓ => by
    induction u using PiTensorProduct.induction_on with
    | add x y hx hy =>
      simp only [map_add]
      exact hx.add hy
    | smul_tprod r f =>
      simp only [map_smul]
      refine Continuous.const_smul ?_ r
      haveI := fd_sq n
      have h := cont_multi (ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ))
        (fun (y : Emb l (fun v : V.frame.Vl => s.w v.1)) (g : UA L n) =>
          GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) g) (f y))
        fun y μ => (cont_sq n _ (f y) μ).comp (cont_cEmb _)
      refine h.congr fun g => congrArg ℓ ?_
      exact (PiTensorProduct.map_tprod _ _).symm
  have hrat : ∀ γ ∈ ratU L n, infRep (V := V) ι lam γ = algRep _ ι lam (J' γ).2 := fun γ hγ =>
    congrArg PiTensorProduct.mapMonoidHom (funext fun y =>
      congrArg (GlobalTheory.Branching.sqRep ℂ n (lam y.res)) (cEmb_rat ι _ y.2.1 hγ))
  have hAF : ∀ F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ, F ∈ (hset Q τ₀).X.AF ξ ↔
      ∀ γ ∈ ratU L n, ∀ g, e (F (J' γ * g)) = infRep (V := V) ι lam γ (e (F g)) := fun F => by
    refine ⟨fun h γ hγ g => ?_, fun h γ g => e.injective ?_⟩
    · rw [hrat γ hγ, ← hξ]
      exact congrArg e (h ⟨γ, hγ⟩ g)
    · refine (h γ.1 γ.2 g).trans ?_
      rw [hrat γ.1 γ.2, ← hξ]
      rfl
  obtain ⟨c1, c2, c3⟩ := core (infRep (V := V) ι lam) J' hfin hcont hker fun y => (hsurj y).elim fun k hk => ⟨k, hk⟩
  refine ⟨fun F _ h => ?_, fun F hF ho ℓ => ?_, fun F ℓ x => funext fun g => ?_, hsurj, fun Φ h1 h2 => ?_⟩
  · have h0 := c1 (fun y => e (F y)) fun ℓ g => congrFun (h ℓ) g
    exact funext fun y => e.map_eq_zero_iff.1 (congrFun h0 y)
  · refine c2 (fun y => e (F y)) ((hAF F).1 hF) ?_ ℓ
    simpa only [e.injective.eq_iff] using ho
  · change ℓ (infRep ι lam (g * x)⁻¹ (e (F (J' (g * x))))) = ℓ (infRep ι lam x⁻¹ (infRep ι lam g⁻¹ (e (F (J' g * J' x)))))
    rw [mul_inv_rev, map_mul, map_mul, Module.End.mul_apply]
  · obtain ⟨F, hF, hF'⟩ := c3 Φ h1 h2
    refine ⟨fun y => e.symm (F y), (hAF _).2 fun γ hγ g => ?_, fun ℓ => funext fun g => ?_⟩
    · simp only [e.apply_symm_apply, hF γ hγ]
    · change ℓ (infRep ι lam g⁻¹ (e (e.symm (F (J' g))))) = _
      rw [e.apply_symm_apply, hF']
