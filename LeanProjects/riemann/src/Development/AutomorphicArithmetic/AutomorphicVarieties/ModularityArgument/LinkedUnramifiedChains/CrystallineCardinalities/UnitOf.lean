import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.TanAOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.CupUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.TwoApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.CrOfPot
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.AdicOfCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.PtSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField Formalism.ConjugateSelfDual Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing Topology UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.Z.J UpperTheory.V.Loc

private theorem crConj {l : ℕ} [Fact l.Prime] {D : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (φ : D →* GQ l) (hφ : IsOpenEmbedding φ)
    {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]
    (r t : D →* GL (Fin 3) E) (g : GL (Fin 3) E) (hr : Continuous fun s => (r s : Matrix (Fin 3) (Fin 3) E))
    (h : ∀ s, t s = g * r s * g⁻¹) (U : Subgroup D) (hU : IsOpen (U : Set D)) (hc : CrOn φ (colRep r) U) : CrOn φ (colRep t) U := by
  have ht : Continuous fun s => (t s : Matrix (Fin 3) (Fin 3) E) := by
    simp only [h, Units.val_mul]
    exact (continuous_const.matrix_mul hr).matrix_mul continuous_const
  have hψ : IsOpenEmbedding (φ.comp U.subtype) := hφ.comp hU.isOpenEmbedding_subtypeVal
  have hr' : Continuous fun s : U => ((r.comp U.subtype) s : Matrix (Fin 3) (Fin 3) E) := hr.comp continuous_subtype_val
  have ht' : Continuous fun s : U => ((t.comp U.subtype) s : Matrix (Fin 3) (Fin 3) E) := ht.comp continuous_subtype_val
  refine ((isCrys_isDR_sub_quot (φ.comp U.subtype) hψ (colRep (r.comp U.subtype)) (colRep (t.comp U.subtype)) (contAction_colRep hr') (contAction_colRep ht')
      ((Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) E)).restrictScalars ℚ_[l]) (fun s x => ?_)).2 (fun y => ?_)).1 hc
  · simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, colRep_apply, Matrix.mulVec_mulVec, MonoidHom.comp_apply, Subgroup.subtype_apply, h,
      ← Units.val_mul, inv_mul_cancel_right]
  · refine ⟨((g⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).mulVec y, ?_⟩
    simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

private theorem idxStep (e : ℕ) (he : 1 ≤ e) {A : Type} [CommGroup A] (x y : A) (hy : IsOfFinOrder y) (hx : ¬ IsOfFinOrder x)
    (i j : Fin 3) (h : (x ^ (e : ℤ) * y) ^ (Fr.w 3 i - Fr.w 3 j) = x) : ∃ i' : Fin 2, i = i'.castSucc ∧ j = i'.succ := by
  have key : ∀ i j : Fin 3, Fr.w 3 i - Fr.w 3 j = 1 → ∃ i' : Fin 2, i = i'.castSucc ∧ j = i'.succ := by decide
  refine key i j ?_
  set d : ℤ := Fr.w 3 i - Fr.w 3 j with hd
  have h0 : x ^ ((e : ℤ) * d) * y ^ d = x := by rw [zpow_mul, ← mul_zpow]; exact h
  have h1 : x ^ ((e : ℤ) * d - 1) = (y ^ d)⁻¹ := by
    rw [zpow_sub, zpow_one, eq_mul_inv_of_mul_eq h0, mul_comm, inv_mul_cancel_left]
  have h2 : (e : ℤ) * d = 1 := by
    by_contra hne
    apply hx
    obtain ⟨n, hn, hyn⟩ := isOfFinOrder_iff_pow_eq_one.1 hy
    refine isOfFinOrder_iff_zpow_eq_one.2 ⟨((e : ℤ) * d - 1) * n, mul_ne_zero (sub_ne_zero.2 hne) (by exact_mod_cast hn.ne'), ?_⟩
    rw [zpow_mul, h1, zpow_natCast, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyn, one_zpow, inv_one]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h2 with ⟨-, h3⟩ | ⟨h3, -⟩
  · exact h3
  · omega

private theorem stepCore (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] {D : Type} [Group D] [TopologicalSpace D]
    [IsTopologicalGroup D] [CompactSpace D] (φ : D →* GQ l) (hφ : IsOpenEmbedding φ) (E : FinExt l)
    (hE : ∀ x : PadicAlgCl l, x ∈ E.1 → ∃ (m : ℕ) (a : c.O), (l : PadicAlgCl l) ^ m * x = a.1)
    (t : D →* GL (Fin 3) c.O) (t' : D →* GL (Fin 3) ↥E.1)
    (ht : ∀ s a b, (((t' s : Matrix (Fin 3) (Fin 3) ↥E.1) a b : ↥E.1) : PadicAlgCl l) = ((t s : Matrix (Fin 3) (Fin 3) c.O) a b : c.O).1)
    (hc : Continuous fun s => (t' s : Matrix (Fin 3) (Fin 3) ↥E.1)) (hup : ∀ s, Fr.UpT (t s : Matrix (Fin 3) (Fin 3) c.O))
    (U : Subgroup D) [U.Normal] (hU : IsOpen (U : Set D)) (hcr : CrOn φ (colRep t') U) (i : Fin 2)
    (hlink : ∀ s, (t s : Matrix (Fin 3) (Fin 3) c.O) i.castSucc i.castSucc =
      algebraMap ℤ_[l] c.O (cyc l l (φ s)) * (t s : Matrix (Fin 3) (Fin 3) c.O) i.succ i.succ)
    (I : Subgroup D) (hI : ∀ s ∈ I, φ s ∈ Iq l) : UnitStep I ((cyc l l).comp φ) t i := by
  haveI := E.2
  haveI : IsModuleTopology ℚ_[l] ↥E.1 := isModuleTopologyOfFiniteDimensional
  have hinv : ∀ s a b, ((((t' s)⁻¹ : GL (Fin 3) ↥E.1) : Matrix (Fin 3) (Fin 3) ↥E.1) a b : PadicAlgCl l) =
      ((((t s)⁻¹ : GL (Fin 3) c.O) : Matrix (Fin 3) (Fin 3) c.O) a b : c.O).1 := fun s a b => by
    rw [← map_inv, ← map_inv]; exact ht _ a b
  have hcy : ∀ s, ((algebraMap ℤ_[l] c.O (cyc l l (φ s)) : c.O) : PadicAlgCl l) = (((cycA l l ↥E.1 (φ s) : (↥E.1)ˣ) : ↥E.1) : PadicAlgCl l) := fun s => rfl
  have hZ := stepF φ hφ t' hc (fun g a b hab => Subtype.ext (by
      rw [ht, hup g a b hab]; rfl)) U hU hcr i (fun g => Subtype.ext (by
      rw [ht, hlink g, MulMemClass.coe_mul, MulMemClass.coe_mul, ht]
      exact congrArg (· * _) (hcy g)))
  obtain ⟨u, β, cu, cβ, ua, ui, ⟨s₀, hs₀⟩, ub⟩ := cupUnr hP φ hφ _ hZ
  have bd : ∀ x : ↥E.1, ∃ (m : ℕ) (a : c.O), (l : PadicAlgCl l) ^ m * (x : PadicAlgCl l) = a.1 := fun x => hE _ x.2
  obtain ⟨m, u', β', au, aβ, hu, hβ⟩ := clearDen c (fun s => (u s : PadicAlgCl l)) (fun s => (β s : PadicAlgCl l))
    (continuous_subtype_val.comp cu) (continuous_subtype_val.comp cβ) (fun s => bd _) (fun s => bd _)
  have hl : (l : PadicAlgCl l) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  refine ⟨hlink, u', β', au, aβ, fun s s' => Subtype.ext ?_, fun s hs => Subtype.ext ?_, ⟨s₀, fun h => hs₀ ?_⟩, fun s s' => Subtype.ext ?_⟩
  · rw [AddMemClass.coe_add, hu, hu, hu, ua, AddMemClass.coe_add, mul_add]
  · rw [hu, ui s (hI s hs)]
    simp
  · have h1 := hu s₀
    rw [h] at h1
    exact Subtype.ext ((mul_eq_zero.1 (h1.symm.trans rfl)).resolve_left hl)
  · have e := congrArg (Subtype.val) (ub s s')
    simp only [AddMemClass.coe_add, AddSubgroupClass.coe_sub, MulMemClass.coe_mul] at e ⊢
    rw [hβ, hβ, hβ, hu, e, ht, hinv, MonoidHom.comp_apply, hcy]
    ring

private theorem fieldOf {l : ℕ} [Fact l.Prime] (c : Coef l) : ∃ E : FinExt l, (∀ x : c.O, x.1 ∈ E.1) ∧
    ∀ x ∈ E.1, ∃ (m : ℕ) (a : c.O), (l : PadicAlgCl l) ^ m * x = a.1 := by
  have hlc : ∀ m : ℕ, (l : PadicAlgCl l) ^ m ∈ c.O := fun m => pow_mem (natCast_mem c.O l) m
  let T : Subalgebra ℚ_[l] (PadicAlgCl l) :=
    { carrier := {x | ∃ (m : ℕ) (a : c.O), (l : PadicAlgCl l) ^ m * x = a.1}
      mul_mem' := by
        rintro x y ⟨m, a, ha⟩ ⟨n, b, hb⟩
        refine ⟨m + n, a * b, ?_⟩
        rw [MulMemClass.coe_mul, ← ha, ← hb, pow_add]
        ring
      add_mem' := by
        rintro x y ⟨m, a, ha⟩ ⟨n, b, hb⟩
        refine ⟨m + n, ⟨_, hlc n⟩ * a + ⟨_, hlc m⟩ * b, ?_⟩
        rw [AddMemClass.coe_add, MulMemClass.coe_mul, MulMemClass.coe_mul, ← ha, ← hb, pow_add]
        ring
      algebraMap_mem' := fun q => by
        have hlt : ‖((l : ℚ_[l]))‖ < 1 := Padic.norm_p_lt_one
        obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (max ‖q‖ 1)⁻¹ by positivity) hlt
        have h1 : ‖(l : ℚ_[l]) ^ m * q‖ ≤ 1 := by
          rw [norm_mul, norm_pow]
          calc _ ≤ (max ‖q‖ 1)⁻¹ * max ‖q‖ 1 := mul_le_mul hm.le (le_max_left _ _) (norm_nonneg _) (by positivity)
            _ = 1 := inv_mul_cancel₀ (by positivity)
        let a : ℤ_[l] := ⟨_, h1⟩
        have ha : algebraMap ℤ_[l] ℚ_[l] a = (l : ℚ_[l]) ^ m * q := rfl
        refine ⟨m, algebraMap ℤ_[l] c.O a, ?_⟩
        have e : ((algebraMap ℤ_[l] c.O a : c.O) : PadicAlgCl l) = algebraMap ℤ_[l] (PadicAlgCl l) a := rfl
        rw [e, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), ha, map_mul, map_pow, map_natCast] }
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] c.O).FG)
  let S : Set (PadicAlgCl l) := (fun x : c.O => x.1) '' (s : Set c.O)
  have hS : S.Finite := s.finite_toSet.image _
  have halg : ∀ x ∈ S, IsIntegral ℚ_[l] x := fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin (S := S) halg
  refine ⟨⟨IntermediateField.adjoin ℚ_[l] S, inferInstance⟩, fun x => ?_, fun x hx => ?_⟩
  · have hx : x ∈ Submodule.span ℤ_[l] (s : Set c.O) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      have e : (a • y).1 = algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] a) * y.1 := by
        rw [← IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), ← Algebra.smul_def]
        rfl
      rw [e]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
  · have h1 : Algebra.adjoin ℚ_[l] S ≤ T := Algebra.adjoin_le (by
      rintro _ ⟨y, -, rfl⟩
      exact ⟨0, y, by simp⟩)
    have h2 : x ∈ (IntermediateField.adjoin ℚ_[l] S).toSubalgebra := hx
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun y hy => (halg y hy).isAlgebraic)] at h2
    exact h1 h2

private theorem flagStep (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] (c₁ : Coef l) [Fr.IsCoef l c₁.O] {F : Fr.Frame l (ResidueField c₁.O)} {C₀ : ℕ}
    (hF : F.Ok C₀) (S : Fr.Space c₁.O F 3) (ξ : S.R →ₐ[c₁.O] c₁.O) (v : F.V) (φ : F.Gv v →* GQ l) (hφ : IsOpenEmbedding φ)
    (hcy : ∀ s, Loc.cyc l l (φ s) = F.eps (F.loc v s)) (hIq : ∀ s ∈ F.Iv v, φ s ∈ Iq l) (i' : Fin 2)
    (hlink : ∀ s, (ξ (S.ρ.ψ v i'.castSucc s).val).1 = (ξ (S.ρ.ψ v i'.succ s).val).1 * algebraMap ℤ_[l] (Qbar l) (Loc.cyc l l (φ s)))
    (hcr : ∀ (E : FinExt l) (r' : F.Gv v →* GL (Fin 3) ↥E.1),
      (∀ s a b, (((r' s : Matrix (Fin 3) (Fin 3) ↥E.1) a b : ↥E.1) : PadicAlgCl l) = (ξ (S.ρ.r (F.loc0 v s) a b)).1) →
      ∃ (U : Subgroup (F.Gv v)) (_ : U.Normal), IsOpen (U : Set (F.Gv v)) ∧ CrOn φ (colRep r') U) :
    UnitAt (S.ρ.map (ξ : S.R →+* c₁.O)) v i' := by
  let y₀ : S.R →ₐ[c₁.O] Qbar l := (Algebra.ofId c₁.O (Qbar l)).comp ξ
  have hcont : ∀ a b, Continuous fun g => y₀ (S.ρ.r g a b) := fun a b => Hi.Up.pt_cont y₀ (S.lift.1.1 a b)
  obtain ⟨E, hE1, hE2⟩ := fieldOf c₁
  haveI := E.2
  haveI : IsModuleTopology ℚ_[l] ↥E.1 := isModuleTopologyOfFiniteDimensional
  let f₀ : S.A →+* c₁.O := (ξ : S.R →+* c₁.O).comp (S.A.val : S.A →+* S.R)
  obtain ⟨g, hg⟩ := Fr.flag hF (Or.inr rfl) S c₁.O f₀ v
  let ρ₀ : F.Gv v →* GL (Fin 3) c₁.O := (((S.u.map f₀).r.comp (F.loc0 v))).toHomUnits
  let t : F.Gv v →* GL (Fin 3) c₁.O := (MulAut.conj g).toMonoidHom.comp ρ₀
  have ht : ∀ s, t s = g * ρ₀ s * g⁻¹ := fun s => rfl
  let ιE : c₁.O →+* ↥E.1 := (c₁.O.val : c₁.O →+* PadicAlgCl l).codRestrict E.1.toSubfield.toSubring hE1
  let m : GL (Fin 3) c₁.O →* GL (Fin 3) ↥E.1 := Matrix.GeneralLinearGroup.map ιE
  let r' : F.Gv v →* GL (Fin 3) ↥E.1 := m.comp ρ₀
  let t' : F.Gv v →* GL (Fin 3) ↥E.1 := m.comp t
  have hm : ∀ (x : GL (Fin 3) c₁.O) a b, (((m x : Matrix (Fin 3) (Fin 3) ↥E.1) a b : ↥E.1) : PadicAlgCl l) = ((x : Matrix (Fin 3) (Fin 3) c₁.O) a b : c₁.O).1 :=
    fun x a b => rfl
  have hr'c : Continuous fun s => (r' s : Matrix (Fin 3) (Fin 3) ↥E.1) := by
    refine continuous_matrix fun a b => Continuous.subtype_mk ?_ _
    exact (hcont a b).comp (hF.loc_cont v)
  have hht' : ∀ s, t' s = m g * r' s * (m g)⁻¹ := fun s => by
    show m (t s) = _
    rw [ht, map_mul, map_mul, map_inv]
    rfl
  have ht'c : Continuous fun s => (t' s : Matrix (Fin 3) (Fin 3) ↥E.1) := by
    simp only [hht', Units.val_mul]
    exact (continuous_const.matrix_mul hr'c).matrix_mul continuous_const
  obtain ⟨U, hUn, hUo, hCr⟩ := hcr E r' (fun s a b => rfl)
  have hCr' := crConj φ hφ r' t' (m g) hr'c hht' U hUo hCr
  have hε : (cyc l l).comp φ = F.eps.comp (F.loc v) := MonoidHom.ext hcy
  have hdiag : ∀ s a, (t s : Matrix (Fin 3) (Fin 3) c₁.O) a a = (S.ρ.map (ξ : S.R →+* c₁.O)).ψ v a s := fun s a => (hg s).2 a
  have hup : ∀ s, Fr.UpT (t s : Matrix (Fin 3) (Fin 3) c₁.O) := fun s a b hab => (hg s).1 a b hab
  refine ⟨g, t, fun s => rfl, hup, hdiag, ?_⟩
  rw [← hε]
  refine stepCore hP c₁ φ hφ E hE2 t t' (fun s a b => hm _ a b) ht'c hup U hUo hCr' i' (fun s => Subtype.ext ?_) _ hIq
  rw [hdiag, hdiag, MulMemClass.coe_mul, mul_comm]
  exact hlink s

private theorem locEmb {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} {L : Type} [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) (v : Φ.V) (j : Ω →+* Om l) (hj : placeJ j = k.pl v) :
    ∃ (φ : Φ.Gv v →* GQ l) (ψ : Φ.Gv v →* G L Ω), IsOpenEmbedding φ ∧ (∀ h y, φ h (j y) = j (ψ h y)) ∧
      (∀ s, k.p0 (ψ s) = Φ.loc0 v s) ∧ (∀ s, φ s ∈ Iq l ↔ s ∈ Φ.Iv v) ∧ (∀ s, Loc.cyc l l (φ s) = Φ.eps (Φ.loc v s)) := by
  have hE := (galEmbTop ℚ L Ω).1
  obtain ⟨hDI, -, hcyc, -⟩ := galEmbFam ℚ L Ω l
  have hmem : ∀ s, (k.j v s).1 ∈ galOf ℚ L Ω := fun s => by
    rw [k.gal]
    refine ⟨(k.j v s).2, ?_⟩
    have h1 := k.del (k.j v s)
    rw [← k.j_loc] at h1
    exact h1.symm.trans (Φ.loc0 v s).2
  have hr := range_galEmb ℚ L Ω
  let e : G L Ω ≃* galOf ℚ L Ω := (MonoidHom.ofInjective hE.injective).trans (MulEquiv.subgroupCongr hr)
  let m : Φ.Gv v →* galOf ℚ L Ω := ((upl Ω L).subtype.comp (k.j v)).codRestrict _ hmem
  let ψ : Φ.Gv v →* G L Ω := e.symm.toMonoidHom.comp m
  have hψ : ∀ s, galEmb ℚ L Ω (ψ s) = (k.j v s).1 := fun s =>
    congrArg Subtype.val (e.apply_symm_apply (m s))
  have hψc : Continuous ψ := by
    refine hE.continuous_iff.2 ?_
    have : (galEmb ℚ L Ω) ∘ ψ = fun s => (k.j v s).1 := funext hψ
    rw [this]
    exact continuous_subtype_val.comp (k.j_cont v)
  have hψi : Function.Injective ψ := fun a b h => by
    have h1 := congrArg (galEmb ℚ L Ω) h
    rw [hψ, hψ] at h1
    exact k.j_inj v (Subtype.ext h1)
  have hD : ∀ x : G L Ω, x ∈ Dec (F := L) (placeJ j) ↔ galEmb ℚ L Ω x ∈ Dec (F := ℚ) (k.pl v) := fun x => by
    rw [hj, ← (hDI (k.pl v)).1]; rfl
  have hI : ∀ x : G L Ω, x ∈ Ine (F := L) (placeJ j) ↔ galEmb ℚ L Ω x ∈ Ine (F := ℚ) (k.pl v) := fun x => by
    rw [hj, ← (hDI (k.pl v)).2]; rfl
  let τ : Φ.Gv v →* Dec (F := L) (placeJ j) := ψ.codRestrict _ fun s => by
    rw [hD, hψ]
    exact (k.j_range v _).1 ⟨s, rfl⟩
  have hτ : IsOpenEmbedding τ := by
    refine (isHomeomorph_iff_continuous_bijective.2 ⟨hψc.subtype_mk _, fun a b h => hψi (congrArg Subtype.val h), fun x => ?_⟩).isOpenEmbedding
    have h1 : galEmb ℚ L Ω x.1 ∈ upl Ω L := by
      have := galEmb_mem ℚ L Ω x.1
      rw [k.gal] at this
      exact this.1
    obtain ⟨s, hs⟩ := (k.j_range v ⟨_, h1⟩).2 ((hD x.1).1 x.2)
    refine ⟨s, Subtype.ext (hE.injective ?_)⟩
    show galEmb ℚ L Ω (ψ s) = _
    rw [hψ, hs]
  obtain ⟨-, φL, hφL, hcomp, -, hIne, hcy, -⟩ := (@Loc.decEmb L Ω _ _ _ _ _ _ l _).2 j
  refine ⟨φL.comp τ, ψ, hφL.comp hτ, fun h y => hcomp (τ h) y, fun s => Subtype.ext ?_, fun s => ?_, fun s => ?_⟩
  · show k.p ⟨galEmb ℚ L Ω (ψ s), _⟩ = Φ.loc v s
    rw [k.j_loc]
    exact congrArg k.p (Subtype.ext (hψ s))
  · refine (hIne (τ s)).trans ?_
    show ψ s ∈ _ ↔ _
    rw [hI, hψ, k.j_ine]
  · refine (hcy l (τ s)).trans ?_
    rw [k.j_loc, k.eps]
    show cycZ L Ω l (ψ s) = _
    rw [← hcyc, MonoidHom.comp_apply, hψ]

theorem UpperTheory.V.Z.J.unitOf :
    Loc.LocalPublishedTheorems → UpperTheory.V.J.UnitOfP := by
  intro hP Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k c₁ _ f R ξ r hr hI v hc i j hij
  let y₀ : R.S.R →ₐ[c₁.O] Qbar l := (Algebra.ofId c₁.O (Qbar l)).comp ξ
  have hy₀ : ∀ a, y₀ a = (ξ a).1 := fun a => rfl
  have hcont : ∀ a b, Continuous fun g => y₀ (R.S.ρ.r g a b) := fun a b => Hi.Up.pt_cont y₀ (R.S.lift.1.1 a b)
  have hp0 : Continuous k.p0 := by
    refine Continuous.subtype_mk (k.p_cont.comp (Continuous.subtype_mk (galEmbTop ℚ L Ω).1.continuous _)) _
  have hrv : Continuous fun s => (r s : Matrix (Fin 3) (Fin 3) (Qbar l)) := by
    refine continuous_matrix fun a b => ?_
    have : (fun s => (r s : Matrix (Fin 3) (Fin 3) (Qbar l)) a b) = fun s => y₀ (R.S.ρ.r (k.p0 s) a b) := funext fun s => by
      rw [hr]; rfl
    rw [this]
    exact (hcont a b).comp hp0
  have hrc : Continuous r := by
    refine Units.continuous_iff.2 ⟨hrv, ?_⟩
    simp only [← map_inv]
    exact hrv.comp continuous_inv
  obtain ⟨jj, hjj, hcr⟩ := crOfPot (k.pl v) r hrc hc
  obtain ⟨φ, ψ', hφ, hcomp, hp, hIq, hcy⟩ := locEmb k v jj hjj
  have hcb : ∀ s : Φ.Gv v, (cycBar ℚ Ω l (k.j v s).1 : Qbar l) = algebraMap ℤ_[l] (Qbar l) (Loc.cyc l l (φ s)) := fun s => by
    rw [hcy, k.j_loc, k.eps]
    rfl
  have hinj : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l)]
    exact (algebraMap ℚ_[l] (Qbar l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  obtain ⟨-, ⟨g₀, rfl⟩, hnf⟩ : ∃ s, s ∈ φ.range ∧ s ∈ Iq l ∧ ¬ IsOfFinOrder (Loc.cyc l l s) := by
    obtain ⟨s, ⟨h1, h2⟩, h3⟩ := ((cycInertia l).2 φ.range (by simpa using hφ.isOpen_range)).2
    exact ⟨s, h1, h2, h3⟩
  obtain ⟨hgI, hnf⟩ := hnf
  have hg₀ : g₀ ∈ Φ.Iv v := (hIq g₀).1 hgI
  let μ : c.Oˣ →* (Qbar l)ˣ := Units.map (c.O.val : c.O →* Qbar l)
  let x : (Qbar l)ˣ := cycBar ℚ Ω l (k.j v g₀).1
  let y : (Qbar l)ˣ := μ (Chr.dirG ℚ Ω ψ (k.j v g₀).1)
  have hx : ¬ IsOfFinOrder x := fun h => hnf (by
    obtain ⟨n, hn, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 h
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, Units.ext (hinj ?_)⟩
    have h2 := congrArg Units.val h1
    rw [Units.val_pow_eq_pow_val, hcb, Units.val_one] at h2
    rw [Units.val_pow_eq_pow_val, map_pow]
    simpa using h2)
  have hy : IsOfFinOrder y := by
    exact MonoidHom.isOfFinOrder μ (MonoidHom.isOfFinOrder ψ.toUnitHom (isOfFinOrder_of_finite (Chr.cls ℚ Ω N (k.j v g₀).1)))
  have hPsi : μ (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g₀).1) = x ^ (e : ℤ) * y := by
    have h1 : μ (chiO ℚ Ω l c.O (k.j v g₀).1) = x := Units.ext rfl
    have h2 : Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g₀).1 = chiO ℚ Ω l c.O (k.j v g₀).1 ^ (e : ℤ) * Chr.dirG ℚ Ω ψ (k.j v g₀).1 := rfl
    rw [h2, map_mul, map_zpow, h1]
  have hrel : (x ^ (e : ℤ) * y) ^ (Fr.w 3 i - Fr.w 3 j) = x := by
    have h1 := hij g₀
    rw [hI v i g₀ hg₀, hI v j g₀ hg₀] at h1
    rw [← hPsi, zpow_sub, ← map_zpow μ, ← map_zpow μ]
    rw [mul_inv_eq_iff_eq_mul, mul_comm]
    exact Units.ext h1
  obtain ⟨i', rfl, rfl⟩ := idxStep e hL.e_pos x y hy hx i j hrel
  refine ⟨i', flagStep hP c₁ R.ok R.S ξ v φ hφ hcy (fun s hs => (hIq s).2 hs) i' (fun s => ?_) fun E r' h => ?_⟩
  · have h1 := hij s
    rw [hcb s] at h1
    exact h1
  · refine hcr φ ψ' hφ hcomp E r' fun s a b => ?_
    rw [hr, hp]
    exact h s a b
