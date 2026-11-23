import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne
open GlobalTheory.Pst GlobalTheory.TripleGal Module TensorProduct Polynomial Formalism.MainNotions.N
open UpperTheory.Lit.CharWD GlobalTheory.Published
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

private theorem letter_lift {L U D M : Type} [Field L] [Field U] [AddCommGroup D] [Module L D] (m : U →+* End L D)
    (F : Type) [Field F] [Algebra L F] (τ : U →+* F) [AddCommGroup M] [Module F M] (g : D →+ M)
    (h1 : ∀ (a : L) x, g (a • x) = algebraMap L F a • g x) (h2 : ∀ c x, g (m c x) = τ c • g x) :
    ∃ Φ : Letter m F τ →ₗ[F] M, ∀ x, Φ (letterMk m F τ x) = g x := by
  letI : Module L M := Module.compHom _ (algebraMap L F)
  haveI : IsScalarTower L F M := ⟨fun a c y => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let g' : D →ₗ[L] M := { g with map_smul' := h1 }
  have e : ∀ (a : F) x, LinearMap.liftBaseChange F g' (a ⊗ₜ x) = a • g x := fun a x =>
    LinearMap.liftBaseChange_tmul _ _ _ _
  refine ⟨(letterKer m F τ).liftQ (LinearMap.liftBaseChange F g') (iSup_le fun c => ?_), fun x =>
    (e 1 x).trans (one_smul _ _)⟩
  rintro _ ⟨y, rfl⟩
  rw [LinearMap.mem_ker]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.sub_apply, LinearMap.baseChange_tmul, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul, e, e, h2, smul_comm, sub_self]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

private theorem line_smul {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (hd : finrank ℂ W = 1)
    (f : End ℂ W) (c : ℂ) (hc : c ∈ f.charpoly.roots) (v : W) : f v = c • v := by
  rw [mem_roots (LinearMap.charpoly_monic _).ne_zero, ← End.hasEigenvalue_iff_isRoot_charpoly] at hc
  obtain ⟨u, hu⟩ := hc.exists_hasEigenvector
  obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) u hu.2).mp hd v
  rw [map_smul, hu.apply_eq_smul, smul_comm]

section

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L₁ L₂ : FinExt l}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
  [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]

open EnlargeCoeff in
private theorem dQ_inv {ρ₁ : Representation ↥L₁.1 ↥(GK K) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK K) V₂}
    {f : V₁ →ₗ[ℚ_[l]] V₂} {f' : V₂ →ₗ[ℚ_[l]] V₁} (hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v))
    (hf' : ∀ g v, f' (ρ₂ g v) = ρ₁ g (f' v)) (e : ∀ v, f (f' v) = v) (y : ↥(Dpst P ρ₂)) :
    dQ P hf (dQ P hf' y) = y := by
  apply Subtype.ext
  rw [coe_dQ, coe_dQ]
  induction (y : V₂ ⊗[ℚ_[l]] Bst P) using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [tensQ_tmul, tensQ_tmul, e]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

open EnlargeCoeff in

private theorem dQ_bij {ρ₁ : Representation ↥L₁.1 ↥(GK K) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK K) V₂}
    (f : V₁ ≃ₗ[ℚ_[l]] V₂) (hf : ∀ g v, f.toLinearMap (ρ₁ g v) = ρ₂ g (f.toLinearMap v)) :
    Function.Bijective (dQ P hf) := by
  have hf' : ∀ g v, f.symm.toLinearMap (ρ₂ g v) = ρ₁ g (f.symm.toLinearMap v) := fun g v =>
    f.injective ((f.apply_symm_apply _).trans ((congrArg (ρ₂ g) (f.apply_symm_apply v).symm).trans (hf g _).symm))
  exact Function.bijective_iff_has_inverse.2
    ⟨dQ P hf', dQ_inv P hf' hf f.symm_apply_apply, dQ_inv P hf hf' f.apply_symm_apply⟩

open EnlargeCoeff in
private theorem isPst_equiv {ρ₁ : Representation ↥L₁.1 ↥(GK K) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK K) V₂}
    (f : V₁ ≃ₗ[ℚ_[l]] V₂) (hf : ∀ g v, f.toLinearMap (ρ₁ g v) = ρ₂ g (f.toLinearMap v)) (hV : IsPst P ρ₁) :
    IsPst P ρ₂ := by
  let T : DpstUr P ρ₁ →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ₂ :=
    { toFun := dQ P hf
      map_add' := (dQ P hf).map_add
      map_smul' := dQ_mulD P hf }
  unfold IsPst at hV ⊢
  rw [← (LinearEquiv.ofBijective T (dQ_bij P f hf)).rank_eq, hV, f.rank_eq]

end

section

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces B)

private theorem exists_semi {K L₁ L₂ : FinExt l}
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
    [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
    {ρ₁ : Representation ↥L₁.1 ↥(GK K) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK K) V₂} (g : GQ l)
    (S : ↥(Dpst P ρ₁) →+ ↥(Dpst P ρ₂))
    (h1 : ∀ a : ↥L₁.1, ∃ a' : ↥L₂.1, (a' : Om l) = g a ∧ ∀ x, S (a • x) = a' • S x)
    (h2 : ∀ c : ↥(MaximalUnramifiedExtension l), ∃ c' : ↥(MaximalUnramifiedExtension l), (c' : Om l) = g c ∧ ∀ x, S (mulD P ρ₁ c x) = mulD P ρ₂ c' (S x)) :
    ∃ Φ : WDSpace P ι ρ₁ → WDSpace P ι ρ₂, (∀ (z : Om l) y, Φ (ι z • y) = ι (g z) • Φ y) ∧
      ∀ x, Φ (wdMk P ι ρ₁ x) = wdMk P ι ρ₂ (S x) := by
  let θ : ℂ →+* ℂ := ι.toRingHom.comp ((g : Om l →+* Om l).comp ι.symm.toRingHom)
  have hθ : ∀ z, θ (ι z) = ι (g z) := fun z => congrArg (fun t => ι (g t)) (ι.symm_apply_apply z)
  letI := algC ι L₁
  obtain ⟨Φ, hΦ⟩ := @letter_lift _ _ _ (WDSpace P ι ρ₂) _ _ _ _ (mulD P ρ₁) ℂ _ _ (urC ι) _ (Module.compHom _ θ)
    ((AddMonoidHom.mk' (wdMk P ι ρ₂) (wdMk_add P ι ρ₂)).comp S)
    (fun a x => by
      obtain ⟨a', e1, e2⟩ := h1 a
      show wdMk P ι ρ₂ (S (a • x)) = θ (ι a) • wdMk P ι ρ₂ (S x)
      rw [e2, wdMk_smul, hθ, e1])
    (fun c x => by
      obtain ⟨c', e1, e2⟩ := h2 c
      show wdMk P ι ρ₂ (S (mulD P ρ₁ c x)) = θ (ι c) • wdMk P ι ρ₂ (S x)
      rw [e2, wdMk_mul, hθ, e1])
  refine ⟨fun y => Φ y, fun z y => ?_, hΦ⟩
  rw [← hθ]
  exact @LinearMap.map_smul _ _ _ _ _ _ _ (Module.compHom _ θ) Φ _ _

open EnlargeCoeff in

private theorem eig_conj {L₁ L₂ : FinExt l}
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
    [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
    [FiniteDimensional ↥L₁.1 V₁] [FiniteDimensional ↥L₂.1 V₂]
    {ρ₁ : Representation ↥L₁.1 ↥(GK B.Kw) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK B.Kw) V₂} (g : GQ l)
    (d₁ : finrank ↥L₁.1 V₁ = 1) (d₂ : finrank ↥L₂.1 V₂ = 1)
    (s : ↥L₁.1 →+* ↥L₂.1) (hs : ∀ a, (s a : Om l) = g a)
    (f : V₁ ≃ₗ[ℚ_[l]] V₂) (hf : ∀ g v, f.toLinearMap (ρ₁ g v) = ρ₂ g (f.toLinearMap v))
    (hfs : ∀ (a : ↥L₁.1) v, f.toLinearMap (a • v) = s a • f.toLinearMap v) (hV₁ : IsPst P ρ₁)
    (σ : Weil h) (z : Om l) (hz : ι z ∈ (wdPst P ι B h hj ρ₁).eig σ) : ι (g z) ∈ (wdPst P ι B h hj ρ₂).eig σ := by
  have hV₂ := isPst_equiv P f hf hV₁
  haveI := hV₁.finite
  haveI := hV₂.finite
  obtain ⟨T, t1, t2, t3, -⟩ := BridgeParam.exists_isTwist P ρ₂ g
  obtain ⟨Φ, hΦ1, hΦ2⟩ := exists_semi P ι g ((T : End ↥L₂.1 ↥(Dpst P ρ₂)).toAddMonoidHom.comp (dQ P hf))
    (fun a => ⟨s a, hs a, fun x => by
      have e : dQ P hf (a • x) = s a • dQ P hf x := Subtype.ext (tensQ_smul P s hfs a x.1)
      exact (congrArg (T : End ↥L₂.1 ↥(Dpst P ρ₂)) e).trans (map_smul _ _ _)⟩)
    (fun c => ⟨⟨g c, (BridgeInd.mem_Kur_iff g _).1 c.2⟩, rfl, fun x =>
      (congrArg (T : End ↥L₂.1 ↥(Dpst P ρ₂)) (dQ_mulD P hf c x)).trans (LinearMap.congr_fun (t1 c _ rfl) _)⟩)
  have e₁ : finrank ℂ (WDSpace P ι ρ₁) = 1 := (LetterDim.finrank_wdSpace l P ι _ L₁ _ _ hV₁).trans d₁
  have e₂ : finrank ℂ (WDSpace P ι ρ₂) = 1 := (LetterDim.finrank_wdSpace l P ι _ L₂ _ _ hV₂).trans d₂
  obtain ⟨y, hy⟩ : ∃ y, wdMk P ι ρ₂ y ≠ 0 := by
    by_contra hc
    have h0 : (⊤ : Submodule ℂ (WDSpace P ι ρ₂)) = ⊥ := by
      rw [← span_wdMk, Submodule.span_eq_bot]
      rintro _ ⟨y, rfl⟩
      exact not_not.1 fun hn => hc ⟨y, hn⟩
    rw [← finrank_top, h0, finrank_bot] at e₂
    exact zero_ne_one e₂
  obtain ⟨y, rfl⟩ := ((End.isUnit_iff _).1 T.isUnit).2 y
  obtain ⟨x, rfl⟩ := (dQ_bij P f hf).2 y
  have hc : Commute (T : End ↥L₂.1 ↥(Dpst P ρ₂)) (weilD B h P ρ₂ σ) :=
    (t2 _).mul_right (Commute.units_zpow_right (u := phiU P ρ₂) t3 _)
  have k1 := line_smul e₁ (wdRho P ι B h hj ρ₁ σ) (ι z)
    (by rw [← DpstMap.charPol_wdPst P ι B h hj ρ₁ hV₁]; exact hz) (wdMk P ι ρ₁ x)
  have k2 := congrArg Φ k1
  rw [hΦ1, wdRho_mk, hΦ2, hΦ2] at k2
  have k3 : wdRho P ι B h hj ρ₂ σ (wdMk P ι ρ₂ ((T : End ↥L₂.1 ↥(Dpst P ρ₂)) (dQ P hf x))) =
      ι (g z) • wdMk P ι ρ₂ ((T : End ↥L₂.1 ↥(Dpst P ρ₂)) (dQ P hf x)) := by
    refine Eq.trans (congrArg (wdMk P ι ρ₂) ?_) k2
    exact ((congrArg (T : End ↥L₂.1 ↥(Dpst P ρ₂)) (dQ_weilD P B h hf σ x)).trans (LinearMap.congr_fun hc.eq _)).symm
  show ι (g z) ∈ ((wdPst P ι B h hj ρ₂).charPol σ).roots
  rw [DpstMap.charPol_wdPst P ι B h hj ρ₂ hV₂, mem_roots (LinearMap.charpoly_monic _).ne_zero,
    ← End.hasEigenvalue_iff_isRoot_charpoly]
  exact End.hasEigenvalue_of_hasEigenvector ⟨End.mem_eigenspace_iff.mpr k3, hy⟩

private theorem wdAt_eq_of {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L : FinExt l)
    (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (hm : mapRep (algebraMap ↥L.1 (Om l)) r₂ = r)
    (hV : IsPst P (B.repE L r₂)) : IsPstAt P B r ∧ wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L r₂) := by
  have k : L.1 ≤ (supExt L B.LL).1 := le_sup_left
  have hr : IsPstAt P B r := ⟨supExt L B.LL, mapRep (IntermediateField.inclusion k).toRingHom r₂,
    ⟨le_sup_right, by rw [← hm]; ext g i j; rfl⟩, GlobalTheory.PstExt.isPst_enlarge P B k r₂ hV⟩
  obtain ⟨L₁, r₁, m₁, V₁, e₁⟩ := wdAt_of_isPstAt ι B h hj hr
  have k₁ : L₁.1 ≤ (supExt L₁ L).1 := le_sup_left
  have k₂ : L.1 ≤ (supExt L₁ L).1 := le_sup_right
  have e : mapRep (IntermediateField.inclusion k₁).toRingHom r₁ =
      mapRep (IntermediateField.inclusion k₂).toRingHom r₂ := by
    ext g i j
    exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
      (m₁.2.trans hm.symm)
  refine ⟨hr, ?_⟩
  rw [e₁, BridgeParam.wdPst_enlarge P ι B h hj k₁ r₁ V₁, BridgeParam.wdPst_enlarge P ι B h hj k₂ r₂ hV, e]

end

theorem UpperTheory.Lit.CharWD.chCoef :
    ChCoef := by
  intro F Ω _ _ _ _ _ l _ A w ι h O _ _ _ Bw hj s κ ξ _ ⟨hp, hs, e⟩
  obtain ⟨L, r, hm, hV, e₁⟩ := wdAt_of_isPstAt ι Bw h hj hp
  let t : ↥L.1 ≃ₐ[ℚ_[l]] ↥(mapExt s L).1 := L.1.equivMap (s : Om l →ₐ[ℚ_[l]] Om l)
  let f : (Fin 1 → ↥L.1) ≃ₗ[ℚ_[l]] (Fin 1 → ↥(mapExt s L).1) := LinearEquiv.piCongrRight fun _ => t.toLinearEquiv
  let r₂ := mapRep (t : ↥L.1 →+* ↥(mapExt s L).1) r
  have hf : ∀ g v, f.toLinearMap (Bw.repE L r g v) = Bw.repE (mapExt s L) r₂ g (f.toLinearMap v) := fun g v =>
    funext fun i => RingHom.map_mulVec (t : ↥L.1 →+* ↥(mapExt s L).1)
      (r (Bw.e.symm g) : Matrix (Fin 1) (Fin 1) ↥L.1) v i
  have hm₂ : mapRep (algebraMap ↥(mapExt s L).1 (Om l)) r₂ = rk1 ((Units.map (s : Qbar l →* Qbar l)).comp κ) := by
    ext g i j
    have := congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin 1) (Om l) => s ((f g : Matrix (Fin 1) (Fin 1) (Om l)) i j))
      hm.2
    refine Eq.trans this ?_
    fin_cases i; fin_cases j
    simp [rk1]
  obtain ⟨hp₂, e₂⟩ := wdAt_eq_of _ ι Bw h hj _ _ r₂ hm₂ (isPst_equiv _ f hf hV)
  refine ⟨hp₂, hs.of_le fun σ hσ => ?_,
    ParamAboveModel.eq_lpOfChar h _ (GlobalTheory.Pst.Test.lpDim_wdAt _ ι Bw h hj _) _ _ fun σ => ?_⟩
  · have h1 : ξ σ = 1 := Units.ext (ι.injective ((congrArg Units.val hσ).trans (map_one ι).symm))
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]
  · rw [e₂]
    refine eig_conj _ ι Bw h hj s (by simp) (by simp) (t : ↥L.1 →+* ↥(mapExt s L).1) (fun _ => rfl) f hf
      (fun a v => funext fun i => map_mul t a (v i)) hV σ (ξ σ) ?_
    rw [← e₁, e, GlobalTheory.LocLanglands.eig_lpOfChar]
    exact Multiset.mem_singleton.2 rfl
