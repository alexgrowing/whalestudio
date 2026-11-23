import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumTwoG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open Module TensorProduct GlobalTheory.Pst.DpstMap
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Split
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
  {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀]
  [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
  [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
  {ρ₀ : Representation ↥LL.1 ↥(GK K) V₀} {ρ₁ : Representation ↥LL.1 ↥(GK K) V₁}
  {ρ₂ : Representation ↥LL.1 ↥(GK K) V₂}
private theorem tensV_section (p : V₁ →ₗ[↥LL.1] V₂) (s : V₂ →ₗ[↥LL.1] V₁) (hps : ∀ v, p (s v) = v)
    (x : V₂ ⊗[ℚ_[l]] Bst P) : tensV P p (tensV P s x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hps]
  | add x y hx hy => simp only [map_add, hx, hy]
variable [FiniteDimensional ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₂]
private theorem isPst_split {AI : LocAinf l P} (T : LocTied l P AI) {i : V₀ →ₗ[↥LL.1] V₁} {p : V₁ →ₗ[↥LL.1] V₂}
    {s : V₂ →ₗ[↥LL.1] V₁} (hi : ∀ g v, i (ρ₀ g v) = ρ₁ g (i v)) (hp : ∀ g v, p (ρ₁ g v) = ρ₂ g (p v))
    (hs : ∀ g v, s (ρ₂ g v) = ρ₁ g (s v)) (h1 : Function.Injective i) (h2 : Function.Exact i p)
    (hps : ∀ v, p (s v) = v) (hV₀ : IsPst P ρ₀) (hV₂ : IsPst P ρ₂) : IsPst P ρ₁ := by
  obtain ⟨hdom, hfrac, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V₀ := Module.Finite.trans ↥LL.1 V₀
  haveI : FiniteDimensional ℚ_[l] V₁ := Module.Finite.trans ↥LL.1 V₁
  haveI : FiniteDimensional ℚ_[l] V₂ := Module.Finite.trans ↥LL.1 V₂
  have b₁ := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation P hdom hfrac ρ₁
  haveI f₁ : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁) :=
    Module.rank_lt_aleph0_iff.mp (b₁.trans_lt (Cardinal.natCast_lt_aleph0))
  obtain ⟨f₀, c₀⟩ := (isPst_iff P ρ₀).1 hV₀
  obtain ⟨f₂, c₂⟩ := (isPst_iff P ρ₂).1 hV₂
  obtain ⟨hinj, hex⟩ := UpperTheory.V.Loc.PstExact.dmap_exact P hi hp h1 h2
  have inj : Function.Injective (UpperTheory.V.Loc.PstExact.dUr P hi) := fun x y h => hinj h
  have sur : Function.Surjective (UpperTheory.V.Loc.PstExact.dUr P hp) := fun y =>
    ⟨toUr P ρ₁ (dmap P hs ((toUr P ρ₂).symm y)), Subtype.ext (tensV_section P p s hps _)⟩
  have ex : Function.Exact (UpperTheory.V.Loc.PstExact.dUr P hi) (UpperTheory.V.Loc.PstExact.dUr P hp) := fun y => hex y
  have e := (UpperTheory.V.Loc.PstExact.dUr P hp).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 sur, finrank_top, LinearMap.exact_iff.mp ex, LinearMap.finrank_range_of_inj inj] at e
  have e' := (p.restrictScalars ℚ_[l]).finrank_range_add_finrank_ker
  have exq : Function.Exact (i.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := h2
  rw [LinearMap.exact_iff.mp exq, LinearMap.finrank_range_of_inj (f := i.restrictScalars ℚ_[l]) h1,
    LinearMap.range_eq_top.2 (show Function.Surjective (p.restrictScalars ℚ_[l]) from fun v => ⟨s v, hps v⟩),
    finrank_top] at e'
  exact (isPst_iff P ρ₁).2 ⟨f₁, by omega⟩
end Split
section Sum
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a b : ℕ}
private theorem isPst_sum (T : LocTied l P AI) {L : FinExt l} (s : ↥Gw →* GL (Fin a) ↥L.1) (s' : ↥Gw →* GL (Fin b) ↥L.1)
    (h : IsPst P (Bw.repE L s)) (h' : IsPst P (Bw.repE L s')) : IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) := by
  let e : (Fin (a + b) → ↥L.1) ≃ₗ[↥L.1] (Fin a → ↥L.1) × (Fin b → ↥L.1) :=
    (LinearEquiv.funCongrLeft ↥L.1 ↥L.1 finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ ↥L.1 ↥L.1)
  have he : ∀ g v, e (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s') g v) =
      (Bw.repE L s g (e v).1, Bw.repE L s' g (e v).2) := by
    intro g v
    rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, GlobalTheory.BCGal.sumRep_val]
    ext i <;>
      simp [e, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl
  have he' : ∀ g x, e.symm (Bw.repE L s g x.1, Bw.repE L s' g x.2) =
      Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s') g (e.symm x) := by
    intro g x
    apply e.injective
    rw [he, e.apply_symm_apply, e.apply_symm_apply]
  refine isPst_split P T (i := e.symm.toLinearMap ∘ₗ LinearMap.inl ↥L.1 _ _)
    (p := LinearMap.snd ↥L.1 _ _ ∘ₗ e.toLinearMap) (s := e.symm.toLinearMap ∘ₗ LinearMap.inr ↥L.1 _ _)
    (ρ₀ := Bw.repE L s) (ρ₂ := Bw.repE L s') (fun g v => ?_) (fun g v => ?_) (fun g v => ?_) ?_ ?_ ?_ h h'
  · have := he' g (v, 0)
    simpa using this
  · simp [he]
  · have := he' g (0, v)
    simpa using this
  · intro x y hxy
    simpa using hxy
  · intro y
    constructor
    · intro hy
      refine ⟨(e y).1, ?_⟩
      apply e.injective
      have hy' : (e y).2 = 0 := hy
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply, e.apply_symm_apply]
      exact Prod.ext rfl hy'.symm
    · rintro ⟨x, rfl⟩
      simp
  · intro v
    simp
private theorem isPstAt_sum (T : LocTied l P AI) {r : ↥Gw →* GL (Fin a) (Om l)} {r' : ↥Gw →* GL (Fin b) (Om l)}
    (h : IsPstAt P Bw r) (h' : IsPstAt P Bw r') : IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
  obtain ⟨L₁, r₁, m₁, p₁⟩ := h
  obtain ⟨L₂, r₂, m₂, p₂⟩ := h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  exact ⟨supExt L₁ L₂, _, ⟨n₁.1, by rw [GlobalTheory.Pst.SumParam.mapRep_sumRep, n₁.2, n₂.2]⟩,
    isPst_sum Bw T _ _ (GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge P Bw l₁ r₁ p₁) (GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge P Bw l₂ r₂ p₂)⟩
end Sum
theorem UpperTheory.V.Z.Win.Gu.sumTwoG_of_printsH_gdLaws_sumAway_sumHTAt :
    _root_.UpperTheory.V.Af.HypothesesH' → GdLaws → SumAway → SumHTAt → SumTwoG := by
  intro _ hG hA hT E Ω _ _ _ _ _ l _ ι a b r r' p p' HT HT' C C'
  obtain ⟨T⟩ := Loc.tiedP l
  have hv := GlobalTheory.BCGal.cont_sumRep r r' (Units.continuous_val.comp C.cont) (Units.continuous_val.comp C'.cont)
  have hc : Continuous (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    simp only [← map_inv]
    exact hv.comp continuous_inv
  refine ⟨hc, GlobalTheory.BCGal.ss_sumRep r r' C.ss C'.ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩
  · exact hT E Ω l a b r r' C.cont C'.cont HT HT' w
      (C.ht w fun A h rc hrc => (((hG E Ω A w h).1 _ _).1 (hg A h rc hrc)).1)
      (C'.ht w fun A h rc hrc => (((hG E Ω A w h).1 _ _).1 (hg A h rc hrc)).2)
  · obtain ⟨a1, b1⟩ := C.par w A h rc hrc
    obtain ⟨a2, b2⟩ := C'.par w A h rc hrc
    have sp := ((hG E Ω A w h).1 (p w A h rc) (p' w A h rc)).1
    refine And.intro (fun hw => ?_) (fun O _ _ _ Bw hj hg => ?_)
    · obtain ⟨x, hx, kx⟩ := a1 hw
      obtain ⟨x', hx', kx'⟩ := a2 hw
      refine Exists.intro (x.lpSum x') (And.intro (hA E Ω l ι a b r r' C.cont C'.cont w hw A h _ _ hx hx') fun g => ?_)
      rw [kx (sp g).1, kx' (sp g).2]
    · obtain ⟨p1, e1⟩ := b1 O Bw hj (sp hg).1
      obtain ⟨p2, e2⟩ := b2 O Bw hj (sp hg).2
      have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F := E) A).subtype =
          Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (Dec (F := E) A).subtype) (r'.comp (Dec (F := E) A).subtype) := by
        ext g i j
        rfl
      have p3 := isPstAt_sum Bw T p1 p2
      rw [e]
      exact ⟨p3, by rw [GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l _ _ ⟨T⟩ ι E Ω A w O Bw h hj a b _ _ p1 p2 p3, e1, e2]⟩
end
