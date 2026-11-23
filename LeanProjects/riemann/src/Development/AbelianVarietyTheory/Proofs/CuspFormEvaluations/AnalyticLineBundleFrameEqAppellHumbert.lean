import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetRdMulInvPow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CorrOfJetsOfAnalyticFrameProducts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppLESpMapJetPt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJets
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPoints
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNormalisedIsoReadingOneAnalyticFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValEL

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

theorem tay_coord {N : ℕ} (k : Fin N) :
    tay (fun v : Fin N → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  classical
  have hθ : ContDiffAt ℂ ω (fun v : Fin N → ℂ => v k) 0 := (contDiff_apply ℂ ℂ k).contDiffAt
  refine TCPf.eq_of_cc _ _ fun l => ?_
  rcases l.eq_nil_or_concat with rfl | ⟨l', ⟨a, j⟩, rfl⟩
  · simp only [List.foldr_nil, constantCoeff_tay, TM.mD_zero, MvPowerSeries.constantCoeff_X, Pi.zero_apply]
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    have hd : (fun y : Fin N → ℂ => fderiv ℂ (fun v : Fin N → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j (1 : ℂ) : Fin N → ℂ) k := by
      funext y
      exact congrArg (fun T : (Fin N → ℂ) →L[ℂ] ℂ => T (Pi.single j 1))
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).fderiv
    rw [List.concat_eq_append, List.foldr_append, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [TM.pderiv_tay hθ, hd, TM.tay_const, MvPowerSeries.pderiv_X]
    congr 2
    by_cases h : k = j
    · subst h; simp
    · simp [h, Ne.symm h, Pi.single_apply]

theorem jetN_coord {n g : ℕ} (m : ℕ) (a : ℂ) (i : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => a * w i j) =
      Ideal.Quotient.mk _ (MvPolynomial.C a * MvPolynomial.X (i, j)) := by
  have h1 : jetOf m (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, j))) := by
    rw [jetOf, tay_coord, psJet, FBIdJet.psTrunc_eq, ← MvPolynomial.coe_X, FBIdJet.mk_trunc_coe]
  have h2 := jetOf_mul m (f := fun _ : Fin (n * g) → ℂ => a) (h := fun v => v (finProdFinEquiv (i, j)))
    contDiffAt_const (contDiff_apply ℂ ℂ _).contDiffAt
  rw [jetOf_const, h1] at h2
  have h3 : jetN m (fun w : Fin n → Fin g → ℂ => a * w i j) = renN n g m (jetOf m
    ((fun _ : Fin (n * g) → ℂ => a) * fun v => v (finProdFinEquiv (i, j)))) := rfl
  have h4 : renN n g m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, j)))) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
    show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
    rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply]
  rw [h3, h2, map_mul, AlgHom.commutes, map_mul, h4, ← MvPolynomial.algebraMap_eq]
  rfl

theorem jetSubstP_X {κ κ' : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (sb : κ → MvPolynomial κ' ℂ) (p : κ) :
    (jetSubstP m sb : Jet ℂ κ m →ₐ[ℂ] Jet ℂ κ' m) (psJet m (MvPowerSeries.X p)) =
      Ideal.Quotient.mk _ (sb p - MvPolynomial.C (MvPolynomial.constantCoeff (sb p))) := by
  rw [psJet, FBIdJet.psTrunc_eq, ← MvPolynomial.coe_X, FBIdJet.mk_trunc_coe]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  rw [MvPolynomial.aeval_X]

theorem jetAug_jetN {n g : ℕ} (m : ℕ) (f : (Fin n → Fin g → ℂ) → ℂ) :
    (jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) (jetN m f) = f 0 := by
  rw [jetN, renN, jetAug_jetMap, jetAug_jetOf]
  rfl

theorem valAt'_id_inj {W : (Sp ℂ).Opens} (hW : ⊤ ≤ W) {a b : Γ(Sp ℂ, W)}
    (h : valAt' (𝟙 (Sp ℂ)) W a = valAt' (𝟙 (Sp ℂ)) W b) : a = b := by
  obtain rfl : W = ⊤ := top_le_iff.mp hW
  rw [valAt'_of _ _ le_rfl, valAt'_of _ _ le_rfl] at h
  unfold valAt at h
  have := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 h
  simpa [Scheme.Hom.appLE] using this

theorem valAt'_spMap_toΓ {R : Type} [CommRing R] (f : R →+* ℂ) (a : R) :
    valAt' (spMap f) ⊤ (toΓ R a) = f a := by
  rw [valAt'_of _ _ le_rfl]
  have := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)) (toΓ R a)
  have h1 : (spMap f).appLE ⊤ ⊤ le_rfl = (spMap f).appTop := (Scheme.Hom.app_eq_appLE _).symm
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom (toΓ R a) = a := by simp [toΓ]
  unfold valAt
  rw [h1]
  exact this.trans (congrArg f h2)

theorem sameSum_cancel {X Y : Scheme.{0}} {P : Type} [Fintype P] (x x' : Y ⟶ X) (hx : x = x') (k : ℤ)
    (φ : Fin 1 ⊕ P → (Y ⟶ X)) (φ' : P → (Y ⟶ X)) (ε : P → ℤ) (h1 : ∀ i, φ (Sum.inl i) = x')
    (h2 : ∀ I, φ (Sum.inr I) = φ' I) :
    LB.SameSum (fun _ : Fin 1 => x) (fun _ => k) (Sum.elim φ φ')
      (fun i => k * Sum.elim (Sum.elim (fun _ => 1) fun I => -ε I) ε i) := by
  subst hx
  obtain rfl : φ = Sum.elim (fun _ => x) φ' := by
    funext i
    rcases i with i | I
    exacts [h1 i, h2 I]
  intro ψ
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc, ← Finset.sum_add_distrib,
    Finset.sum_eq_zero (s := (Finset.univ : Finset P)), add_zero]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : x = ψ <;> simp [h]
  · intro I _
    by_cases h : φ' I = ψ <;> simp [h]

theorem prod_zpow_sum {K : Type} {a : ℂ} (ha : a ≠ 0) (s : Finset K) (ε : K → ℤ) :
    ∏ k ∈ s, a ^ ε k = a ^ ∑ k ∈ s, ε k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.prod_insert hk, Finset.sum_insert hk, ih, zpow_add₀ ha]

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem jetMap_uniq {n m : ℕ} {ψ ψ' : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) (h' : Φ.JetMap m ψ' Λ') (e : Λ = Λ') :
    ψ = ψ' := by
  subst e
  obtain ⟨_, rfl⟩ := h
  obtain ⟨_, rfl⟩ := h'
  rfl

theorem e_zero_left : (Φ.e 0).left = x0 ≫ eSec A := by
  rw [(Φ.e_ker 0).2 Φ.lat.zero_mem, Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem jetMap_aug {n m : ℕ} {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) :
    spMap ((jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin n × Fin g) m →+* ℂ) ≫ ψ = (Φ.e 0).left := by
  obtain ⟨hol, rfl⟩ := h
  have hr : ((jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin n × Fin g) m →+* ℂ).comp
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) =
      ((jetAug : Jet ℂ (Fin 1 × Fin (n * g)) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin (n * g)) m →+* ℂ) :=
    RingHom.ext fun a => jetAug_jetMap _ (fun _ => X_mem_orig _) a
  rw [← Category.assoc, ← anSpMap_comp, hr, jetPt_aug]
  exact congrArg (fun z => (Φ.e z).left) (map_zero Λ)

theorem corr_rig {n m : ℕ} {K : Type} [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ)
    (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : Φ.JetRd m φ ε τ Λ)
    (hε : ∑ k, ε k = 1) :
    LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L φ ε τ (homAt x0 (jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ)).left)
      (rigT A L.L L.rig (overAt x0 ℂ) 1) := by
  have hid : spMap (algebraMap ℂ ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have h0 : (overAt x0 ℂ).hom = x0 := by
    show spMap (algebraMap ℂ ℂ) ≫ x0 = x0
    rw [hid, Category.id_comp]
  intro j j' _ _ hjj
  have hj : ∀ k, j k = j' 0 := fun k => hjj k 0 (by
    rw [h0, ← e_zero_left Φ]; exact jetMap_aug Φ (h.1 k))
  apply Units.ext
  set W := LB.wchart L.L (fun k => (homAt x0 (jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ)).left ≫ φ k) j ⊓
    LB.wchart L.L (fun _ : Fin 1 => (overAt x0 ℂ).hom ≫ eSec A) j' with hWdef
  by_cases hc : cpt ∈ W
  · have hW : (⊤ : (Sp ℂ).Opens) ≤ W := top_le_of_mem (x := 𝟙 (Sp ℂ)) hc
    have hW1 := hW.trans inf_le_left
    have hW2 := hW.trans inf_le_right
    haveI : IsLocalHom ((jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin n × Fin g) m →+* ℂ) :=
      ⟨fun a ha => isUnit_of_jetAug a ha.ne_zero⟩
    have hp : spMap ((jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin n × Fin g) m →+* ℂ) cpt =
        IsLocalRing.closedPoint _ := Spec_closedPoint
    have hT : ⊤ ≤ LB.wchart L.L φ j := by
      refine (Scheme.preimage_eq_top_of_closedPoint_mem
        (𝟙 (Spec (CommRingCat.of (Jet ℂ (Fin n × Fin g) m)))) (U := LB.wchart L.L φ j) ?_).ge
      have : spMap ((jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin n × Fin g) m →+* ℂ) cpt ∈
          LB.wchart L.L φ j := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hc.1 k
      rwa [hp] at this
    have hU : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U (j' 0) := by
      rw [e_zero_left Φ, ← h0]
      exact hW2.trans (LB.wchart_le _ _ _ 0)
    refine valAt'_id_inj hW ?_
    refine (TB.ValAt.valAt'_res (𝟙 (Sp ℂ)) inf_le_left hW _).trans (Eq.trans ?_ (TB.ValAt.valAt'_res (𝟙 (Sp ℂ)) inf_le_right hW _).symm)
    refine (TB.ValAt.valAt'_res (𝟙 (Sp ℂ)) (V := LB.wchart L.L _ j) _ hW1 _).trans ((valAt'_comp (𝟙 (Sp ℂ)) _ _ _).trans ?_)
    have hR : valAt' (𝟙 (Sp ℂ)) _ ((rigT A L.L L.rig (overAt x0 ℂ) 1).s j').val = Φ.fr (j' 0) 0 := by
      rw [Φ.fr_0 _ hU]
      simp only [rigT, zpow_one]
      refine (TB.ValAt.valAt'_res (𝟙 (Sp ℂ)) (V := LB.wchart L.L _ j') _ hW2 _).trans ((valAt'_comp (𝟙 (Sp ℂ)) _ _ _).trans ?_)
      rw [Category.id_comp, h0]
      rfl
    refine Eq.trans ?_ hR.symm
    rw [Category.id_comp]
    refine (TB.ValAt.valAt'_res _ hT le_rfl _).symm.trans ?_
    refine (congrArg (valAt' _ ⊤) (h.2 j hT)).trans ((valAt'_spMap_toΓ _ _).trans ?_)
    refine (jetAug_jetN m _).trans ?_
    have hne := Φ.fr_ne _ _ hU
    simp only [map_zero, hj]
    rw [prod_zpow_sum hne, hε, zpow_one]
  · have hb : W = ⊥ := by
      refine le_bot_iff.1 fun p hp => hc ?_
      rwa [Subsingleton.elim cpt p]
    haveI : Subsingleton Γ(Sp ℂ, W) := by rw [hb]; infer_instance
    exact Subsingleton.elim (α := Γ(Sp ℂ, W)) _ _

end General

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] [StarRing (𝓞 E)] {y : FrPt Xo c ℂ} {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

def graphL (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : (Fin 1 → Fin g → ℂ) →ₗ[ℂ] (Fin 2 → Fin g → ℂ) :=
  LinearMap.pi ![LinearMap.proj 0, tyAct ty a ∘ₗ LinearMap.proj 0]

omit [IsCMField E] [StarRing (𝓞 E)] in
theorem graphL_apply (a : 𝓞 E) (w : Fin 1 → Fin g → ℂ) : graphL ty a w = ![w 0, tyAct ty a (w 0)] := by
  funext i
  fin_cases i <;> rfl

theorem jetRd_prim (wP : PrimTy H Xo) (hP : IsPrim wP) (m : ℕ) :
    Φ.toAnFr.JetRd (n := 1) m _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wP (Φ.jx m).left)
      (Sum.elim (fun _ => LinearMap.proj 0) fun I => psumL 2 g I ∘ₗ graphL ty H.w0) := by
  obtain ⟨hq, hx⟩ := (GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ 1 m).2.2.2.2
  rw [hx]
  refine GlobalTheory.AnValJetGlob.jetRd_pullGen _ _ _ _ _ Φ.toAnFr 1 m _ _ _ _ wP _ _ hq fun v => ?_
  have := (GlobalTheory.AnVal.PrimRd.prim_reading E H Dw l Xo c y g ty el Φ).2 wP hP (colsOf 1 g v 0)
  convert this using 1
  · rfl
  funext k
  rcases k with k | I
  · rfl
  · show psumL 2 g I (graphL ty H.w0 _) = _
    rw [graphL_apply]
    rfl

theorem jetRd_pe (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (m : ℕ) :
    Φ.toAnFr.JetRd (n := 1) m _ _
      (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn g m ![0] ((anFB ty).A.act H.w0 j)])
      (fun I => psumL 2 g I ∘ₗ graphL ty H.w0) := by
  refine GlobalTheory.JetLinSub.jetRd_linSubst _ _ _ _ _ Φ.toAnFr 2 1 m (graphL ty H.w0) _ (fun p => ?_) _ _ _ (e m) _ (he m).2
  obtain ⟨i, j⟩ := p
  rw [jetSubstP_X]
  fin_cases i
  · have := jetN_coord (n := 1) m 1 0 j
    simp only [_root_.one_mul, map_one] at this
    refine Eq.trans ?_ this.symm
    simp
  · refine Eq.trans ?_ (jetN_coord (n := 1) m (ty j (H.w0 : E)) 0 j).symm
    have hr : psIn g m ![0] ((anFB ty).A.act H.w0 j) = psTrunc m (linAct ty H.w0 j) := by
      have : (fun p : Fin 1 × Fin g => ((![0] : Fin 1 → Fin 1) p.1, p.2)) = id := by
        funext p
        exact Prod.ext (Subsingleton.elim _ _) rfl
      rw [psIn, this, MvPolynomial.rename_id]
      rfl
    have hc := constantCoeff_of_mem_orig (FBIdJet.psTrunc_mem_orig m _ (cc_linAct ty H.w0 j))
    show Ideal.Quotient.mk _ (psIn g m ![0] ((anFB ty).A.act H.w0 j) -
      MvPolynomial.C (MvPolynomial.constantCoeff (psIn g m ![0] ((anFB ty).A.act H.w0 j)))) = _
    rw [hr, hc, map_zero, sub_zero, FBIdJet.psTrunc_eq, ← FBIdJet.mk_trunc_coe m (MvPolynomial.C _ * _)]
    simp [linAct]

end Pt

theorem eL_appellHumbert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ (e : ∀ m, FrTy y g Φ.jx m) (wP : PrimTy H Xo), Φ.IsAnE e → IsPrim wP → (∀ (m k : ℕ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y g Φ.jx (anFB ty).A.act e wP m) k)) ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (eL y g Φ.jx (anFB ty).A.act e wP 0) (homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) 0 →ₐ[ℂ] ℂ)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x ℂ) 1) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hI e wP he hP
  have key := fun m => GlobalTheory.AnVal.jetRd_mul_inv_pow _ _ _ _ _ Φ.toAnFr 1 m _ _ _ _ _ _ _ _ _ _
    (jetRd_prim Φ wP hP m) (jetRd_pe Φ e he m)
  refine ⟨fun m k τ hτ => ?_, corr_rig Φ.toAnFr _ _ _ _ (key 0).1 ?_⟩
  · have h2 := (GlobalTheory.AnVal.jetRd_mul_inv_pow _ _ _ _ _ Φ.toAnFr 1 m _ _ _ _ _ _ _ _ _ _ (key m).1 hτ).2.2 k
    refine GlobalTheory.AnVal.JetCorr.corr_of_jetRd _ _ _ _ _ Φ.toAnFr hI 1 m _ _ _ _ _ _ _ _ _ _ hτ h2 ?_
    exact sameSum_cancel _ _ rfl _ _ _ _ (fun _ => Category.comp_id _) fun I =>
      jetMap_uniq Φ.toAnFr ((jetRd_prim Φ wP hP m).1 (Sum.inr I)) ((jetRd_pe Φ e he m).1 I) rfl
  · simp [Fintype.sum_sum_type]

end GlobalTheory.AnValEL
