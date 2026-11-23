import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetF

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.JetUniq

theorem jet_zero_ext {κ : Type} (a b : Jet ℂ κ 0)
    (h : (jetAug : Jet ℂ κ 0 →ₐ[ℂ] ℂ) a = (jetAug : Jet ℂ κ 0 →ₐ[ℂ] ℂ) b) : a = b := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hcc : ∀ R : MvPolynomial κ ℂ, MvPolynomial.aeval (fun _ => (0 : ℂ)) R = MvPolynomial.constantCoeff R := by
    intro R
    induction R using MvPolynomial.induction_on <;> simp_all
  change MvPolynomial.aeval (fun _ => (0 : ℂ)) P = MvPolynomial.aeval (fun _ => (0 : ℂ)) Q at h
  rw [hcc, hcc] at h
  rw [Ideal.Quotient.eq, zero_add, pow_one]
  change P - Q ∈ Ideal.span (Set.range MvPolynomial.X)
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro d hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, sub_ne_zero] at hd
    exact hd h
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hd0
  exact ⟨i, Set.mem_univ i, hi⟩

private theorem snd_aeval_eps_monomial_eq_ite {κ : Type} [DecidableEq κ] (ℓ : κ) (e : κ →₀ ℕ) (c : ℂ) :
    (MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0)
      (MvPolynomial.monomial e c)).snd = if e = Finsupp.single ℓ 1 then c else 0 := by
  rw [MvPolynomial.aeval_monomial]
  split_ifs with he
  · subst he
    simp [Finsupp.prod_single_index]
    rfl
  · have hp : (e.prod fun i k => (if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0) ^ k).snd = 0 := by
      by_cases hs : ∃ i ∈ e.support, i ≠ ℓ
      · obtain ⟨i, hi, hiℓ⟩ := hs
        rw [Finsupp.prod, Finset.prod_eq_zero hi (by rw [if_neg hiℓ]; exact zero_pow (Finsupp.mem_support_iff.mp hi))]
        rfl
      · have he' : e = Finsupp.single ℓ (e ℓ) := by
          ext i
          by_cases hi : i = ℓ
          · subst hi
            simp
          · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
            by_contra h0
            exact hs ⟨i, Finsupp.mem_support_iff.mpr h0, hi⟩
        have hk : e ℓ ≠ 1 := fun h1 => he (by rw [he', h1])
        rw [he', Finsupp.prod_single_index (by simp), if_pos rfl]
        rcases Nat.lt_or_gt_of_ne hk with h0 | h2
        · rw [show e ℓ = 0 by omega, pow_zero]
          rfl
        · obtain ⟨j, hj⟩ : ∃ j, e ℓ = j + 2 := ⟨e ℓ - 2, by omega⟩
          rw [hj, pow_add, pow_two, DualNumber.eps_mul_eps, mul_zero]
          rfl
    rw [TrivSqZeroExt.snd_mul, hp, smul_zero, zero_add]
    exact smul_zero _

private theorem single_one_mem_degLE_succ {κ : Type} [Fintype κ] [DecidableEq κ] (k : ℕ) (ℓ : κ) :
    Finsupp.single ℓ 1 ∈ (degLE (k + 1) : Finset (κ →₀ ℕ)) := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨fun i => ⟨Finsupp.single ℓ 1 i, by rw [Finsupp.single_apply]; split_ifs <;> omega⟩,
    Finset.mem_univ _, ?_⟩, ?_⟩
  · ext i
    simp
  · simp [Finsupp.sum_single_index]

private theorem snd_jetTan_psJet_succ_eq_coeff_single {κ : Type} [Fintype κ] [DecidableEq κ] (k : ℕ) (ℓ : κ)
    (F : MvPowerSeries κ ℂ) :
    (jetTan ℓ (psJet (k + 1) F) : DualNumber ℂ).snd = MvPowerSeries.coeff (Finsupp.single ℓ 1) F := by
  change (MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0)
    (psTrunc (k + 1) F)).snd = _
  unfold psTrunc
  rw [map_sum, TrivSqZeroExt.snd_sum]
  simp_rw [snd_aeval_eps_monomial_eq_ite]
  rw [Finset.sum_ite_eq', if_pos (single_one_mem_degLE_succ k ℓ)]

theorem fderiv_eq_of_jetOf {g : ℕ} (m : ℕ) (θ θ' : (Fin g → ℂ) → ℂ)
    (h : PullbackSections.jetOf (m + 1) θ = PullbackSections.jetOf (m + 1) θ') : fderiv ℂ θ 0 = fderiv ℂ θ' 0 := by
  have hc : ∀ j : Fin g, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (PullbackSections.tay θ 0) =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (PullbackSections.tay θ' 0) := by
    intro j
    have := congrArg (fun a => (jetTan ((0 : Fin 1), j) a : DualNumber ℂ).snd) h
    change (jetTan ((0 : Fin 1), j) (psJet (m + 1) (PullbackSections.tay θ 0)) : DualNumber ℂ).snd =
      (jetTan ((0 : Fin 1), j) (psJet (m + 1) (PullbackSections.tay θ' 0)) : DualNumber ℂ).snd at this
    rwa [snd_jetTan_psJet_succ_eq_coeff_single, snd_jetTan_psJet_succ_eq_coeff_single] at this
  have hd : ∀ j : Fin g, fderiv ℂ θ 0 (Pi.single j 1) = fderiv ℂ θ' 0 (Pi.single j 1) := by
    intro j
    have hm : ∀ φ : (Fin g → ℂ) → ℂ,
        PullbackSections.mD φ 0 (PullbackSections.dirs (Finsupp.single ((0 : Fin 1), j) 1)) = fderiv ℂ φ 0 (Pi.single j 1) := by
      intro φ
      have key : ∀ (w : Fin g → ℂ) (l : List (Fin g → ℂ)), l = [w] →
          iteratedFDeriv ℂ l.length φ 0 (fun i => l.get i) = fderiv ℂ φ 0 w := by
        intro w l hl
        subst hl
        exact iteratedFDeriv_one_apply _
      simp only [PullbackSections.dirs, Finsupp.toMultiset_single, one_smul, Multiset.map_singleton]
      unfold PullbackSections.mD PullbackSections.lD
      exact key _ _ (Multiset.toList_singleton _)
    have e1 := PullbackSections.coeff_tay_zero θ (Finsupp.single ((0 : Fin 1), j) 1)
    have e2 := PullbackSections.coeff_tay_zero θ' (Finsupp.single ((0 : Fin 1), j) 1)
    rw [hc j] at e1
    rw [← hm θ, ← hm θ']
    exact e1.symm.trans e2
  ext v
  rw [PullbackSections.sum_single_smul v]
  simp only [map_sum, map_smul, hd]

def renInv (n g m : ℕ) : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (n * g)) m :=
  jetMap (fun p => MvPolynomial.X ((0 : Fin 1), finProdFinEquiv p)) fun _ => X_mem_orig _

theorem renInv_renN (n g m : ℕ) (a : Jet ℂ (Fin 1 × Fin (n * g)) m) : renInv n g m (renN n g m a) = a := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hcomp : ((MvPolynomial.aeval fun p : Fin n × Fin g =>
        (MvPolynomial.X ((0 : Fin 1), finProdFinEquiv p) : MvPolynomial (Fin 1 × Fin (n * g)) ℂ)).comp
      (MvPolynomial.aeval fun p : Fin 1 × Fin (n * g) =>
        (MvPolynomial.X (finProdFinEquiv.symm p.2) : MvPolynomial (Fin n × Fin g) ℂ))) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    rw [Fin.fin_one_eq_zero i]
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, AlgHom.id_apply]
    rw [Equiv.apply_symm_apply]
  change Ideal.Quotient.mk _ ((MvPolynomial.aeval fun p : Fin n × Fin g =>
        (MvPolynomial.X ((0 : Fin 1), finProdFinEquiv p) : MvPolynomial (Fin 1 × Fin (n * g)) ℂ))
      ((MvPolynomial.aeval fun p : Fin 1 × Fin (n * g) =>
        (MvPolynomial.X (finProdFinEquiv.symm p.2) : MvPolynomial (Fin n × Fin g) ℂ)) P)) = Ideal.Quotient.mk _ P
  rw [← AlgHom.comp_apply, hcomp, AlgHom.id_apply]

theorem cancel_renN {Y : Scheme.{0}} (n g m : ℕ) (x y : Sp (Jet ℂ (Fin 1 × Fin (n * g)) m) ⟶ Y)
    (h : spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ x =
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ y) : x = y := by
  have hc : spMap (renInv n g m : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) ≫
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) = 𝟙 _ := by
    unfold spMap
    rw [← Spec.map_comp]
    have hid : CommRingCat.ofHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        CommRingCat.ofHom (renInv n g m : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) = 𝟙 _ := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact renInv_renN n g m a
    rw [hid, Spec.map_id]
  calc x = (spMap (renInv n g m : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) ≫
        spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m)) ≫ x := by
        rw [hc, Category.id_comp]
    _ = (spMap (renInv n g m : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) ≫
        spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m)) ≫ y := by
        rw [Category.assoc, h, ← Category.assoc]
    _ = y := by rw [hc, Category.id_comp]

private theorem appLE_specMap_comp_fromSpecStalk_eq_germ {Y : Scheme.{0}} {y : Y} {R : CommRingCat.{0}}
    (φ : Y.presheaf.stalk y ⟶ R) (U : Y.Opens) (hy : y ∈ U) (hx : ⊤ ≤ (Spec.map φ ≫ Y.fromSpecStalk y) ⁻¹ᵁ U) :
    (Spec.map φ ≫ Y.fromSpecStalk y).appLE U ⊤ hx = Y.presheaf.germ U y hy ≫ φ ≫ (Scheme.ΓSpecIso R).inv := by
  rw [Scheme.Hom.comp_appLE, Scheme.fromSpecStalk_app hy]
  have hx2 : ⊤ ≤ Spec.map φ ⁻¹ᵁ (Y.fromSpecStalk y ⁻¹ᵁ U) := hx
  change (Y.presheaf.germ U y hy ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv ≫
      (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE (le_top : Y.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op) ≫
      (Spec.map φ).appLE (Y.fromSpecStalk y ⁻¹ᵁ U) ⊤ hx2 = _
  simp only [Category.assoc]
  rw [Scheme.Hom.map_appLE, Scheme.ΓSpecIso_inv_naturality]
  congr 2

set_option backward.isDefEq.respectTransparency false in

theorem jetOf_eq_of_jetPt {g : ℕ} {Y : Scheme.{0}} (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (hol' : IsHolFam e') (m : ℕ) (h : PullbackSections.jetPt e hol m = PullbackSections.jetPt e' hol' m) (U : Y.Opens) (hU : e 0 cpt ∈ U)
    (hU' : e' 0 cpt ∈ U) (f : Γ(Y, U)) :
    PullbackSections.jetOf m (fun z => valAt' (e z) U f) = PullbackSections.jetOf m (fun z => valAt' (e' z) U f) := by
  have hx_of : ∀ (e₀ : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (h₀ : IsHolFam e₀), e₀ 0 cpt ∈ U →
      ⊤ ≤ (PullbackSections.jetPt e₀ h₀ m) ⁻¹ᵁ U := by
    intro e₀ h₀ hU₀ p _
    have key2 : ∀ q, Y.fromSpecStalk ((e₀ 0) cpt) q ∈ U := fun q => by
      have hr : Y.fromSpecStalk ((e₀ 0) cpt) q ∈ Set.range (Y.fromSpecStalk ((e₀ 0) cpt)) := ⟨q, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hr
      exact Specializes.mem_open hr U.isOpen hU₀
    exact key2 _
  have key : ∀ (e₀ : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (h₀ : IsHolFam e₀), e₀ 0 cpt ∈ U →
      ∀ hx : ⊤ ≤ (PullbackSections.jetPt e₀ h₀ m) ⁻¹ᵁ U,
      ((PullbackSections.jetPt e₀ h₀ m).appLE U ⊤ hx).hom f = toΓ _ (PullbackSections.jetOf m fun z => valAt' (e₀ z) U f) := by
    intro e₀ h₀ hU₀ hx
    unfold PullbackSections.jetPt nbhdPt at hx ⊢
    rw [appLE_specMap_comp_fromSpecStalk_eq_germ _ U hU₀, ← Category.assoc]
    unfold nbhdLift TopCat.Presheaf.germ
    rw [colimit.ι_desc]
    rfl
  have hx := hx_of e hol hU
  have hx' := hx_of e' hol' hU'
  have heq : ((PullbackSections.jetPt e hol m).appLE U ⊤ hx).hom f = ((PullbackSections.jetPt e' hol' m).appLE U ⊤ hx').hom f := by
    have hgen : ∀ (x x' : Sp (Jet ℂ (Fin 1 × Fin g) m) ⟶ Y) (_ : x = x') (hx : ⊤ ≤ x ⁻¹ᵁ U)
        (hx' : ⊤ ≤ x' ⁻¹ᵁ U), (x.appLE U ⊤ hx).hom f = (x'.appLE U ⊤ hx').hom f := by
      intro x x' hxx _ _
      subst hxx
      rfl
    exact hgen _ _ h hx hx'
  rw [key e hol hU hx, key e' hol' hU' hx'] at heq
  have hinj : Function.Injective (toΓ (Jet ℂ (Fin 1 × Fin g) m)) := by
    intro a b hab
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Jet ℂ (Fin 1 × Fin g) m))).hom.hom hab
    simpa [toΓ] using this
  exact hinj heq

def colsL (n g : ℕ) : (Fin (n * g) → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ) where
  toFun := colsOf n g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem colsOf_surj (n g : ℕ) : Function.Surjective (colsOf n g) := by
  intro w
  refine ⟨fun k => w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2, ?_⟩
  funext i j
  simp [colsOf]

theorem fderiv_comp_lin {a b : ℕ} (θ : (Fin b → ℂ) → ℂ) (hθ : DifferentiableAt ℂ θ 0)
    (T : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ)) (v : Fin a → ℂ) :
    fderiv ℂ (fun z => θ (T z)) 0 v = fderiv ℂ θ 0 (T v) := by
  set Tc := LinearMap.toContinuousLinearMap T with hTc
  have hT : HasFDerivAt (⇑Tc) Tc 0 := Tc.hasFDerivAt
  have hθ' : HasFDerivAt θ (fderiv ℂ θ 0) (Tc 0) := by
    rw [map_zero]
    exact hθ.hasFDerivAt
  change fderiv ℂ (θ ∘ ⇑Tc) 0 v = _
  rw [(hθ'.comp (0 : Fin a → ℂ) hT).fderiv]
  rfl

private theorem zero_mem_degLE' {κ : Type} [Fintype κ] [DecidableEq κ] (k : ℕ) :
    (0 : κ →₀ ℕ) ∈ (degLE k : Finset (κ →₀ ℕ)) := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨fun _ => ⟨0, by omega⟩, Finset.mem_univ _, ?_⟩, by simp⟩
  ext i
  simp

private theorem jetAug_jetN_zero_eq_apply_zero {n g : ℕ} (F : (Fin n → Fin g → ℂ) → ℂ) :
    (jetAug : Jet ℂ (Fin n × Fin g) 0 →ₐ[ℂ] ℂ) (jetN 0 F) = F 0 := by
  have hcc : ∀ {κ : Type} (R : MvPolynomial κ ℂ),
      MvPolynomial.aeval (fun _ => (0 : ℂ)) R = MvPolynomial.constantCoeff R := by
    intro κ R
    induction R using MvPolynomial.induction_on <;> simp_all
  have hc2 : (MvPolynomial.aeval (fun _ => (0 : ℂ))).comp (MvPolynomial.aeval fun p : Fin 1 × Fin (n * g) =>
      (MvPolynomial.X (finProdFinEquiv.symm p.2) : MvPolynomial (Fin n × Fin g) ℂ)) =
      MvPolynomial.aeval (fun _ => (0 : ℂ)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp
  change MvPolynomial.aeval (fun _ => (0 : ℂ)) ((MvPolynomial.aeval fun p : Fin 1 × Fin (n * g) =>
      (MvPolynomial.X (finProdFinEquiv.symm p.2) : MvPolynomial (Fin n × Fin g) ℂ))
      (psTrunc 0 (PullbackSections.tay (fun v => F (colsOf n g v)) 0))) = F 0
  rw [← AlgHom.comp_apply, hc2, hcc]
  unfold psTrunc
  rw [map_sum]
  simp only [MvPolynomial.constantCoeff_monomial]
  rw [Finset.sum_ite_eq', if_pos (zero_mem_degLE' 0)]
  have e1 := PullbackSections.coeff_tay_zero (fun v => F (colsOf n g v)) 0
  have hf : PullbackSections.fct (0 : Fin 1 × Fin (n * g) →₀ ℕ) = 1 := by simp [PullbackSections.fct]
  have hdir : PullbackSections.dirs (0 : Fin 1 × Fin (n * g) →₀ ℕ) = 0 := by simp [PullbackSections.dirs]
  rw [hf, _root_.one_mul, hdir] at e1
  rw [e1]
  have key : ∀ l : List (Fin (n * g) → ℂ), l = [] →
      iteratedFDeriv ℂ l.length (fun v => F (colsOf n g v)) 0 (fun i => l.get i) = F (colsOf n g 0) := by
    intro l hl
    subst hl
    exact iteratedFDeriv_zero_apply _
  unfold PullbackSections.mD PullbackSections.lD
  exact key _ (by simp)

theorem jet_uniq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), Φ.Imm → ∀ (n m : ℕ) (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetMap m ψ Λ → Φ.JetMap m ψ Λ' → ∀ f : (Fin g → ℂ) → ℂ, jetN m (fun w => f (Λ w)) = jetN m (fun w => f (Λ' w)) := by
  intro S A _ _ L x0 g Φ hImm n m ψ Λ Λ' hΛ hΛ' f
  rcases m with _ | k
  · apply jet_zero_ext
    rw [jetAug_jetN_zero_eq_apply_zero, jetAug_jetN_zero_eq_apply_zero]
    simp only [map_zero]
  · have hΛΛ : Λ = Λ' := by
      obtain ⟨hol, hψ⟩ := hΛ
      obtain ⟨hol', hψ'⟩ := hΛ'
      have hpt := cancel_renN n g (k + 1) _ _ (hψ.symm.trans hψ')
      apply LinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := colsOf_surj n g w
      by_contra hne
      obtain ⟨U, F, hU, hder⟩ := hImm _ (sub_ne_zero.mpr hne)
      have hU0 : (Φ.e 0).left cpt ∈ U := hU trivial
      have hz : Φ.e (Λ (colsOf n g 0)) = Φ.e 0 := by
        rw [show colsOf n g 0 = 0 from rfl, map_zero]
      have hz' : Φ.e (Λ' (colsOf n g 0)) = Φ.e 0 := by
        rw [show colsOf n g 0 = 0 from rfl, map_zero]
      have hjet := jetOf_eq_of_jetPt _ _ hol hol' (k + 1) hpt U
        (by show (Φ.e (Λ (colsOf n g 0))).left cpt ∈ U; rw [hz]; exact hU0)
        (by show (Φ.e (Λ' (colsOf n g 0))).left cpt ∈ U; rw [hz']; exact hU0) F
      have hfd := fderiv_eq_of_jetOf k _ _ hjet
      obtain ⟨hopen, hdiff⟩ := Φ.hol U F
      have hθ : DifferentiableAt ℂ (fun z => valAt' (Φ.e z).left U F) 0 :=
        hdiff.differentiableAt (hopen.mem_nhds hU)
      have h1 := fderiv_comp_lin _ hθ (Λ ∘ₗ colsL n g) v
      have h2 := fderiv_comp_lin _ hθ (Λ' ∘ₗ colsL n g) v
      apply hder
      rw [map_sub, sub_eq_zero]
      exact h1.symm.trans ((congrArg (fun T => T v) hfd).trans h2)
    subst hΛΛ
    rfl

end GlobalTheory.AnVal.JetUniq
