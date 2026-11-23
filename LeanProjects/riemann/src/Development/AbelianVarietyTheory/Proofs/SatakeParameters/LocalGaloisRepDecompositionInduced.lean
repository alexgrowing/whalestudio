import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
open GlobalTheory.WeilDeligne Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace GlobalTheory.PstLine

section Letter

variable {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* End LL D)
  (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) {M : Type} [AddCommGroup M] [Module F M]

def letterLift (q : D →+ M) (h1 : ∀ (a : LL) x, q (a • x) = algebraMap LL F a • q x)
    (h2 : ∀ c x, q (m c x) = τ c • q x) : Letter m F τ →ₗ[F] M :=
  letI : Module LL M := Module.compHom M (algebraMap LL F)
  haveI : IsScalarTower LL F M := ⟨fun a b x => by
    show (a • b) • x = algebraMap LL F a • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let q' : D →ₗ[LL] M := { toFun := q, map_add' := map_add q, map_smul' := h1 }
  Submodule.liftQ (letterKer m F τ) (q'.liftBaseChange F) (iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul z x =>
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.baseChange_tmul,
        LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearMap.liftBaseChange_tmul]
      show z • q (m c x) - τ c • z • q x = 0
      rw [h2, smul_comm, sub_self]
    | add y z hy hz => rw [map_add]; exact add_mem hy hz)

@[simp] theorem letterLift_mk (q : D →+ M) (h1 : ∀ (a : LL) x, q (a • x) = algebraMap LL F a • q x)
    (h2 : ∀ c x, q (m c x) = τ c • q x) (x : D) :
    letterLift m F τ q h1 h2 (letterMk m F τ x) = q x := by
  show (1 : F) • q x = q x
  rw [one_smul]

end Letter

theorem zpow_semiconj {R R' A B : Type} [Field R] [Field R'] [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R' B] (u : (End R A)ˣ) (u' : (End R' B)ˣ) (d : A →+ B)
    (h : ∀ x, d ((u : End R A) x) = (u' : End R' B) (d x)) (n : ℤ) (x : A) :
    d (((u ^ n : (End R A)ˣ) : End R A) x) = ((u' ^ n : (End R' B)ˣ) : End R' B) (d x) := by
  have hinv : ∀ y, d (((u⁻¹ : (End R A)ˣ) : End R A) y) = ((u'⁻¹ : (End R' B)ˣ) : End R' B) (d y) := by
    intro y
    have e1 : (u : End R A) (((u⁻¹ : (End R A)ˣ) : End R A) y) = y := LinearMap.congr_fun (Units.mul_inv u) y
    have e2 := h (((u⁻¹ : (End R A)ˣ) : End R A) y)
    rw [e1] at e2
    rw [e2, ← End.mul_apply, Units.inv_mul, End.one_apply]
  induction n using Int.induction_on generalizing x with
  | zero => rfl
  | succ n ih => rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, h]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, hinv]

section St

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  (f : V →ₗ[ℚ_[l]] V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ' : Representation ↥L'.1 ↥(GK K) V')

def stMap : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P := f.rTensor (Bst P)

@[simp] theorem stMap_tmul (v : V) (b : Bst P) : stMap P f (v ⊗ₜ b) = f v ⊗ₜ b := rfl

theorem stMap_onB (T : End ℚ_[l] (Bst P)) (x : V ⊗[ℚ_[l]] Bst P) :
    stMap P f (onB P ↥L.1 V T x) = onB P ↥L'.1 V' T (stMap P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem stMap_smul {a : ↥L.1} {a' : ↥L'.1} (h : ∀ x, f (a • x) = a' • f x) (x : V ⊗[ℚ_[l]] Bst P) :
    stMap P f (a • x) = a' • stMap P f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [smul_tmul', stMap_tmul, h, stMap_tmul, smul_tmul']
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

variable {f ρ ρ'}

theorem stMap_stRep (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) :
    stMap P f (stRep P ρ g x) = stRep P ρ' g (stMap P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [he]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem stMap_mem_Dpst (he : ∀ g x, f (ρ g x) = ρ' g (f x)) {x : V ⊗[ℚ_[l]] Bst P} (hx : x ∈ Dpst P ρ) :
    stMap P f x ∈ Dpst P ρ' := by
  obtain ⟨K', hx⟩ := (mem_Dpst P ρ).mp hx
  exact (mem_Dpst P ρ').mpr ⟨K', fun g hg => by rw [← stMap_stRep P he, hx g hg]⟩

def dMap (he : ∀ g x, f (ρ g x) = ρ' g (f x)) : ↥(Dpst P ρ) →+ ↥(Dpst P ρ') where
  toFun x := ⟨stMap P f x, stMap_mem_Dpst P he x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

@[simp] theorem coe_dMap (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (x : ↥(Dpst P ρ)) :
    (dMap P he x : V' ⊗[ℚ_[l]] Bst P) = stMap P f x := rfl

variable (he : ∀ g x, f (ρ g x) = ρ' g (f x))

include he

theorem dMap_phiD (x : ↥(Dpst P ρ)) : dMap P he (phiD P ρ x) = phiD P ρ' (dMap P he x) :=
  Subtype.ext (stMap_onB P f _ x.1)

theorem dMap_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) :
    dMap P he (mulD P ρ c x) = mulD P ρ' c (dMap P he x) :=
  Subtype.ext (stMap_onB P f _ x.1)

theorem dMap_actD (g : ↥(GK K)) (x : ↥(Dpst P ρ)) :
    dMap P he (actD P ρ g x) = actD P ρ' g (dMap P he x) :=
  Subtype.ext (stMap_stRep P he g x.1)

theorem dMap_phiD_pow (n : ℕ) (x : ↥(Dpst P ρ)) :
    dMap P he ((phiD P ρ ^ n) x) = (phiD P ρ' ^ n) (dMap P he x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, ih, dMap_phiD]

theorem dMap_phiU_zpow [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]
    (n : ℤ) (x : ↥(Dpst P ρ)) :
    dMap P he (((phiU P ρ ^ n : (End ↥L.1 ↥(Dpst P ρ))ˣ) : End ↥L.1 ↥(Dpst P ρ)) x) =
      ((phiU P ρ' ^ n : (End ↥L'.1 ↥(Dpst P ρ'))ˣ) : End ↥L'.1 ↥(Dpst P ρ')) (dMap P he x) :=
  zpow_semiconj (phiU P ρ) (phiU P ρ') (dMap P he) (dMap_phiD P he) n x

end St

section Fun

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {f : V →ₗ[ℚ_[l]] V'} {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}

structure IsMor (hL : L.1 ≤ L'.1) (f : V →ₗ[ℚ_[l]] V') (ρ : Representation ↥L.1 ↥(GK K) V)
    (ρ' : Representation ↥L'.1 ↥(GK K) V') : Prop where
  smul : ∀ (a : ↥L.1) x, f (a • x) = IntermediateField.inclusion hL a • f x
  equiv : ∀ g x, f (ρ g x) = ρ' g (f x)

variable {hL : L.1 ≤ L'.1} (hm : IsMor hL f ρ ρ')

def wdMkHom (ρ' : Representation ↥L'.1 ↥(GK K) V') : ↥(Dpst P ρ') →+ WDSpace P ι ρ' :=
  AddMonoidHom.mk' (wdMk P ι ρ') (wdMk_add P ι ρ')

def wdFun : WDSpace P ι ρ →ₗ[ℂ] WDSpace P ι ρ' :=
  letI := algC ι L
  letterLift (mulD P ρ) ℂ (urC ι) ((wdMkHom P ι ρ').comp (dMap P hm.equiv))
    (fun a x => by
      show wdMk P ι ρ' (dMap P hm.equiv (a • x)) = _
      have e : dMap P hm.equiv (a • x) = IntermediateField.inclusion hL a • dMap P hm.equiv x :=
        Subtype.ext (stMap_smul P f (hm.smul a) x.1)
      rw [e, wdMk_smul]
      rfl)
    (fun c x => by
      show wdMk P ι ρ' (dMap P hm.equiv (mulD P ρ c x)) = _
      rw [dMap_mulD, wdMk_mul]
      rfl)

theorem wdFun_mk (x : ↥(Dpst P ρ)) :
    wdFun P ι hm (wdMk P ι ρ x) = wdMk P ι ρ' (dMap P hm.equiv x) :=
  letI := algC ι L
  letterLift_mk _ _ _ _ _ _ x

theorem exists_wdFun_ne_zero (hinj : Function.Injective f) [Nontrivial (WDSpace P ι ρ)] :
    ∃ u, wdFun P ι hm u ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, wdMk P ι ρ x ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h1 : (⊤ : Submodule ℂ (WDSpace P ι ρ)) ≤ ⊥ := by
      rw [← span_wdMk P ι ρ, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hall x
    exact top_ne_bot (le_bot_iff.mp h1)
  have hx0 : dMap P hm.equiv x ≠ 0 := by
    intro h0
    have h1 : stMap P f x.1 = 0 := congrArg Subtype.val h0
    have h2 : Function.Injective (stMap P f) :=
      Module.Flat.rTensor_preserves_injective_linearMap f hinj
    have h3 : x = 0 := Subtype.ext (h2 (h1.trans (map_zero _).symm))
    exact hx (by rw [h3, wdMk_zero])
  by_contra hall
  push_neg at hall
  exact hx0 (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι K L' V' ρ' _ fun n => by
    rw [← dMap_phiD_pow, ← wdFun_mk P ι hm]
    exact hall _)

section Decomp

variable {n : ℕ} {e : Fin n → ↥L'.1} {A : Fin n → V' →ₗ[ℚ_[l]] V}

theorem sum_stMap (hs : ∀ y, ∑ i, e i • f (A i y) = y) (x : V' ⊗[ℚ_[l]] Bst P) :
    ∑ i, e i • stMap P f (stMap P (A i) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    conv_rhs => rw [← hs v]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun i _ => by rw [stMap_tmul, stMap_tmul, smul_tmul']
  | add x y hx hy =>
    simp only [map_add, smul_add, Finset.sum_add_distrib, hx, hy]

variable (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (hA : ∀ i g y, A i (ρ' g y) = ρ g (A i y))
  (hs : ∀ y, ∑ i, e i • f (A i y) = y)

include hs in
theorem sum_dMap (x : ↥(Dpst P ρ')) : ∑ i, e i • dMap P he (dMap P (hA i) x) = x :=
  Subtype.ext (by
    rw [AddSubmonoidClass.coe_finset_sum]
    exact sum_stMap P hs x.1)

include he hA hs in

theorem finite_of_decomp [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] :
    FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ') := by
  let T : (Fin n → DpstUr P ρ) →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ' :=
    { toFun := fun t => toUr P ρ' (∑ i, e i • dMap P he ((toUr P ρ).symm (t i)))
      map_add' := fun s t => by
        simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
      map_smul' := fun c t => by
        show toUr P ρ' (∑ i, e i • dMap P he (mulD P ρ c ((toUr P ρ).symm (t i)))) =
          toUr P ρ' (mulD P ρ' c (∑ i, e i • dMap P he ((toUr P ρ).symm (t i))))
        congr 1
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [dMap_mulD, map_smul] }
  have hT : Function.Surjective T := fun y => by
    refine ⟨fun i => toUr P ρ (dMap P (hA i) ((toUr P ρ').symm y)), ?_⟩
    show toUr P ρ' _ = y
    simp only [AddEquiv.symm_apply_apply]
    rw [sum_dMap P he hA hs, AddEquiv.apply_symm_apply]
  exact Module.Finite.of_surjective T hT

include hA hs in

theorem wdFun_surjective : Function.Surjective (wdFun P ι hm) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_wdMk P ι ρ', Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have e1 : wdMk P ι ρ' x = ∑ i, ι (e i : Om l) • wdFun P ι hm (wdMk P ι ρ (dMap P (hA i) x)) :=
    calc wdMk P ι ρ' x = wdMkHom P ι ρ' (∑ i, e i • dMap P hm.equiv (dMap P (hA i) x)) := by
          rw [sum_dMap P hm.equiv hA hs]; rfl
      _ = ∑ i, wdMkHom P ι ρ' (e i • dMap P hm.equiv (dMap P (hA i) x)) := map_sum _ _ _
      _ = _ := Finset.sum_congr rfl fun i _ => by
          show wdMk P ι ρ' _ = _
          rw [wdMk_smul, wdFun_mk]
  rw [SetLike.mem_coe, e1]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ⟨_, rfl⟩

end Decomp

end Fun

theorem roots_le_of_line {W₁ W₂ W : Type} [AddCommGroup W₁] [Module ℂ W₁] [FiniteDimensional ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] [FiniteDimensional ℂ W₂] [AddCommGroup W] [Module ℂ W]
    (h1 : finrank ℂ W₁ = 1) (T₁ : End ℂ W₁) (T₂ : End ℂ W₂) (T : End ℂ W) (F₁ : W₁ →ₗ[ℂ] W) (F₂ : W₂ →ₗ[ℂ] W)
    (hF₁ : ∃ u, F₁ u ≠ 0) (hF₂ : Function.Surjective F₂) (h₁ : ∀ y, F₁ (T₁ y) = T (F₁ y))
    (h₂ : ∀ y, F₂ (T₂ y) = T (F₂ y)) : T₁.charpoly.roots ≤ T₂.charpoly.roots := by
  have hd : T₁.charpoly.natDegree = 1 := by rw [LinearMap.charpoly_natDegree, h1]
  have hp := (LinearMap.charpoly_monic T₁).eq_X_add_C hd
  set a := T₁.charpoly.coeff 0 with ha
  have hT₁ : ∀ y, T₁ y = (-a) • y := fun y => by
    have h0 := LinearMap.congr_fun (LinearMap.aeval_self_charpoly T₁) y
    rw [hp] at h0
    simp only [map_add, aeval_X, aeval_C, LinearMap.add_apply, Module.algebraMap_end_apply,
      LinearMap.zero_apply] at h0
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h0
  obtain ⟨u, hu⟩ := hF₁
  obtain ⟨y, hy⟩ := hF₂ (F₁ u)
  have hT : T (F₁ u) = (-a) • F₁ u := by rw [← h₁, hT₁, map_smul]
  have hpow : ∀ n : ℕ, F₂ ((T₂ ^ n) y) = (-a) ^ n • F₁ u := fun n => by
    induction n with
    | zero => simpa using hy
    | succ n ih => rw [pow_succ', End.mul_apply, h₂, ih, map_smul, hT, smul_smul, pow_succ]
  have hq : ∀ q : ℂ[X], F₂ (aeval T₂ q y) = q.eval (-a) • F₁ u := fun q => by
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, eval_add, add_smul]
    | monomial n c =>
      rw [aeval_monomial, End.mul_apply, Module.algebraMap_end_apply, map_smul, hpow, eval_monomial,
        smul_smul]
  have h0 := hq T₂.charpoly
  rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero] at h0
  have hroot : T₂.charpoly.eval (-a) = 0 := (smul_eq_zero.mp h0.symm).resolve_right hu
  have e : T₁.charpoly = X - C (-a) := by rw [hp]; simp
  rw [e, roots_X_sub_C, Multiset.singleton_le, mem_roots (LinearMap.charpoly_monic T₂).ne_zero]
  exact hroot

section Bridge

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {f : V →ₗ[ℚ_[l]] V'} {ρ : Representation ↥L.1 ↥(GK Bw.Kw) V} {ρ' : Representation ↥L'.1 ↥(GK Bw.Kw) V'}

theorem dMap_weilD [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]
    (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (σ : ↥(Weil h)) (x : ↥(Dpst P ρ)) :
    dMap P he (weilD Bw h P ρ σ x) = weilD Bw h P ρ' σ (dMap P he x) := by
  exact (dMap_actD P he (weilToGK Bw h σ) _).trans
    (congrArg (actD P ρ' (weilToGK Bw h σ)) (dMap_phiU_zpow P he _ x))

theorem wdFun_wdRho [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]
    {hL : L.1 ≤ L'.1} (hm : IsMor hL f ρ ρ') (σ : ↥(Weil h)) (y : WDSpace P ι ρ) :
    wdFun P ι hm (wdRho P ι Bw h hj ρ σ y) = wdRho P ι Bw h hj ρ' σ (wdFun P ι hm y) := by
  have e : (wdFun P ι hm) ∘ₗ (wdRho P ι Bw h hj ρ σ) = (wdRho P ι Bw h hj ρ' σ) ∘ₗ (wdFun P ι hm) :=
    LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
      simp only [LinearMap.comp_apply, wdRho_mk, wdFun_mk, dMap_weilD]
  exact LinearMap.congr_fun e y

theorem charPol_wdPst [FiniteDimensional ↥L.1 V] (hV : IsPst P ρ)
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] (σ : ↥(Weil h)) :
    WD.charPol (wdPst P ι Bw h hj ρ) σ = (wdRho P ι Bw h hj ρ σ).charpoly := by
  rw [wdPst_of_isPst ι Bw h hj hV, WD.charPol_mk]
  obtain ⟨u, -, hu, -, hc, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  exact (GlobalTheory.WeilDeligne.isFrobSS_of_unipotent u hu hc hρ).charpoly_eq σ

end Bridge

section Model

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
  {L L' : FinExt l} (hL : L.1 ≤ L'.1) (m : ℕ) (r : ↥Gw →* GL (Fin m) ↥L.1)

def incV : (Fin m → ↥L.1) →ₗ[ℚ_[l]] (Fin m → ↥L'.1) :=
  (IntermediateField.inclusion hL).toLinearMap.compLeft (Fin m)

abbrev upRep : ↥Gw →* GL (Fin m) ↥L'.1 := mapRep (IntermediateField.inclusion hL).toRingHom r

theorem isMor_incV : IsMor hL (incV hL m) (Bw.repE L r) (Bw.repE L' (upRep hL m r)) where
  smul a x := funext fun i => map_mul (IntermediateField.inclusion hL) a (x i)
  equiv g x := funext fun i => by
    exact RingHom.map_mulVec (IntermediateField.inclusion hL).toRingHom _ x i

theorem exists_decomp : ∃ (n : ℕ) (e : Fin n → ↥L'.1) (A : Fin n → (Fin m → ↥L'.1) →ₗ[ℚ_[l]] (Fin m → ↥L.1)),
    (∀ i g y, A i (Bw.repE L' (upRep hL m r) g y) = Bw.repE L r g (A i y)) ∧
    ∀ y, ∑ i, e i • incV hL m (A i y) = y := by
  let _ : Algebra ↥L.1 ↥L'.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L.1 ↥L'.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L'.2
  have : FiniteDimensional ↥L.1 ↥L'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  let b := finBasis ↥L.1 ↥L'.1
  refine ⟨_, b, fun i => ((b.coord i).restrictScalars ℚ_[l]).compLeft (Fin m), ?_, ?_⟩
  · intro i g y
    funext j
    show b.coord i (∑ k : Fin m, _) = ∑ k : Fin m, _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : ∀ (c : ↥L.1) (z : ↥L'.1), (IntermediateField.inclusion hL) c * z = c • z :=
      fun c z => (Algebra.smul_def c z).symm
    show b.coord i ((IntermediateField.inclusion hL) _ * _) = _
    rw [e1, map_smul]
    rfl
  · intro y
    funext j
    have e1 := b.sum_repr (y j)
    rw [Finset.sum_apply]
    conv_rhs => rw [← e1]
    refine Finset.sum_congr rfl fun i _ => ?_
    show b i * (IntermediateField.inclusion hL) (b.repr (y j) i) = b.repr (y j) i • b i
    rw [Algebra.smul_def, mul_comm]
    rfl

end Model

section Line

variable {l : ℕ} [Fact l.Prime]

theorem exists_common (L₁ L₂ : FinExt l) {a : ℕ} (v : Fin a → Om l) :
    ∃ L : FinExt l, L₁.1 ≤ L.1 ∧ L₂.1 ≤ L.1 ∧ ∀ j, v j ∈ L.1 := by
  have := fun j => (adjExt (v j)).2
  refine ⟨supExt (supExt L₁ L₂) ⟨⨆ j, (adjExt (v j)).1, inferInstance⟩, ?_, ?_, fun j => ?_⟩
  · exact le_sup_of_le_left (le_sup_left (a := L₁.1) (b := L₂.1))
  · exact le_sup_of_le_left (le_sup_right (a := L₁.1) (b := L₂.1))
  · exact (le_sup_of_le_right (le_iSup (fun j => (adjExt (v j)).1) j) :
      (adjExt (v j)).1 ≤ (supExt L₁ L₂).1 ⊔ ⨆ j, (adjExt (v j)).1) (mem_adjExt (v j))

variable {L₁ L : FinExt l} (hL : L₁.1 ≤ L.1) {a : ℕ}

def lineV (u : Fin a → ↥L.1) : (Fin 1 → ↥L₁.1) →ₗ[ℚ_[l]] (Fin a → ↥L.1) where
  toFun x := IntermediateField.inclusion hL (x 0) • u
  map_add' x y := by simp only [Pi.add_apply, map_add, add_smul]
  map_smul' c x := by
    show IntermediateField.inclusion hL (c • x 0) • u = c • IntermediateField.inclusion hL (x 0) • u
    rw [show IntermediateField.inclusion hL (c • x 0) = c • IntermediateField.inclusion hL (x 0) from
      (IntermediateField.inclusion hL).toLinearMap.map_smul c (x 0), smul_assoc]

theorem lineV_injective {u : Fin a → ↥L.1} (hu : u ≠ 0) : Function.Injective (lineV hL u) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h0 : x 0 = 0 := by
    have := (smul_eq_zero.mp hx).resolve_right hu
    exact (IntermediateField.inclusion hL).toRingHom.injective (this.trans (map_zero _).symm)
  funext i
  rw [Subsingleton.elim i 0, h0]
  rfl

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem isMor_lineV (r : ↥Gw →* GL (Fin a) ↥L.1) (c : ↥Gw →* GL (Fin 1) ↥L₁.1) (u : Fin a → ↥L.1)
    (hu : ∀ g, (r g : Matrix (Fin a) (Fin a) ↥L.1).mulVec u =
      IntermediateField.inclusion hL ((c g : Matrix (Fin 1) (Fin 1) ↥L₁.1) 0 0) • u) :
    IsMor hL (lineV hL u) (Bw.repE L₁ c) (Bw.repE L r) where
  smul b x := by
    show IntermediateField.inclusion hL (b * x 0) • u = _ • IntermediateField.inclusion hL (x 0) • u
    rw [map_mul, mul_smul]
  equiv g x := by
    show IntermediateField.inclusion hL (((c (Bw.e.symm g) : Matrix (Fin 1) (Fin 1) ↥L₁.1)).mulVec x 0) • u =
      Bw.repE L r g (IntermediateField.inclusion hL (x 0) • u)
    rw [map_smul]
    show _ = IntermediateField.inclusion hL (x 0) • (r (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥L.1).mulVec u
    rw [hu, smul_smul]
    simp [Matrix.mulVec, dotProduct, mul_comm]

end Line

section Models

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
  [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
  {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {a : ℕ}

theorem roots_le_of_decomp {L₁ L₂ L : FinExt l} (hL₁ : L₁.1 ≤ L.1) (hL₂ : L₂.1 ≤ L.1)
    (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1) (c₁ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L₁.1)
    (hp₁ : IsPst P (Bw.repE L₁ c₁))
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L₁ c₁))]
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L₂ r₂))]
    (u : Fin a → ↥L.1) (hu0 : u ≠ 0)
    (hu : ∀ g, ((upRep hL₂ a r₂) g : Matrix (Fin a) (Fin a) ↥L.1).mulVec u =
      IntermediateField.inclusion hL₁ ((c₁ g : Matrix (Fin 1) (Fin 1) ↥L₁.1) 0 0) • u) (σ : ↥(Weil h))
    {n : ℕ} {e : Fin n → ↥L.1} {B : Fin n → (Fin a → ↥L.1) →ₗ[ℚ_[l]] (Fin a → ↥L₂.1)}
    (hB : ∀ i g y, B i (Bw.repE L (upRep hL₂ a r₂) g y) = Bw.repE L₂ r₂ g (B i y))
    (hs : ∀ y, ∑ i, e i • incV hL₂ a (B i y) = y) :
    (wdRho P ι Bw h hj (Bw.repE L₁ c₁) σ).charpoly.roots ≤
      (wdRho P ι Bw h hj (Bw.repE L₂ r₂) σ).charpoly.roots := by
  have hm := isMor_incV Bw hL₂ a r₂
  have fL : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L (upRep hL₂ a r₂))) :=
    finite_of_decomp P hm.equiv hB hs
  have hm' := isMor_lineV hL₁ Bw (upRep hL₂ a r₂) c₁ u hu
  have h1 : finrank ℂ (WDSpace P ι (Bw.repE L₁ c₁)) = 1 := by
    rw [GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L₁ _ _ hp₁]
    simp
  have : Nontrivial (WDSpace P ι (Bw.repE L₁ c₁)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  have a1 := exists_wdFun_ne_zero P ι hm' (lineV_injective hL₁ hu0)
  have a2 := wdFun_surjective P ι hm hB hs
  have a3 := wdFun_wdRho P ι Bw h hj hm' σ
  have a4 := wdFun_wdRho P ι Bw h hj hm σ
  exact roots_le_of_line (W₁ := WDSpace P ι (Bw.repE L₁ c₁)) (W₂ := WDSpace P ι (Bw.repE L₂ r₂))
    (W := WDSpace P ι (Bw.repE L (upRep hL₂ a r₂))) h1 _ _ _ _ _ a1 a2 a3 a4

end Models

section Vec

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω Gw O} {a : ℕ}

theorem stable_of_models {r : ↥Gw →* GL (Fin a) (Om l)} {c : ↥Gw →* GL (Fin 1) (Om l)}
    {L₁ L₂ L : FinExt l} (hL₁ : L₁.1 ≤ L.1) (hL₂ : L₂.1 ≤ L.1) {r₂ : ↥Gw →* GL (Fin a) ↥L₂.1}
    {c₁ : ↥Gw →* GL (Fin 1) ↥L₁.1} (hm₂ : IsModel Bw r L₂ r₂) (hm₁ : IsModel Bw c L₁ c₁)
    {v : Fin a → Om l} (hvL : ∀ j, v j ∈ L.1)
    (hvec : ∀ g, (r g : Matrix (Fin a) (Fin a) (Om l)).mulVec v = (c g : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 • v)
    (g : ↥Gw) : ((upRep hL₂ a r₂) g : Matrix (Fin a) (Fin a) ↥L.1).mulVec (fun j => ⟨v j, hvL j⟩) =
      IntermediateField.inclusion hL₁ ((c₁ g : Matrix (Fin 1) (Fin 1) ↥L₁.1) 0 0) •
        (fun j => ⟨v j, hvL j⟩ : Fin a → ↥L.1) := by
  funext i
  have eR : (((upRep hL₂ a r₂) g : Matrix (Fin a) (Fin a) ↥L.1)).map (algebraMap ↥L.1 (Om l)) =
      (r g : Matrix (Fin a) (Fin a) (Om l)) := by
    rw [← hm₂.2]; rfl
  have eC : (c g : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 =
      (((c₁ g : Matrix (Fin 1) (Fin 1) ↥L₁.1) 0 0 : ↥L₁.1) : Om l) := by
    rw [← hm₁.2]; rfl
  have h2 := RingHom.map_mulVec (algebraMap ↥L.1 (Om l))
    ((upRep hL₂ a r₂) g : Matrix (Fin a) (Fin a) ↥L.1) (fun j => ⟨v j, hvL j⟩) i
  rw [eR] at h2
  refine Subtype.ext (h2.trans ?_)
  have h3 : (algebraMap ↥L.1 (Om l)) ∘ (fun j => (⟨v j, hvL j⟩ : ↥L.1)) = v := rfl
  rw [h3, hvec g, eC]
  rfl

end Vec

theorem roots_charPol_le : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (c : ↥(Dec (F := E) A) →* GL (Fin 1) (Om l)),
    IsPstAt P Bw r → IsPstAt P Bw c → ∀ v : Fin a → Om l, v ≠ 0 →
    (∀ g, (r g : Matrix (Fin a) (Fin a) (Om l)).mulVec v = (c g : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 • v) →
    ∀ σ : ↥(Weil h), (WD.charPol (wdAt P ι Bw h hj c) σ).roots ≤ (WD.charPol (wdAt P ι Bw h hj r) σ).roots := by
  intro l _ P ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj a r c hr hc v hv hvec σ
  obtain ⟨L₂, r₂, hm₂, hp₂, e₂⟩ := wdAt_of_isPstAt ι Bw h hj hr
  obtain ⟨L₁, c₁, hm₁, hp₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj hc
  obtain ⟨L, hL₁, hL₂, hvL⟩ := exists_common L₁ L₂ v
  have f₁ := hp₁.finite
  have f₂ := hp₂.finite
  have t₁ : WD.charPol (wdAt P ι Bw h hj c) σ = (wdRho P ι Bw h hj (Bw.repE L₁ c₁) σ).charpoly :=
    (congrArg (fun x => WD.charPol x σ) e₁).trans (charPol_wdPst P ι Bw h hj hp₁ σ)
  have t₂ : WD.charPol (wdAt P ι Bw h hj r) σ = (wdRho P ι Bw h hj (Bw.repE L₂ r₂) σ).charpoly :=
    (congrArg (fun x => WD.charPol x σ) e₂).trans (charPol_wdPst P ι Bw h hj hp₂ σ)
  have key : (wdRho P ι Bw h hj (Bw.repE L₁ c₁) σ).charpoly.roots ≤
      (wdRho P ι Bw h hj (Bw.repE L₂ r₂) σ).charpoly.roots :=
    Exists.elim (exists_decomp Bw hL₂ a r₂) fun n d => Exists.elim d fun e d => Exists.elim d fun B d =>
      roots_le_of_decomp P ι Bw h hj hL₁ hL₂ r₂ c₁ hp₁ (fun j => ⟨v j, hvL j⟩)
        (fun h0 => hv (funext fun j => congrArg Subtype.val (congrFun h0 j)))
        (stable_of_models hL₁ hL₂ hm₂ hm₁ hvL hvec) σ d.1 d.2
  exact (congrArg Polynomial.roots t₁).le.trans (key.trans (congrArg Polynomial.roots t₂).ge)

end GlobalTheory.PstLine
