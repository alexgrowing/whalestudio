import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.SpanEqTopOfForallMaximal

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.SqZero

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

section Maps

variable {S S' A A' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']

def dualTo (f : S →ₐ[R] A) (t : A) (ht : t * t = 0) : DualNumber S →ₐ[R] A :=
  DualNumber.lift ⟨(f, t), ht, fun _ => Commute.all _ _⟩

theorem dualTo_apply (f : S →ₐ[R] A) (t : A) (ht : t * t = 0) (a : DualNumber S) :
    dualTo f t ht a = f a.fst + f a.snd * t := rfl

def epsTo (R : Type) [CommRing R] {A : Type} [CommRing A] [Algebra R A] (t : A) (ht : t * t = 0) :
    DualNumber R →ₐ[R] A := dualTo (Algebra.ofId R A) t ht

@[simp] theorem epsTo_eps (t : A) (ht : t * t = 0) : epsTo R t ht DualNumber.eps = t := by
  simp [epsTo, dualTo_apply]

theorem comp_epsTo (φ : A →ₐ[R] A') (t : A) (ht : t * t = 0) :
    φ.comp (epsTo R t ht) = epsTo R (φ t) (by rw [← map_mul, ht, map_zero]) :=
  DualNumber.algHom_ext (by simp)

theorem epsTo_zero : epsTo R (0 : A) (mul_zero _) = (Algebra.ofId R A).comp (fstD R) :=
  DualNumber.algHom_ext (by simp)

theorem epsTo_comp_scaleD (t : A) (ht : t * t = 0) (a : R) :
    (epsTo R t ht).comp (scaleD a) =
      epsTo R (a • t) (by rw [smul_mul_smul_comm, ht, smul_zero]) :=
  DualNumber.algHom_ext (by
    rw [epsTo_eps]
    change epsTo R t ht (TrivSqZeroExt.map _ (inr 1)) = _
    simp [epsTo, dualTo_apply, Algebra.smul_def])

theorem scaleD_eq (a : R) :
    scaleD a = epsTo R (inr a : DualNumber R) (TrivSqZeroExt.inr_mul_inr _ _ _) :=
  DualNumber.algHom_ext (by
    rw [epsTo_eps]
    change TrivSqZeroExt.map _ (inr 1) = _
    rw [TrivSqZeroExt.map_inr, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one])

def vecTo {n : ℕ} (α : S →ₐ[R] A) (c : Fin n → A) (hc : ∀ i j, c i * c j = 0) :
    TrivSqZeroExt S (Fin n → S) →ₐ[R] A :=
  TrivSqZeroExt.lift α
    { toFun := fun m => ∑ i, α (m i) * c i
      map_add' := fun m m' => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r m => by simp [Finset.smul_sum] }
    (fun x y => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul_sum]
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        rw [mul_mul_mul_comm, hc, mul_zero])
    (fun r x => by simp [Finset.mul_sum, mul_assoc])
    (fun r x => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, op_smul_eq_mul, map_mul,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring)

theorem vecTo_apply {n : ℕ} (α : S →ₐ[R] A) (c : Fin n → A) (hc : ∀ i j, c i * c j = 0)
    (x : TrivSqZeroExt S (Fin n → S)) : vecTo α c hc x = α x.fst + ∑ i, α (x.snd i) * c i := rfl

theorem vecTo_single {n : ℕ} (α : S →ₐ[R] A) (c : Fin n → A) (hc : ∀ i j, c i * c j = 0)
    (i : Fin n) : vecTo α c hc (inr (Pi.single i 1)) = c i := by
  simp [vecTo_apply, Pi.single_apply, apply_ite]

theorem mul_eq_zero_of_sq {J : Ideal A} (hJ : J ^ 2 = ⊥) {a b : A} (ha : a ∈ J) (hb : b ∈ J) :
    a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rwa [← pow_two, hJ, Ideal.mem_bot] at this

theorem map_sq {J : Ideal A} (hJ : J ^ 2 = ⊥) (φ : A →ₐ[R] A') : (J.map φ) ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, hJ, Ideal.map_bot]

theorem nil_of_sq {J : Ideal A} (hJ : J ^ 2 = ⊥) (a : A) (ha : Ideal.Quotient.mkₐ R J a = 0) :
    IsNilpotent a :=
  ⟨2, by
    have := Ideal.Quotient.eq_zero_iff_mem.1 ha
    rw [pow_two, mul_eq_zero_of_sq hJ this this]⟩

theorem ker_fst_sq (M : Type) [AddCommGroup M] [Module S M] [Module Sᵐᵒᵖ M] [IsCentralScalar S M]
    [Module R M] [IsScalarTower R S M] [IsScalarTower R Sᵐᵒᵖ M] :
    RingHom.ker (TrivSqZeroExt.fstHom R S M) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  have hx : x.fst = 0 := hx
  have hy : y.fst = 0 := hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]

end Maps

section Group

variable (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {A A' A₀ : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  [CommRing A₀] [Algebra R A₀]

def pointsMap (φ : A →ₐ[R] A') : (sp A ⟶ G) →* (sp A' ⟶ G) where
  toFun y := spMap φ ≫ y
  map_one' := MonObj.comp_one _
  map_mul' := MonObj.comp_mul _

@[simp] theorem ptsMap_apply (φ : A →ₐ[R] A') (y : sp A ⟶ G) : pointsMap G φ y = spMap φ ≫ y := rfl

def redKer (J : Ideal A) : Subgroup (sp (R₀ := R) A ⟶ G) := (pointsMap G (Ideal.Quotient.mkₐ R J)).ker

variable {G}

theorem mem_redKer {J : Ideal A} {y : sp A ⟶ G} :
    y ∈ redKer G J ↔ spMap (Ideal.Quotient.mkₐ R J) ≫ y = 1 := Iff.rfl

theorem comp_eq_one_of_mem_redKer {J : Ideal A} {y : sp A ⟶ G} (hy : y ∈ redKer G J)
    (q : A →ₐ[R] A₀) (hq : ∀ a ∈ J, q a = 0) : spMap q ≫ y = 1 := by
  have : q = (Ideal.Quotient.liftₐ J q hq).comp (Ideal.Quotient.mkₐ R J) := by ext; rfl
  rw [this, ← spMap_comp, Category.assoc, mem_redKer.1 hy, comp_one']

theorem comp_mem_redKer {J : Ideal A} {J' : Ideal A'} {y : sp A ⟶ G} (hy : y ∈ redKer G J)
    (φ : A →ₐ[R] A') (hφ : ∀ a ∈ J, φ a ∈ J') : spMap φ ≫ y ∈ redKer G J' := by
  rw [mem_redKer, ← Category.assoc, spMap_comp]
  exact comp_eq_one_of_mem_redKer hy _ fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hφ a ha)

theorem mem_redKer_of_section (q : A →ₐ[R] A₀) (s : A₀ →ₐ[R] A) (hs : ∀ a, q (s a) = a)
    {y : sp A ⟶ G} (hy : spMap q ≫ y = 1) : y ∈ redKer G (RingHom.ker q) := by
  have : Ideal.Quotient.mkₐ R (RingHom.ker q) =
      ((Ideal.Quotient.mkₐ R (RingHom.ker q)).comp s).comp q := by
    ext a
    exact Ideal.Quotient.eq.2 (by simp [RingHom.mem_ker, hs])
  rw [mem_redKer, this, ← spMap_comp, Category.assoc, hy, comp_one']

variable (G A) in

def UnitInChart : Prop :=
  ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (j : sp B ⟶ G) (u : B →ₐ[R] A),
    IsOpenImmersion j.left ∧ spMap u ≫ j = 1

theorem UnitInChart.map (h : UnitInChart G A) (φ : A →ₐ[R] A') : UnitInChart G A' := by
  obtain ⟨B, _, _, j, u, hj, hu⟩ := h
  exact ⟨B, _, _, j, φ.comp u, hj, by rw [← spMap_comp, Category.assoc, hu, comp_one']⟩

variable (G A) in
theorem span_unitInChart :
    Ideal.span {f : A | UnitInChart G (Localization.Away f)} = ⊤ := by
  refine span_eq_top_of_forall_maximal fun m hm => ?_
  obtain ⟨f, hf, B, _, _, j, hj, h⟩ := exists_local_chart (1 : sp A ⟶ G) m hm.isPrime
  obtain ⟨u, hu⟩ := h _ (awayHom R f) (isAway_awayHom f).unit
  exact ⟨f, ⟨B, _, _, j, u, hj, by rw [← hu, comp_one']⟩, hf⟩

variable (G A) in
theorem exists_fin_unitInChart : ∃ (κ : Type) (_ : Finite κ) (s : κ → A),
    Ideal.span (Set.range s) = ⊤ ∧ ∀ k, UnitInChart G (Localization.Away (s k)) := by
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite _).1 (span_unitInChart G A)
  exact ⟨s, inferInstance, Subtype.val, by rw [Subtype.range_coe_subtype]; exact hspan,
    fun k => hs k.2⟩

theorem exists_chart_of_mem_redKer {B : Type} [CommRing B] [Algebra R B] (j : sp B ⟶ G)
    [IsOpenImmersion j.left] (u : B →ₐ[R] A) (hu : spMap u ≫ j = 1) {J : Ideal A} (hJ : J ^ 2 = ⊥)
    {y : sp A ⟶ G} (hy : y ∈ redKer G J) :
    ∃ φ : B →ₐ[R] A, y = spMap φ ≫ j ∧ ∀ b, φ b - u b ∈ J := by
  obtain ⟨φ, h1, h2⟩ := exists_chart_pt_of_nil j (Ideal.Quotient.mkₐ R J)
    (Ideal.Quotient.mkₐ_surjective R J) (nil_of_sq hJ) y ((Ideal.Quotient.mkₐ R J).comp u)
    (by rw [mem_redKer.1 hy, ← spMap_comp, Category.assoc, hu, comp_one'])
  exact ⟨φ, h1, fun b => Ideal.Quotient.eq.1 (AlgHom.congr_fun h2 b)⟩

theorem redKer_ext {J : Ideal A} (hJ : J ^ 2 = ⊥) {y y' : sp A ⟶ G} (hy : y ∈ redKer G J)
    (hy' : y' ∈ redKer G J) (q₁ : A →ₐ[R] A') (q₂ : A →ₐ[R] A₀)
    (hq : ∀ a, q₁ a = 0 → q₂ a = 0 → a = 0) (h₁ : spMap q₁ ≫ y = spMap q₁ ≫ y')
    (h₂ : spMap q₂ ≫ y = spMap q₂ ≫ y') : y = y' := by
  obtain ⟨κ, _, s, hs, hsm⟩ := exists_fin_unitInChart G A
  refine away_ext hs (fun k => awayHom R (s k)) (fun k => isAway_awayHom _) fun k => ?_
  obtain ⟨B, _, _, j, u, hj, hu⟩ := hsm k
  have hρ := isAway_awayHom (R := R) (s k)
  obtain ⟨φ, e, -⟩ := exists_chart_of_mem_redKer j u hu (map_sq hJ (awayHom R (s k)))
    (comp_mem_redKer hy (awayHom R (s k)) fun a ha => Ideal.mem_map_of_mem _ ha)
  obtain ⟨φ', e', -⟩ := exists_chart_of_mem_redKer j u hu (map_sq hJ (awayHom R (s k)))
    (comp_mem_redKer hy' (awayHom R (s k)) fun a ha => Ideal.mem_map_of_mem _ ha)
  rw [e, e']
  congr 2
  ext b
  obtain ⟨N, a, ha⟩ := hρ.surj (φ b - φ' b)
  have key : ∀ {T : Type} [CommRing T] [Algebra R T] (q : A →ₐ[R] T),
      spMap q ≫ y = spMap q ≫ y' → ∃ M : ℕ, q (s k ^ M * a) = 0 := by
    intro T _ _ q h
    have hρ' := isAway_awayHom (R := R) (q (s k))
    obtain ⟨ψ, hψ⟩ := hρ.lift ((awayHom R (q (s k))).comp q) hρ'.unit
    have : spMap (ψ.comp φ) ≫ j = spMap (ψ.comp φ') ≫ j := by
      rw [← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, ← e, ← e',
        ← Category.assoc, ← Category.assoc, spMap_comp, hψ, ← spMap_comp, Category.assoc,
        Category.assoc, h]
    have h3 : ψ (φ b) = ψ (φ' b) := AlgHom.congr_fun (chart_inj j this) b
    obtain ⟨M, hM⟩ := hρ'.ker (a := q a) (by
      rw [← AlgHom.comp_apply, ← hψ, AlgHom.comp_apply, ← ha, map_mul, map_sub, h3, sub_self,
        zero_mul])
    exact ⟨M, by rw [map_mul, map_pow, hM]⟩
  obtain ⟨M₁, e₁⟩ := key q₁ h₁
  obtain ⟨M₂, e₂⟩ := key q₂ h₂
  have h0 : s k ^ M₁ * s k ^ M₂ * a = 0 := hq _
    (by rw [mul_right_comm, map_mul, e₁, zero_mul]) (by rw [mul_assoc, map_mul, e₂, mul_zero])
  have h1 := congrArg (awayHom R (s k)) h0
  rw [map_mul, map_mul, map_pow, map_pow, map_zero, ← ha,
    ((hρ.unit.pow M₁).mul (hρ.unit.pow M₂)).mul_right_eq_zero,
    (hρ.unit.pow N).mul_left_eq_zero] at h1
  exact sub_eq_zero.1 h1

theorem epsTo_zero_comp {w : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (t : A) (ht0 : t = 0)
    (ht : t * t = 0) : spMap (epsTo R t ht) ≫ w = 1 := by
  subst ht0
  rw [epsTo_zero, ← spMap_comp, Category.assoc, hw, comp_one']

theorem epsTo_comp_mem_redKer {w : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) {J : Ideal A}
    {t : A} (htJ : t ∈ J) (ht : t * t = 0) : spMap (epsTo R t ht) ≫ w ∈ redKer G J := by
  rw [mem_redKer, ← Category.assoc, spMap_comp, comp_epsTo]
  exact epsTo_zero_comp hw _ (Ideal.Quotient.eq_zero_iff_mem.2 htJ) _

theorem epsTo_add_comp {w : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (t₁ t₂ : A)
    (h₁ : t₁ * t₁ = 0) (h₂ : t₂ * t₂ = 0) (h₁₂ : t₁ * t₂ = 0) (h : (t₁ + t₂) * (t₁ + t₂) = 0) :
    spMap (epsTo R (t₁ + t₂) h) ≫ w =
      (spMap (epsTo R t₁ h₁) ≫ w) * (spMap (epsTo R t₂ h₂) ≫ w) := by
  let E := TrivSqZeroExt R (Fin 2 → R)
  let e : Fin 2 → E := fun i => inr (Pi.single i 1)
  have he : ∀ i j, e i * e j = 0 := fun i j => TrivSqZeroExt.inr_mul_inr _ _ _
  have he' : (e 0 + e 1) * (e 0 + e 1) = 0 := by simp [add_mul, mul_add, he]
  have hk : ∀ i, e i ∈ RingHom.ker (TrivSqZeroExt.fstHom R R (Fin 2 → R)) := fun i => rfl
  have ax : ∀ i : Fin 2, ∀ a b : Fin 2, (Pi.single i DualNumber.eps : Fin 2 → DualNumber R) a *
      (Pi.single i DualNumber.eps : Fin 2 → DualNumber R) b = 0 := by
    intro i a b
    simp only [Pi.single_apply]
    split_ifs <;> simp
  let q : Fin 2 → (E →ₐ[R] DualNumber R) := fun i =>
    vecTo (Algebra.ofId R _) (Pi.single i DualNumber.eps) (ax i)
  have hq : ∀ i a, q i (e a) = (Pi.single i DualNumber.eps : Fin 2 → DualNumber R) a :=
    fun i a => vecTo_single _ _ _ _
  have univ : spMap (epsTo R (e 0 + e 1) he') ≫ w =
      (spMap (epsTo R (e 0) (he 0 0)) ≫ w) * (spMap (epsTo R (e 1) (he 1 1)) ≫ w) := by
    refine redKer_ext (ker_fst_sq (R := R) (S := R) (Fin 2 → R))
      (epsTo_comp_mem_redKer hw (add_mem (hk 0) (hk 1)) _)
      (mul_mem (epsTo_comp_mem_redKer hw (hk 0) _) (epsTo_comp_mem_redKer hw (hk 1) _))
      (q 0) (q 1) ?_ ?_ ?_
    · intro a h0 h1
      have a0 := congrArg TrivSqZeroExt.fst h0
      have a1 := congrArg TrivSqZeroExt.snd h0
      have a2 := congrArg TrivSqZeroExt.snd h1
      simp [q, vecTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl] at a0 a1 a2
      refine TrivSqZeroExt.ext a0 (funext fun i => ?_)
      fin_cases i
      · exact a1
      · exact a2
    · simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, comp_epsTo]
      rw [epsTo_zero_comp hw (q 0 (e 1)) (by simp [hq]), mul_one]
      congr 3
      simp [hq]
    · simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, comp_epsTo]
      rw [epsTo_zero_comp hw (q 1 (e 0)) (by simp [hq]), one_mul]
      congr 3
      simp [hq]
  let ψ : E →ₐ[R] A := vecTo (Algebra.ofId R A) ![t₁, t₂] (fun a b => by
    fin_cases a <;> fin_cases b <;> simp [h₁, h₂, h₁₂, mul_comm t₂ t₁])
  have hψ₀ : ψ (e 0) = t₁ := vecTo_single _ _ _ _
  have hψ₁ : ψ (e 1) = t₂ := vecTo_single _ _ _ _
  have := congrArg (spMap ψ ≫ ·) univ
  simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, comp_epsTo, map_add, hψ₀, hψ₁] at this
  exact this

variable [IsCommMonObj G] {n : ℕ}

def lieExp (v : Fin n → (epsR R ⟶ G)) (c : Fin n → A) (hc : ∀ i, c i * c i = 0) : sp A ⟶ G :=
  ∏ i, spMap (epsTo R (c i) (hc i)) ≫ v i

theorem comp_lieExp (v : Fin n → (epsR R ⟶ G)) (φ : A →ₐ[R] A') (c : Fin n → A)
    (hc : ∀ i, c i * c i = 0) :
    spMap φ ≫ lieExp v c hc =
      lieExp v (fun i => φ (c i)) (fun i => by rw [← map_mul, hc, map_zero]) := by
  rw [lieExp, ← ptsMap_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ptsMap_apply, ← Category.assoc, spMap_comp, comp_epsTo]

theorem lieExp_congr (v : Fin n → (epsR R ⟶ G)) {c c' : Fin n → A} (h : ∀ i, c i = c' i)
    (hc : ∀ i, c i * c i = 0) (hc' : ∀ i, c' i * c' i = 0) : lieExp v c hc = lieExp v c' hc' := by
  obtain rfl : c = c' := funext h
  rfl

variable {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i))

include hv

theorem lieExp_eq_one (c : Fin n → A) (h0 : ∀ i, c i = 0) (hc : ∀ i, c i * c i = 0) :
    lieExp v c hc = 1 :=
  Finset.prod_eq_one fun i _ => epsTo_zero_comp ((isTan_iff _).2 (hv i)) _ (h0 i) _

theorem lieExp_mem_redKer {J : Ideal A} (c : Fin n → A) (hcJ : ∀ i, c i ∈ J)
    (hc : ∀ i, c i * c i = 0) : lieExp v c hc ∈ redKer G J :=
  prod_mem fun i _ => epsTo_comp_mem_redKer ((isTan_iff _).2 (hv i)) (hcJ i) _

theorem lieExp_add (c c' : Fin n → A) (hc : ∀ i, c i * c i = 0) (hc' : ∀ i, c' i * c' i = 0)
    (hcc : ∀ i, c i * c' i = 0) (h : ∀ i, (c i + c' i) * (c i + c' i) = 0) :
    lieExp v (fun i => c i + c' i) h = lieExp v c hc * lieExp v c' hc' := by
  rw [lieExp, lieExp, lieExp, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => epsTo_add_comp ((isTan_iff _).2 (hv i)) _ _ _ _ (hcc i) _

omit hv in
theorem prodPts_eq_lieExp (c : Fin n → R) : prodPts c v =
    lieExp v (fun i => (inr (c i) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  rw [prodPts, List.prod_ofFn, lieExp]
  exact Finset.prod_congr rfl fun i _ => by rw [scaleD_eq]

omit hv in
theorem isLieComb_iff_lieExp (c : Fin n → R) (w : epsR R ⟶ G) : IsLieComb c v w ↔
    w = lieExp v (fun i => (inr (c i) : DualNumber R))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  rw [isLieComb_iff, prodPts_eq_lieExp]

end Group

end GlobalTheory.SqZero
