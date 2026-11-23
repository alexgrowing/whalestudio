import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.RuleDescend

theorem exists_square {R R₁ R' : Type} [CommRing R] [CommRing R₁] [CommRing R'] (σ : R →+* R₁)
    (hσ : σ.FaithfullyFlat) (τ : R →+* R') :
    ∃ (T : Type) (_ : CommRing T) (a : R₁ →+* T) (b : R' →+* T), a.comp σ = b.comp τ ∧ Function.Injective b := by
  letI := σ.toAlgebra
  letI := τ.toAlgebra
  haveI : Module.FaithfullyFlat R R₁ := hσ
  refine ⟨R₁ ⊗[R] R', inferInstance, Algebra.TensorProduct.includeLeftRingHom,
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] R₁ ⊗[R] R').toRingHom,
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, ?_⟩
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := R₁) R'

theorem exists_equaliser {R R₁ : Type} [CommRing R] [CommRing R₁] (σ : R →+* R₁) (hσ : σ.FaithfullyFlat) :
    ∃ (T : Type) (_ : CommRing T) (a b : R₁ →+* T), a.comp σ = b.comp σ ∧ ∀ x, a x = b x → ∃ y, σ y = x := by
  letI := σ.toAlgebra
  haveI : Module.FaithfullyFlat R R₁ := hσ
  refine ⟨R₁ ⊗[R] R₁, inferInstance, Algebra.TensorProduct.includeLeftRingHom,
    (Algebra.TensorProduct.includeRight : R₁ →ₐ[R] R₁ ⊗[R] R₁).toRingHom,
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, fun x hx ↦ ?_⟩
  refine (Algebra.IsEffective.of_faithfullyFlat R R₁ x).1 ?_
  have : x ⊗ₜ[R] (1 : R₁) = (1 : R₁) ⊗ₜ[R] x := hx
  simp [this]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Chart.dualMapR (g.comp f) = (Chart.dualMapR g).comp (Chart.dualMapR f) := by
  refine RingHom.ext fun r ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [Chart.dualMapR]

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
  {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem lieCorr_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    {v : X.Lie} {v' : X'.Lie} {v'' : X''.Lie} (h : Obj.LieCorr σ φ v v') (h' : Obj.LieCorr τ ψ v' v'') :
    Obj.LieCorr (τ.comp σ) (ψ ≫ φ) v v'' := by
  unfold Obj.LieCorr at *
  rw [← Category.assoc, h', Category.assoc, h, dualMapR_comp, spMap_comp, Category.assoc]

theorem existsUnique_lieCorr {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (v : X.Lie) : ∃! v', Obj.LieCorr σ φ v v' := by
  letI := σ.toAlgebra
  obtain ⟨e, he, -⟩ := Obj.exists_lieEquiv (R' := R') h
  exact ⟨_, (he v _).2 rfl, fun w hw ↦ (he v w).1 hw⟩

theorem isPullBy_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h : X'.IsPullBy X (spMap σ) φ) (h' : X''.IsPullBy X' (spMap τ) ψ) :
    X''.IsPullBy X (spMap (τ.comp σ)) (ψ ≫ φ) := by
  rw [spMap_comp]; exact h'.comp h

theorem detCorr_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h : X'.IsPullBy X (spMap σ) φ) (h' : X''.IsPullBy X' (spMap τ) ψ)
    {δ : X.DetOmega} {δ' : X'.DetOmega} {δ'' : X''.DetOmega}
    (hd : Obj.DetCorr σ φ δ δ') (hd' : Obj.DetCorr τ ψ δ' δ'') : Obj.DetCorr (τ.comp σ) (ψ ≫ φ) δ δ'' := by
  intro v v'' hv
  choose v' hv' using fun i ↦ (existsUnique_lieCorr h (v i)).exists
  have : ∀ i, Obj.LieCorr τ ψ (v' i) (v'' i) := fun i ↦ by
    obtain ⟨w, hw⟩ := (existsUnique_lieCorr h' (v' i)).exists
    rwa [(existsUnique_lieCorr (isPullBy_comp h h') (v i)).unique (hv i) (lieCorr_comp (hv' i) hw)]
  rw [hd' v' v'' this, hd v v' hv', RingHom.comp_apply]

theorem isUnit_of_eq_smul {X : Obj F 𝔠 (Sp R)} (δ δ' : X.DetGen) (c : R) (h : δ'.1 = c • δ.1) : IsUnit c := by
  haveI := X.invertible_detOmega
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (δ'.2.ge Submodule.mem_top : δ.1 ∈ Submodule.span R {δ'.1})
  refine IsUnit.of_mul_eq_one_right a (eq_of_smul_eq_smul (α := X.DetOmega) fun m ↦ ?_)
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : m ∈ Submodule.span R {δ.1})
  rw [smul_comm, mul_smul, ← h, ha, one_smul]

variable {N : ℕ} {R₀ : Type} [CommRing R₀] {k : ℕ}

theorem levObj_of_isPullBy {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (hX : levObj 𝔠 N R X) : levObj 𝔠 N R' X' := by
  obtain ⟨hu, ⟨α⟩⟩ := hX
  obtain ⟨α', -⟩ := h.exists_level α
  exact ⟨by simpa using hu.map σ, ⟨α'⟩⟩

def IsVal (r : Rule (levObj 𝔠 N) R₀ k) [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) (x : R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra R₀ R'] (σ : R →ₐ[R₀] R') (X' : Obj F 𝔠 (Sp R')) (h' : levObj 𝔠 N R' X')
    (φ : X'.A.left ⟶ X.A.left) (δ' : X'.DetGen), X'.IsPullBy X (spMap (σ : R →+* R')) φ →
    Obj.DetCorr (σ : R →+* R') φ δ.1 δ'.1 → r.val R' X' h' δ' = σ x

theorem val_eq_of_square (r : Rule (levObj 𝔠 N) R₀ k) {R₁ R₂ T : Type} [CommRing R₁] [CommRing R₂] [CommRing T]
    [Algebra R₀ R] [Algebra R₀ R₁] [Algebra R₀ R₂] (σ : R →ₐ[R₀] R₁) (τ : R →ₐ[R₀] R₂)
    (a : R₁ →+* T) (b : R₂ →+* T) (hab : a.comp (σ : R →+* R₁) = b.comp (τ : R →+* R₂))
    {X : Obj F 𝔠 (Sp R)} {X₁ : Obj F 𝔠 (Sp R₁)} {X₂ : Obj F 𝔠 (Sp R₂)}
    {φ₁ : X₁.A.left ⟶ X.A.left} {φ₂ : X₂.A.left ⟶ X.A.left}
    (h₁ : X₁.IsPullBy X (spMap (σ : R →+* R₁)) φ₁) (h₂ : X₂.IsPullBy X (spMap (τ : R →+* R₂)) φ₂)
    (l₁ : levObj 𝔠 N R₁ X₁) (l₂ : levObj 𝔠 N R₂ X₂) {δ : X.DetGen} {δ₁ : X₁.DetGen} {δ₂ : X₂.DetGen}
    (d₁ : Obj.DetCorr (σ : R →+* R₁) φ₁ δ.1 δ₁.1) (d₂ : Obj.DetCorr (τ : R →+* R₂) φ₂ δ.1 δ₂.1) :
    a (r.val R₁ X₁ l₁ δ₁) = b (r.val R₂ X₂ l₂ δ₂) := by
  letI : Algebra R₀ T := (a.comp (algebraMap R₀ R₁)).toAlgebra
  let a' : R₁ →ₐ[R₀] T := { a with commutes' := fun _ ↦ rfl }
  let b' : R₂ →ₐ[R₀] T := { b with
    commutes' := fun x ↦ by
      have := RingHom.congr_fun hab (algebraMap R₀ R x)
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes] at this
      exact this.symm }
  obtain ⟨Y, ψ₁, k₁⟩ := X₁.exists_isPullBy (spMap a)
  have hY := isPullBy_comp h₁ k₁
  have hY' := hY
  rw [hab, spMap_comp] at hY'
  obtain ⟨ψ₂, k₂, hψ⟩ := hY'.cancel h₂
  obtain ⟨ε₁, e₁⟩ := (k₁.existsUnique_detGen a δ₁).exists
  obtain ⟨ε₂, e₂⟩ := (k₂.existsUnique_detGen b δ₂).exists
  have f₂ := detCorr_comp h₂ k₂ d₂ e₂
  rw [hψ, ← hab] at f₂
  obtain rfl : ε₁ = ε₂ := (hY.existsUnique_detGen _ δ).unique (detCorr_comp h₁ k₁ d₁ e₁) f₂
  have lY := levObj_of_isPullBy k₁ l₁
  exact (r.baseChange R₁ T a' X₁ l₁ Y lY ψ₁ δ₁ ε₁ k₁ e₁).symm.trans (r.baseChange R₂ T b' X₂ l₂ Y lY ψ₂ δ₂ ε₁ k₂ e₂)

variable (𝔠 N) in

def HasLevelCovers : Prop :=
  ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
    ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
      σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N)

theorem exists_cover (hN : HasLevelCovers 𝔠 N) [Algebra R₀ R] (hu : IsUnit (N : R)) (X : Obj F 𝔠 (Sp R)) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R₀ R₁) (σ : R →ₐ[R₀] R₁) (X₁ : Obj F 𝔠 (Sp R₁))
      (φ : X₁.A.left ⟶ X.A.left), (σ : R →+* R₁).FaithfullyFlat ∧ X₁.IsPullBy X (spMap (σ : R →+* R₁)) φ ∧
      levObj 𝔠 N R₁ X₁ := by
  obtain ⟨R₁, _, σ, X₁, φ, hσ, hp, hl⟩ := hN R hu X
  letI : Algebra R₀ R₁ := (σ.comp (algebraMap R₀ R)).toAlgebra
  exact ⟨R₁, inferInstance, inferInstance, { σ with commutes' := fun _ ↦ rfl }, X₁, φ, hσ, hp,
    by simpa using hu.map σ, hl⟩

theorem existsUnique_isVal (hN : HasLevelCovers 𝔠 N) (r : Rule (levObj 𝔠 N) R₀ k) [Algebra R₀ R]
    (hu : IsUnit (N : R)) (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) : ∃! x, IsVal r X δ x := by
  obtain ⟨R₁, _, _, σ, X₁, φ, hσ, hp, hl⟩ := exists_cover (R₀ := R₀) hN hu X
  obtain ⟨δ₁, d₁⟩ := (hp.existsUnique_detGen _ δ).exists
  obtain ⟨T, _, a, b, hab, hT⟩ := exists_equaliser _ hσ
  obtain ⟨x, hx⟩ := hT _ (val_eq_of_square r σ σ a b hab hp hp hl hl d₁ d₁)
  refine ⟨x, fun R' _ _ τ X' h' φ' δ' hp' d' ↦ ?_, fun y hy ↦ hσ.injective ?_⟩
  · obtain ⟨T', _, a', b', hab', hb'⟩ := exists_square _ hσ (τ : R →+* R')
    refine hb' ?_
    rw [← val_eq_of_square r σ τ a' b' hab' hp hp' hl h' d₁ d', ← hx]
    exact RingHom.congr_fun hab' x
  · rw [hx]; exact (hy R₁ σ X₁ hl φ δ₁ hp d₁).symm

theorem IsVal.baseChange {r : Rule (levObj 𝔠 N) R₀ k} [Algebra R₀ R] [Algebra R₀ R'] (σ : R →ₐ[R₀] R')
    {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {φ : X'.A.left ⟶ X.A.left} {δ : X.DetGen} {δ' : X'.DetGen}
    (h : X'.IsPullBy X (spMap (σ : R →+* R')) φ) (d : Obj.DetCorr (σ : R →+* R') φ δ.1 δ'.1) {x : R}
    (hx : IsVal r X δ x) : IsVal r X' δ' (σ x) := fun R'' _ _ τ X'' h'' ψ δ'' hp d' ↦
  hx R'' (τ.comp σ) X'' h'' (ψ ≫ φ) δ'' (isPullBy_comp h hp) (detCorr_comp h hp d d')

theorem IsVal.homog {r : Rule (levObj 𝔠 N) R₀ k} [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)} {δ δ' : X.DetGen} {c : R}
    (hc : δ'.1 = c • δ.1) {x : R} (hx : IsVal r X δ' x) : IsVal r X δ (c ^ k * x) := by
  intro R' _ _ σ X' h' φ ε hp d
  have hu : IsUnit (σ c) := (isUnit_of_eq_smul δ δ' c hc).map σ
  let ε' : X'.DetGen := ⟨σ c • ε.1, (Submodule.span_singleton_smul_eq hu _).trans ε.2⟩
  have d' : Obj.DetCorr (σ : R →+* R') φ δ'.1 ε'.1 := fun v v' hv ↦ by
    change σ c • ε.1 v' = _
    rw [d v v' hv, hc]
    simp
  rw [← r.homog R' X' h' ε ε' (σ c) rfl, hx R' σ X' h' φ ε' hp d', map_mul, map_pow]

def descend (hN : HasLevelCovers 𝔠 N) (r : Rule (levObj 𝔠 N) R₀ k) : Rule (unitObj 𝔠 N) R₀ k where
  val _ _ _ X h δ := (existsUnique_isVal hN r h X δ).exists.choose
  homog _ _ _ X h δ δ' _ hc := (existsUnique_isVal hN r h X δ).unique
    ((existsUnique_isVal hN r h X δ').exists.choose_spec.homog hc) (existsUnique_isVal hN r h X δ).exists.choose_spec
  baseChange _ _ _ _ _ _ σ X h X' h' _ δ δ' hp d := (existsUnique_isVal hN r h' X' δ').unique
    (existsUnique_isVal hN r h' X' δ').exists.choose_spec
    ((existsUnique_isVal hN r h X δ).exists.choose_spec.baseChange σ hp d)

theorem descend_val_eq (hN : HasLevelCovers 𝔠 N) (r : Rule (levObj 𝔠 N) R₀ k) [Algebra R₀ R]
    (X : Obj F 𝔠 (Sp R)) (h : IsUnit (N : R)) (δ : X.DetGen) {x : R} (hx : IsVal r X δ x) :
    (descend hN r).val R X h δ = x :=
  (existsUnique_isVal hN r h X δ).unique (existsUnique_isVal hN r h X δ).exists.choose_spec hx

theorem exists_rule_unitObj_of_covers
    (H : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
    ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
      ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
        σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N)) :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
  ∀ (R₀ : Type) [CommRing R₀] (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k) (r : Rule (levObj 𝔠 N) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : levObj 𝔠 N R X)
    (hX : X.IsRapoport) (δ : X.DetGen), r.val R X h δ = r₀.val R X hX δ) →
  ∃ r' : Rule (unitObj 𝔠 N) R₀ k,
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : levObj 𝔠 N R X) (δ : X.DetGen),
      r'.val R X h.1 δ = r.val R X h δ) ∧
    ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((N : ℕ) : R))
      (hX : X.IsRapoport) (δ : X.DetGen), r'.val R X h δ = r₀.val R X hX δ := by
  intro F _ _ _ 𝔠 N hN₁ R₀ _ k r₀ r hr
  have hN : HasLevelCovers 𝔠 N := H F 𝔠 N hN₁
  refine ⟨descend hN r, fun R _ _ X h δ ↦ descend_val_eq hN r X h.1 δ ?_,
    fun R _ _ X h hX δ ↦ descend_val_eq hN r X h δ ?_⟩
  · exact fun R' _ _ σ X' h' φ δ' hp d ↦ r.baseChange R R' σ X h X' h' φ δ δ' hp d
  · intro R' _ _ σ X' h' φ δ' hp d
    have hX' := hp.isRapoport _ hX
    rw [hr R' X' h' hX' δ']
    exact r₀.baseChange R R' σ X hX X' hX' φ δ δ' hp d

end GlobalTheory.RealMult.RuleDescend
