import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace ThetaModelGroup

theorem grpObj_of_points {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C] (X : C)
    {A : Type*} [AddCommGroup A] (ex : A → (𝟙_ C ⟶ X)) (hs : Function.Surjective ex) (m : X ⊗ X ⟶ X) (i : X ⟶ X)
    (hm : ∀ z w, lift (ex z) (ex w) ≫ m = ex (z + w)) (hi : ∀ z, ex z ≫ i = ex (-z))
    (e1 : ∀ f g : X ⟶ X, (∀ y : 𝟙_ C ⟶ X, y ≫ f = y ≫ g) → f = g)
    (e2 : ∀ f g : X ⊗ X ⟶ X, (∀ y : 𝟙_ C ⟶ X ⊗ X, y ≫ f = y ≫ g) → f = g)
    (e3 : ∀ f g : (X ⊗ X) ⊗ X ⟶ X, (∀ y : 𝟙_ C ⟶ (X ⊗ X) ⊗ X, y ≫ f = y ≫ g) → f = g) :
    ∃ (_ : GrpObj X), IsCommMonObj X ∧ ∀ z w, ex (z + w) = ex z * ex w := by
  have hu : ∀ y : 𝟙_ C ⟶ X, y ≫ toUnit X = 𝟙 _ := fun y => Subsingleton.elim _ _
  have p2 : ∀ y : 𝟙_ C ⟶ X ⊗ X, ∃ z w, y = lift (ex z) (ex w) := fun y => by
    obtain ⟨z, hz⟩ := hs (y ≫ fst _ _)
    obtain ⟨w, hw⟩ := hs (y ≫ snd _ _)
    exact ⟨z, w, by rw [hz, hw]; ext <;> simp⟩
  have p3 : ∀ y : 𝟙_ C ⟶ (X ⊗ X) ⊗ X, ∃ z w v, y = lift (lift (ex z) (ex w)) (ex v) := fun y => by
    obtain ⟨z, w, hz⟩ := p2 (y ≫ fst _ _)
    obtain ⟨v, hw⟩ := hs (y ≫ snd _ _)
    exact ⟨z, w, v, by rw [← hz, hw]; ext <;> simp⟩
  let G : GrpObj X :=
    { one := ex 0
      mul := m
      inv := i
      one_mul := by
        rw [← cancel_epi (λ_ X).inv, Iso.inv_hom_id]
        refine e1 _ _ fun y => ?_
        obtain ⟨z, rfl⟩ := hs y
        have : ex z ≫ (λ_ X).inv ≫ ex 0 ▷ X = lift (ex 0) (ex z) := by
          ext
          · simp [reassoc_of% hu]
          · simp
        rw [reassoc_of% this, hm, zero_add, Category.comp_id]
      mul_one := by
        rw [← cancel_epi (ρ_ X).inv, Iso.inv_hom_id]
        refine e1 _ _ fun y => ?_
        obtain ⟨z, rfl⟩ := hs y
        have : ex z ≫ (ρ_ X).inv ≫ X ◁ ex 0 = lift (ex z) (ex 0) := by
          ext
          · simp
          · simp [reassoc_of% hu]
        rw [reassoc_of% this, hm, add_zero, Category.comp_id]
      mul_assoc := by
        refine e3 _ _ fun y => ?_
        obtain ⟨z, w, v, rfl⟩ := p3 y
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hm, hm, hm, hm,
          add_assoc]
      left_inv := by
        refine e1 _ _ fun y => ?_
        obtain ⟨z, rfl⟩ := hs y
        rw [comp_lift_assoc, hi, Category.comp_id, hm, reassoc_of% hu, neg_add_cancel]
      right_inv := by
        refine e1 _ _ fun y => ?_
        obtain ⟨z, rfl⟩ := hs y
        rw [comp_lift_assoc, hi, Category.comp_id, hm, reassoc_of% hu, add_neg_cancel] }
  refine ⟨G, ⟨e2 _ _ fun y => ?_⟩, fun z w => (hm z w).symm⟩
  obtain ⟨z, w, rfl⟩ := p2 y
  change _ ≫ _ ≫ m = _ ≫ m
  rw [lift_braiding_hom_assoc, hm, hm, add_comm]

variable {X Y : Over (Sp ℂ)}

def RegOn (U : Y.left.Opens) (s : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ) : Prop :=
  ∃ ρ : Γ(Y.left, U), ∀ y' : 𝟙_ (Over (Sp ℂ)) ⟶ Y, ⊤ ≤ y'.left ⁻¹ᵁ U → valAt' y'.left U ρ = s y'

def RegAt (y : 𝟙_ (Over (Sp ℂ)) ⟶ Y) (s : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ) : Prop :=
  ∃ U : Y.left.Opens, ⊤ ≤ y.left ⁻¹ᵁ U ∧ RegOn U s

theorem RegOn.mono {U V : Y.left.Opens} {s : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (h : RegOn U s) (e : V ≤ U) :
    RegOn V s := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨resG _ e ρ, fun y' hy' => (valAt'_res _ e ρ hy').trans (hρ y' (top_le_preimage_mono _ e hy'))⟩

theorem exists_regOn_family {κ : Type} [Finite κ] {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y}
    {s : κ → (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (h : ∀ c, RegAt y (s c)) :
    ∃ U : Y.left.Opens, ⊤ ≤ y.left ⁻¹ᵁ U ∧ ∀ c, RegOn U (s c) := by
  classical
  have := Fintype.ofFinite κ
  choose U hU hR using h
  refine ⟨Finset.univ.inf U, ?_, fun c => (hR c).mono (Finset.inf_le (Finset.mem_univ c))⟩
  generalize (Finset.univ : Finset κ) = t
  induction t using Finset.induction_on with
  | empty => exact le_top
  | insert a t _ ih =>
    rw [Finset.inf_insert]
    exact (top_le_preimage_inf _ _ _).2 ⟨hU a, ih⟩

theorem RegAt.mul {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y} {s t : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (hs : RegAt y s) (ht : RegAt y t) :
    RegAt y (fun y' => s y' * t y') := by
  obtain ⟨U, hU, hs⟩ := hs
  obtain ⟨V, hV, ht⟩ := ht
  obtain ⟨ρ, hρ⟩ := hs.mono (inf_le_left (b := V))
  obtain ⟨ρ', hρ'⟩ := ht.mono (inf_le_right (a := U))
  exact ⟨U ⊓ V, (top_le_preimage_inf _ _ _).2 ⟨hU, hV⟩, ρ * ρ', fun y' hy' => by
    rw [valAt'_mul, hρ y' hy', hρ' y' hy']⟩

theorem RegAt.sum {κ : Type} [Fintype κ] {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y}
    {s : κ → (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (h : ∀ c, RegAt y (s c)) : RegAt y (fun y' => ∑ c, s c y') := by
  obtain ⟨U, hU, hR⟩ := exists_regOn_family h
  choose ρ hρ using hR
  exact ⟨U, hU, ∑ c, ρ c, fun y' hy' => by
    rw [valAt'_sum]; exact Finset.sum_congr rfl fun c _ => hρ c y' hy'⟩

theorem RegAt.comp {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y} (p : Y ⟶ X) {s : (𝟙_ (Over (Sp ℂ)) ⟶ X) → ℂ}
    (h : RegAt (y ≫ p) s) : RegAt y (fun y' => s (y' ≫ p)) := by
  obtain ⟨U, hU, ρ, hρ⟩ := h
  refine ⟨p.left ⁻¹ᵁ U, (top_le_preimage_comp _ _ _).1 hU, (p.left.app U).hom ρ, fun y' hy' => ?_⟩
  exact (valAt'_comp _ _ _ _).trans (hρ (y' ≫ p) ((top_le_preimage_comp _ _ _).2 hy'))

theorem exists_regOn_div {κ : Type} [Finite κ] {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y}
    {s : κ → (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (h : ∀ c, RegAt y (s c)) (c : κ) (hc : s c y ≠ 0) :
    ∃ U : Y.left.Opens, ⊤ ≤ y.left ⁻¹ᵁ U ∧ (∀ y' : 𝟙_ (Over (Sp ℂ)) ⟶ Y, ⊤ ≤ y'.left ⁻¹ᵁ U → s c y' ≠ 0) ∧
      ∀ c', RegOn U (fun y' => s c' y' / s c y') := by
  obtain ⟨U, hU, hR⟩ := exists_regOn_family h
  obtain ⟨q, hq⟩ := hR c
  have e : Y.left.basicOpen q ≤ U := Y.left.basicOpen_le q
  have hne : ∀ y' : 𝟙_ (Over (Sp ℂ)) ⟶ Y, ⊤ ≤ y'.left ⁻¹ᵁ Y.left.basicOpen q → s c y' ≠ 0 := fun y' hy' => by
    rw [← hq y' (top_le_preimage_mono _ e hy')]
    exact (top_le_preimage_basicOpen_iff _ _ _).1 hy'
  refine ⟨Y.left.basicOpen q, (top_le_preimage_basicOpen_iff _ _ _).2 (by rwa [hq y hU]), hne, fun c' => ?_⟩
  obtain ⟨ρ, hρ⟩ := (hR c').mono e
  obtain ⟨u, hu⟩ : IsUnit (resG _ e q) := Y.left.toRingedSpace.isUnit_res_basicOpen q
  refine ⟨ρ * (u⁻¹).val, fun y' hy' => ?_⟩
  rw [valAt'_mul, valAt'_units_inv _ hy', hρ y' hy', hu, valAt'_res _ e q hy', hq y' (top_le_preimage_mono _ e hy')]
  exact (div_eq_mul_inv _ _).symm

theorem exists_chart {κ : Type} {D : κ → X.left.Opens} (hD : ⨆ c, D c = ⊤) (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) :
    ∃ c, ⊤ ≤ x.left ⁻¹ᵁ D c := by
  have : x.left (default : PrimeSpectrum ℂ) ∈ ⨆ c, D c := by rw [hD]; trivial
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨c, (top_le_preimage_iff_mem _ _).2 hc⟩

theorem valAt'_eval₂ {κ : Type} (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) (U : X.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ U)
    (r : κ → Γ(X.left, U)) (F : MvPolynomial κ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) = MvPolynomial.eval (fun c => valAt' x.left U (r c)) F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C, MvPolynomial.eval_C]
    exact valAt'_constFn x.left X.hom (Over.w x) U a h
  | add p q hp hq => rw [MvPolynomial.eval₂_add, valAt'_add, hp, hq, map_add]
  | mul_X p c hp => rw [MvPolynomial.eval₂_mul, valAt'_mul, hp, MvPolynomial.eval₂_X, map_mul, MvPolynomial.eval_X]

def PointCriterion : Prop :=
  ∀ (X Y : Over (Sp ℂ)), IsReduced Y.left → LocallyOfFiniteType Y.hom → ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y

theorem hom_ext_points (H : PointCriterion) (h1 : IsReduced Y.left) (h2 : LocallyOfFiniteType Y.hom)
    {κ : Type} {D : κ → X.left.Opens} (hD : ⨆ c, D c = ⊤) (ha : ∀ c, IsAffineOpen (D c)) (f g : Y ⟶ X)
    (h : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ Y, y ≫ f = y ≫ g) : f = g := by
  refine (H X Y h1 h2 (fun y => y ≫ f) fun y => ?_).unique (fun _ => rfl) (fun y => (h y).symm)
  obtain ⟨c, hc⟩ := exists_chart hD (y ≫ f)
  exact ⟨f.left ⁻¹ᵁ D c, D c, (top_le_preimage_comp _ _ _).1 hc, ha c,
    fun y' hy' => (top_le_preimage_comp _ _ _).2 hy',
    fun φ => ⟨(f.left.app (D c)).hom φ, fun y' _ => valAt'_comp _ _ _ _⟩⟩

theorem exists_hom_of_coords (H : PointCriterion) (h1 : IsReduced Y.left) (h2 : LocallyOfFiniteType Y.hom)
    {κ A : Type} [Finite κ] {D : κ → X.left.Opens} (hD : ⨆ c, D c = ⊤) (ex : A → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (θ : κ → A → ℂ)
    (hc : ∀ c, IsAffineOpen (D c) ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ θ c z ≠ 0) ∧ ∃ r : κ → Γ(X.left, D c),
      (∀ c' z, θ c z ≠ 0 → valAt' (ex z).left (D c) (r c') = θ c' z / θ c z) ∧
      ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial κ ℂ, f = MvPolynomial.eval₂ (RingHom.comp
        (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F)
    (G : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → A)
    (hG : ∀ y, ∃ l : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ, l y ≠ 0 ∧ ∀ c, RegAt y (fun y' => l y' * θ c (G y'))) :
    ∃ m : Y ⟶ X, ∀ y, y ≫ m = ex (G y) := by
  refine (H X Y h1 h2 (fun y => ex (G y)) fun y => ?_).exists
  obtain ⟨c, hcy⟩ := exists_chart hD (ex (G y))
  obtain ⟨ha, hm, r, hr, hF⟩ := hc c
  obtain ⟨l, hl, hR⟩ := hG y
  obtain ⟨U, hU, hne, hq⟩ := exists_regOn_div hR c (mul_ne_zero hl ((hm _).1 hcy))
  choose ρ hρ using hq
  refine ⟨U, D c, hU, ha, fun y' hy' => (hm _).2 (right_ne_zero_of_mul (hne y' hy')), fun φ => ?_⟩
  obtain ⟨F, rfl⟩ := hF φ
  refine ⟨MvPolynomial.eval₂ (RingHom.comp (Y.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) ρ F, fun y' hy' => ?_⟩
  have h0 := right_ne_zero_of_mul (hne y' hy')
  rw [valAt'_eval₂ y' U hy', valAt'_eval₂ _ _ ((hm _).2 h0)]
  congr 2
  funext c'
  rw [hρ c' y' hy', hr c' _ h0]
  exact mul_div_mul_left _ _ (left_ne_zero_of_mul (hne y' hy'))

def IsLevel {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (f : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
    eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z

theorem IsLevel.neg {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {N : ℕ} {f : (Fin g → ℂ) → ℂ} (h : IsLevel τ N f) :
    IsLevel τ N (fun z => f (-z)) := by
  refine ⟨h.1.comp (differentiable_id (𝕜 := ℂ) (E := Fin g → ℂ)).neg, fun n n' z => ?_⟩
  have := h.2 (-n) (-n') (-z)
  simp only [ofIntVec_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg] at this
  rw [← this]
  congr 1
  abel

theorem IsLevel.sq {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {N : ℕ} {f : (Fin g → ℂ) → ℂ} (h : IsLevel τ N f) :
    IsLevel τ (N * 2) (fun z => f z ^ 2) := by
  refine ⟨h.1.pow 2, fun n n' z => ?_⟩
  simp only [h.2, mul_pow, eC]
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem locallyOfFiniteType_tensor [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

end ThetaModelGroup

open ThetaModelGroup in

theorem thetaModel_groupLaw : (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X
    Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U
    : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a
    w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b
    w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w
    | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w))
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w))
    w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (X : Over (Sp
    ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left,
    U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶
    X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X Y : Over (Sp
    ℂ)), IsReduced Y.left → LocallyOfFiniteType Y.hom → ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp
    ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D
    : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶
    Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left,
    U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F
    y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y) → (∀ (X Y : Over (Sp
    ℂ)), IsReduced X.left → IsReduced Y.left → LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom → IsReduced (X
    ⊗ Y).left) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
    g) → ∀ N : ℕ, 1 ≤ N → ∀ f f' : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n'
    : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → (Differentiable ℂ f' ∧ ∀ (n n'
    : Fin g → ℤ) z, f' (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f' z) → ∃ (n : ℕ) (h k : Fin n → (Fin g →
    ℂ) → ℂ), (∀ i, (Differentiable ℂ (h i) ∧ ∀ (n n' : Fin g → ℤ) z, (h i) (z + τ *ᵥ ofIntVec n +
    ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * (h i) z) ∧ (Differentiable ℂ (k i) ∧ ∀ (n n' : Fin g → ℤ) z, (k i) (z + τ *ᵥ ofIntVec n +
    ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * (k i) z)) ∧ ∀ z w, f (z + w) * f' (z - w) = ∑ i, h i z * k i w) → (∀ (g : ℕ) (τ
    : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
    g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n'
    : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z
    + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 +
    ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
    τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
    g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n
    n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c
    : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N
    : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
    g) → ∀ N : ℕ, 2 ≤ N → ∀ z, ∃ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n'
    : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) ∧ f z ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
    g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice
    τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g →
    ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g
    : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp
    ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin
    N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
    (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
    U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ
    : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left,
    D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) •
    z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r
    c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c
    i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin
    g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso
    (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g →
    ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec
    n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec
    n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠
    0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → ∃ (_
    : GrpObj X), IsCommMonObj X ∧ ∀ z w, ex (z + w) = ex z * ex w) := by
  intro _ _ H Hred Hadd Hth _ Hne _ g τ hτ N hN X ex D ⟨hint, hprop, hs, hker, _, hc, hD⟩ hreg
  have hX : IsReduced X.left := inferInstance
  have hXf : LocallyOfFiniteType X.hom := inferInstance
  have hXXf : LocallyOfFiniteType (X ⊗ X).hom := locallyOfFiniteType_tensor
  have hXX : IsReduced (X ⊗ X).left := Hred X X hX hX hXf hXf
  have hXXXf : LocallyOfFiniteType ((X ⊗ X) ⊗ X).hom := locallyOfFiniteType_tensor
  have hXXX : IsReduced ((X ⊗ X) ⊗ X).left := Hred _ X hXX hX hXXf hXf
  have hlev := (Hth g τ hτ N (by omega)).1
  generalize hθ : (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) = θ
  have hθ' : ∀ c z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) = θ c z :=
    fun c z => by rw [← hθ]
  simp only [hθ'] at hc hlev
  replace hlev : ∀ c, IsLevel τ N (θ c) := hlev
  have hc' := fun c => And.intro (hc c).1 (hc c).2.2
  choose s hs' using hs
  have hch : ∀ x, ∃ a, θ a (s x) ≠ 0 := fun x => by
    obtain ⟨a, ha⟩ := exists_chart hD (ex (s x))
    exact ⟨a, ((hc a).2.2.1 _).1 ha⟩
  have hq : ∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), IsLevel τ (N * d) p → IsLevel τ (N * d) q → ∀ x, q (s x) ≠ 0 →
      RegAt x (fun x' => p (s x') / q (s x')) := fun d p q hp hq x hx => by
    obtain ⟨U, φ, hU⟩ := hreg d p q hp hq
    refine ⟨U, by simpa only [hs'] using (hU (s x)).1.2 hx, φ, fun x' hx' => ?_⟩
    have := hU (s x')
    rw [hs'] at this
    exact this.2 (this.1.1 hx')
  have hsub : ∀ z, s (ex z) - z ∈ periodLattice τ := fun z => (hker _ _).1 (hs' _)
  obtain ⟨m, hm⟩ := exists_hom_of_coords H hXX hXXf hD ex θ hc'
    (fun y => s (y ≫ fst X X) + s (y ≫ snd X X)) (fun y => by
      obtain ⟨a, ha⟩ := hch (y ≫ fst X X)
      obtain ⟨b, hb⟩ := hch (y ≫ snd X X)
      obtain ⟨f', hf', hf0⟩ := Hne g τ hτ N (by omega) (s (y ≫ fst X X) - s (y ≫ snd X X))
      refine ⟨fun y' => f' (s (y' ≫ fst X X) - s (y' ≫ snd X X)) /
        (θ a (s (y' ≫ fst X X)) ^ 2 * θ b (s (y' ≫ snd X X)) ^ 2),
        div_ne_zero hf0 (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)), fun c => ?_⟩
      obtain ⟨n, h, k, hhk, hsum⟩ := Hadd g τ hτ N (by omega) (θ c) f' (hlev c) hf'
      have := RegAt.sum (y := y) fun i : Fin n =>
        ((hq 2 (h i) _ (by rw [mul_comm]; exact (hhk i).1) (hlev a).sq _ (pow_ne_zero _ ha)).comp (fst X X)).mul
        ((hq 2 (k i) _ (by rw [mul_comm]; exact (hhk i).2) (hlev b).sq _ (pow_ne_zero _ hb)).comp (snd X X))
      convert this using 2 with y'
      rw [div_mul_eq_mul_div, mul_comm (f' _), hsum, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [div_mul_div_comm])
  obtain ⟨i, hi⟩ := exists_hom_of_coords H hX hXf hD ex θ hc' (fun y => - s y) (fun y => by
      obtain ⟨a, ha⟩ := hch y
      refine ⟨fun y' => (θ a (s y'))⁻¹, inv_ne_zero ha, fun c => ?_⟩
      have := hq 1 _ _ (by rw [Nat.mul_one]; exact (hlev c).neg) (by rw [Nat.mul_one]; exact hlev a) y ha
      convert this using 2 with y'
      rw [div_eq_inv_mul])
  have ha : ∀ c, IsAffineOpen (D c) := fun c => (hc c).1
  refine grpObj_of_points X ex (fun x => ⟨s x, hs' x⟩) m i (fun z w => ?_) (fun z => ?_)
    (hom_ext_points H hX hXf hD ha) (hom_ext_points H hXX hXXf hD ha) (hom_ext_points H hXXX hXXXf hD ha)
  · rw [hm, lift_fst, lift_snd, hker, add_sub_add_comm]
    exact add_mem (hsub z) (hsub w)
  · rw [hi, hker, neg_sub_neg, ← neg_sub]
    exact neg_mem (hsub z)

end GlobalTheory
