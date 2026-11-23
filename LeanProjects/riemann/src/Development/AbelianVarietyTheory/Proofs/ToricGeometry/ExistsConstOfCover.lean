import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.ThetaGroupFrame

theorem exists_const_of_cover {g : ℕ} {J : Type*} (D : J → Set (Fin g → ℂ))
    (G : J → (Fin g → ℂ) → ℂ) (hD : ∀ j, IsOpen (D j)) (hcov : ∀ z, ∃ j, z ∈ D j)
    (hG : ∀ j, DifferentiableOn ℂ (G j) (D j))
    (hc : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z)
    {S : Set (Fin g → ℂ)} (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ j z, z ∈ D j → ∀ l ∈ S, z + l ∈ D j ∧ G j (z + l) = G j z) :
    ∃ C : ℂ, ∀ j z, z ∈ D j → G j z = C := by
  classical
  choose jOf hjOf using hcov
  let F : (Fin g → ℂ) → ℂ := fun z => G (jOf z) z
  have hFeq : ∀ j z, z ∈ D j → F z = G j z := fun j z hz => hc _ _ _ (hjOf z) hz
  have hFdiff : Differentiable ℂ F := by
    intro z
    have hmem : D (jOf z) ∈ 𝓝 z := (hD _).mem_nhds (hjOf z)
    have hev : F =ᶠ[𝓝 z] G (jOf z) := by
      filter_upwards [hmem] with w hw
      exact hFeq _ _ hw
    exact ((hG _).differentiableAt hmem).congr_of_eventuallyEq hev
  have hFper : ∀ x, ∀ l ∈ S, F (x + l) = F x := by
    intro x l hl
    have h1 := hper (jOf x) x (hjOf x) l hl
    rw [hFeq _ _ h1.1, h1.2]
  refine ⟨F 0, fun j z hz => ?_⟩
  rw [← hFeq j z hz]
  exact GlobalTheory.entire_apply_eq_of_periodic_of_span_real hFdiff hS hFper z 0

abbrev ValLaws : Prop :=
  ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)

theorem top_le_wchart_iff {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (j : K → L.ι) (x : Z ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  unfold LB.wchart
  constructor
  · intro h k z _
    have hz : x z ∈ ⋂ k, ⇑(φ k) ⁻¹' ↑(L.U (j k)) := h (show z ∈ (⊤ : Z.Opens) from trivial)
    exact Set.mem_iInter.mp hz k
  · intro h z _
    show x z ∈ ⋂ k, ⇑(φ k) ⁻¹' ↑(L.U (j k))
    exact Set.mem_iInter.mpr fun k => h k (show z ∈ (⊤ : Z.Opens) from trivial)

theorem top_le_inf {X Z : Scheme.{0}} (x : Z ⟶ X) {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) := le_inf h h'

theorem valAt'_unit_ne_zero (hv : ValLaws) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) : valAt' x U s.val ≠ 0 := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  rw [he]
  intro h0
  have h1 := congrArg e s.mul_inv
  rw [map_mul, map_one, h0, zero_mul] at h1
  exact zero_ne_one h1

theorem valAt'_gen_linComb (hv : ValLaws) {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen)
    (x : Sp ℂ ⟶ Y) (j j' : K → L.ι) (hj : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j)
    (hj' : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j') :
    valAt' x (LB.wchart L φ j) (c.s j).val =
      (∏ k, valAt' (x ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valAt' x (LB.wchart L φ j') (c.s j').val := by
  have hV : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := top_le_inf x hj hj'
  obtain ⟨e, he⟩ := (hv Y x).2.1 _ hV
  have h3 := (hv Y x).2.2.1
  have h4 := (hv Y x).2.2.2.1
  have hcj := congrArg
    (fun w => ((Units.map (e : Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j') →* ℂ) w : ℂˣ) : ℂ)) (hc j j')
  unfold LB.LinComb at hcj
  dsimp only at hcj
  simp only [map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod,
    Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe] at hcj
  simp only [← he] at hcj
  unfold res pullU at hcj
  simp only [Units.coe_map, MonoidHom.coe_coe] at hcj
  simp only [h3 _ _ _ _ hV] at hcj
  rw [hcj]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  exact (h3 _ _ _ _ hV).trans (h4 X (φ i) (L.U (j i) ⊓ L.U (j' i)) (L.g (j i) (j' i)).val)

theorem top_le_wchart_two {X Y Z : Scheme.{0}} (L : LB X) (φ₀ φ₁ : Y ⟶ X) (j : Fin 2 → L.ι)
    (x : Z ⟶ Y) (y₀ y₁ : Z ⟶ X) (h₀ : x ≫ φ₀ = y₀) (h₁ : x ≫ φ₁ = y₁) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j ↔ ⊤ ≤ y₀ ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ y₁ ⁻¹ᵁ L.U (j 1) := by
  rw [top_le_wchart_iff, Fin.forall_fin_two]
  simp [h₀, h₁]

theorem valAt'_gen_two (hv : ValLaws) {X Y : Scheme.{0}} (L : LB X) (φ₀ φ₁ : Y ⟶ X) (k : ℕ)
    (c : LB.Gen (LB.LinComb L (K := Fin 2) ![φ₀, φ₁] ![(k : ℤ), -(k : ℤ)])) (hc : c.IsGen)
    (x : Sp ℂ ⟶ Y) (y₀ y₁ : Sp ℂ ⟶ X) (h₀ : x ≫ φ₀ = y₀) (h₁ : x ≫ φ₁ = y₁)
    (j j' : Fin 2 → L.ι) (a₀ : ⊤ ≤ y₀ ⁻¹ᵁ L.U (j 0)) (a₁ : ⊤ ≤ y₁ ⁻¹ᵁ L.U (j 1))
    (b₀ : ⊤ ≤ y₀ ⁻¹ᵁ L.U (j' 0)) (b₁ : ⊤ ≤ y₁ ⁻¹ᵁ L.U (j' 1)) :
    valAt' x (LB.wchart L ![φ₀, φ₁] j) (c.s j).val =
      valAt' y₀ (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val ^ k *
        (valAt' y₁ (L.U (j 1) ⊓ L.U (j' 1)) (L.g (j 1) (j' 1)).val ^ k)⁻¹ *
        valAt' x (LB.wchart L ![φ₀, φ₁] j') (c.s j').val := by
  have hj : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j :=
    (top_le_wchart_two L φ₀ φ₁ j x y₀ y₁ h₀ h₁).2 ⟨a₀, a₁⟩
  have hj' : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j' :=
    (top_le_wchart_two L φ₀ φ₁ j' x y₀ y₁ h₀ h₁).2 ⟨b₀, b₁⟩
  rw [valAt'_gen_linComb hv L ![φ₀, φ₁] ![(k : ℤ), -(k : ℤ)] c hc x j j' hj hj']
  simp [Fin.prod_univ_two, h₀, h₁, _root_.zpow_neg, zpow_natCast]

theorem lift_translPt {S : Scheme.{0}} (A : Over S) [GrpObj A] {T B : Over S} (p : B ⟶ T)
    (x : T ⟶ A) (y : B ⟶ A) : lift p y ≫ Out.translPt A x = (p ≫ x) * y := by
  unfold Out.translPt
  rw [CategoryTheory.Hom.mul_def, ← Category.assoc, CartesianMonoidalCategory.comp_lift]
  simp

private lemma herm_swap_eq_zero_of_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (l a : Fin g → ℂ) :
    a ⬝ᵥ Hm.mulVec (star l) = starRingEnd ℂ (l ⬝ᵥ Hm.mulVec (star a)) := by
  simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply j i]
  simp
  ring

theorem exp_herm_eq {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (l a : Fin g → ℂ) (n : ℤ) (hn : (n : ℝ) = (l ⬝ᵥ Hm.mulVec (star a)).im) :
    cexp (Real.pi * (l ⬝ᵥ Hm.mulVec (star a))) = cexp (Real.pi * (a ⬝ᵥ Hm.mulVec (star l))) := by
  rw [herm_swap_eq_zero_of_eq_zero hH l a]
  have e : (Real.pi : ℂ) * (l ⬝ᵥ Hm.mulVec (star a)) =
      Real.pi * starRingEnd ℂ (l ⬝ᵥ Hm.mulVec (star a)) + n * (2 * Real.pi * Complex.I) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, ← hn] <;> ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, _root_.mul_one]

theorem thetaGrp_in_frame :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a : u.Λ), 0 < k → ∀ (T : Over (Sp ℂ)) (p : (𝟙_ (Over (Sp ℂ)) ⟶ T)) (θ : Out.ThetaGrp P.A P.L k T), p ≫ θ.pt = u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) → ∃ C : ℂ, ∀ (j : Fin 2 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j 1) → valAt' (lift p (u.ex z)).left _ (θ.φ.s j).val * u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ^ k = C * cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))))) * u.fr (j 0) z ^ k) := by
  intro hv han P u Hm χ Ef hAH k a hk T p θ hp
  obtain ⟨hH, hχ, hEf, hfr⟩ := hAH
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'

  have h₀ : ∀ z, (lift p (u.ex z)).left ≫ (snd T P.A).left = (u.ex z).left := fun z => by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_snd]
  have h₁ : ∀ z, (lift p (u.ex z)).left ≫ (Out.translPt P.A θ.pt).left =
      (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left := fun z => by
    rw [← Over.comp_left, lift_translPt, hp, ← u.ex_add, add_comm]

  let D : (Fin 2 → P.L.ι) → Set (Fin P.g → ℂ) := fun j =>
    {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) ∧
      ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j 1)}
  let V : (Fin 2 → P.L.ι) → (Fin P.g → ℂ) → ℂ := fun j z =>
    valAt' (lift p (u.ex z)).left ((Out.thetaLB P.A P.L (k : ℤ) θ.pt).U j) (θ.φ.s j).val
  let G : (Fin 2 → P.L.ι) → (Fin P.g → ℂ) → ℂ := fun j z =>
    V j z * u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ^ k *
      cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ)))) / u.fr (j 0) z ^ k
  have hopen : ∀ j, IsOpen (D j) := fun j =>
    ((u.hol _ 1).1).inter (((u.hol _ 1).1).preimage (continuous_id.add continuous_const))
  have hcov : ∀ z, ∃ j, z ∈ D j := by
    intro z
    have pick : ∀ y : Sp ℂ ⟶ P.A.left, ∃ i, ⊤ ≤ y ⁻¹ᵁ P.L.U i := fun y => by
      have hy : y (default : PrimeSpectrum ℂ) ∈ (⨆ i, P.L.U i) := by
        rw [P.isLB.cover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      exact ⟨i, ((hv _ y).1 _).2 hi⟩
    obtain ⟨i₀, hi₀⟩ := pick (u.ex z).left
    obtain ⟨i₁, hi₁⟩ := pick (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left
    exact ⟨![i₀, i₁], show _ ∧ _ from ⟨hi₀, hi₁⟩⟩
  have hVdiff : ∀ j, DifferentiableOn ℂ (V j) (D j) := by
    intro j
    have hh := han (Fin P.g → ℂ) Set.univ T P.A (fun _ => p) u.ex
      (fun U f => by
        by_cases hU : ⊤ ≤ p.left ⁻¹ᵁ U
        · simp only [Set.mem_univ, true_and, hU, Set.ofPred_true]
          exact ⟨isOpen_univ, differentiableOn_const _⟩
        · simp only [Set.mem_univ, true_and, hU, Set.ofPred_false]
          exact ⟨isOpen_empty, differentiableOn_empty⟩)
      (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
      ((Out.thetaLB P.A P.L (k : ℤ) θ.pt).U j) (θ.φ.s j).val
    refine hh.2.mono fun z hz => ⟨trivial, ?_⟩
    exact (top_le_wchart_two P.L (snd T P.A).left (Out.translPt P.A θ.pt).left j
      (lift p (u.ex z)).left _ _ (h₀ z) (h₁ z)).2 hz
  have hlin : Differentiable ℂ
      (fun z : Fin P.g → ℂ => z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))) := by
    simp only [dotProduct]
    fun_prop
  have hGdiff : ∀ j, DifferentiableOn ℂ (G j) (D j) := by
    intro j
    have hfr0 : DifferentiableOn ℂ (u.fr (j 0)) (D j) := (u.fr_hol _).mono fun z hz => hz.1
    have hfr1 : DifferentiableOn ℂ
        (fun z => u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (D j) :=
      (u.fr_hol _).comp (differentiable_id.add_const _).differentiableOn (fun z hz => hz.2)
    have hp0 : DifferentiableOn ℂ (fun z => u.fr (j 0) z ^ k) (D j) := hfr0.pow k
    have hp1 : DifferentiableOn ℂ
        (fun z => u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ^ k) (D j) := hfr1.pow k
    have hE : DifferentiableOn ℂ
        (fun z => cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))))) (D j) :=
      (hlin.const_mul _).cexp.differentiableOn
    have hq := (((hVdiff j).mul hp1).mul hE).mul
      (hp0.inv (fun z (hz : z ∈ D j) => pow_ne_zero _ (u.fr_ne _ _ hz.1)))
    refine hq.congr fun z _ => ?_
    simp only [G, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]
  have hcompat : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z := by
    intro j j' z hz hz'
    have hgen : V j z =
        valAt' (u.ex z).left (P.L.U (j 0) ⊓ P.L.U (j' 0)) (P.L.g (j 0) (j' 0)).val ^ k *
          (valAt' (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left (P.L.U (j 1) ⊓ P.L.U (j' 1))
            (P.L.g (j 1) (j' 1)).val ^ k)⁻¹ * V j' z :=
      valAt'_gen_two hv P.L (snd T P.A).left (Out.translPt P.A θ.pt).left k θ.φ θ.isGen
        (lift p (u.ex z)).left _ _ (h₀ z) (h₁ z) j j' hz.1 hz.2 hz'.1 hz'.2
    have hc0 := u.fr_compat (j 0) (j' 0) z (top_le_inf _ hz.1 hz'.1)
    have hc1 := u.fr_compat (j 1) (j' 1) _ (top_le_inf _ hz.2 hz'.2)
    have hn0 := valAt'_unit_ne_zero hv _ _ (top_le_inf _ hz.1 hz'.1) (P.L.g (j 0) (j' 0))
    have hn1 := valAt'_unit_ne_zero hv _ _ (top_le_inf _ hz.2 hz'.2) (P.L.g (j 1) (j' 1))
    have hf0 := u.fr_ne _ _ hz'.1
    have hf1 := u.fr_ne _ _ hz'.2
    simp only [G]
    rw [hgen, hc0, hc1]
    field_simp
    ring
  have hper : ∀ j z, z ∈ D j → ∀ l ∈ (u.Λ : Set (Fin P.g → ℂ)),
      z + l ∈ D j ∧ G j (z + l) = G j z := by
    intro j z hz l hl
    have hex : ∀ y, u.ex (y + l) = u.ex y := fun y => by
      rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
    have hzl : z + l + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) = z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) + l := by
      abel
    have hmem : z + l ∈ D j := by
      refine ⟨?_, ?_⟩
      · rw [hex]; exact hz.1
      · rw [hzl, hex]; exact hz.2
    refine ⟨hmem, ?_⟩
    have hV : V j (z + l) = V j z := by simp only [V, hex]
    have hf0 := u.fr_ne _ _ hmem.1
    have hf1 := u.fr_ne _ _ hmem.2
    rw [hzl] at hf1
    have e0 := hfr ⟨l, hl⟩ (j 0) z hz.1
    have e1 := hfr ⟨l, hl⟩ (j 1) _ hz.2
    dsimp only at e0 e1
    have hχ0 : χ ⟨l, hl⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l, hl⟩
    have hh := exp_herm_eq hH l (a : Fin P.g → ℂ) (Ef ⟨l, hl⟩ a) (hEf ⟨l, hl⟩ a)
    have eA : cexp ((Real.pi : ℂ) * ((z + l) ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ)))) =
        cexp ((Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ)))) *
          cexp ((Real.pi : ℂ) * (l ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ)))) := by
      rw [add_dotProduct, mul_add, Complex.exp_add]
    have eB : cexp ((Real.pi : ℂ) * ((z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ⬝ᵥ Hm.mulVec (star l)) +
          (Real.pi : ℂ) / 2 * (l ⬝ᵥ Hm.mulVec (star l))) ^ k =
        cexp ((Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star l)) +
          (Real.pi : ℂ) / 2 * (l ⬝ᵥ Hm.mulVec (star l))) ^ k *
          cexp ((Real.pi : ℂ) * ((a : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star l))) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
      have hkk : (k : ℂ) * (k : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hk0
      linear_combination ((Real.pi : ℂ) * ((a : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star l))) * hkk
    simp only [G, hV]
    rw [hzl, e0, e1, eA, mul_pow, mul_pow, mul_pow, mul_pow, eB, hh]
    field_simp
  obtain ⟨C, hC⟩ := exists_const_of_cover D G hopen hcov hGdiff hcompat u.full hper
  refine ⟨C, fun j z hz0 hz1 => ?_⟩
  have h1 := hC j z ⟨hz0, hz1⟩
  have hf0 := u.fr_ne _ _ hz0
  simp only [G, V] at h1
  rw [div_eq_iff (pow_ne_zero _ hf0)] at h1
  have hE : cexp ((Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ)))) *
      cexp (-((Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination cexp (-((Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))))) * h1 -
    (valAt' (lift p (u.ex z)).left ((Out.thetaLB P.A P.L (k : ℤ) θ.pt).U j) (θ.φ.s j).val *
      u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ^ k) * hE

end GlobalTheory.ThetaGroupFrame
