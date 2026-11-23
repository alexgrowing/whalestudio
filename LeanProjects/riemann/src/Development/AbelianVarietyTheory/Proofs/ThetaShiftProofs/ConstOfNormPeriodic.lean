import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FrameValue

open CubeValues SymmetricSemicharacter EigenNorm

section Calculus

def chartAt {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) : L.ι :=
  (ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (x (default : PrimeSpectrum ℂ))).choose

theorem le_chartAt {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) : ⊤ ≤ x ⁻¹ᵁ L.U (chartAt hL x) :=
  ((valueRules X x).1 _).2 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (x (default : PrimeSpectrum ℂ))).choose_spec

theorem val_sec {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {L : LB X} (s : L.Sec) (i j : L.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x (L.U i) (s.f i) = valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j) (s.f j) := by
  have hij := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  obtain ⟨e, he⟩ := (valueRules X x).2.1 _ hij
  rw [← (valueRules X x).2.2.1 _ _ inf_le_left (s.f i) hij, ← (valueRules X x).2.2.1 _ _ inf_le_right (s.f j) hij,
    he, he, he, ← map_mul]
  exact congrArg e (s.compat i j)

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ}

def IsLift (φ : K → (Y ⟶ A.left)) (y : Sp ℂ ⟶ Y) (z : K → Fin g → ℂ) : Prop :=
  ∀ k, y ≫ φ k = (u.ex (z k)).left

def frameProd (ε : K → ℤ) (z : K → Fin g → ℂ) (j : K → L.ι) : ℂ := ∏ k, u.fr (j k) (z k) ^ ε k

def secValIn (s : LB.Sec (LB.LinComb L φ ε)) (y : Sp ℂ ⟶ Y) (z : K → Fin g → ℂ) (j : K → L.ι) : ℂ :=
  valAt' y (L.wchart φ j) (s.f j) / frameProd u ε z j

def genValIn (t : LB.Gen (LB.LinComb L φ ε)) (y : Sp ℂ ⟶ Y) (z : K → Fin g → ℂ) (j : K → L.ι) : ℂ :=
  valAt' y (L.wchart φ j) (t.s j).val / frameProd u ε z j

def secVal (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε)) (y : Sp ℂ ⟶ Y) (z : K → Fin g → ℂ) : ℂ :=
  secValIn u s y z (fun k => chartAt hL (y ≫ φ k))

def genVal (hL : L.IsLB) (t : LB.Gen (LB.LinComb L φ ε)) (y : Sp ℂ ⟶ Y) (z : K → Fin g → ℂ) : ℂ :=
  genValIn u t y z (fun k => chartAt hL (y ≫ φ k))

theorem le_wchart_chartAt (hL : L.IsLB) (φ : K → (Y ⟶ A.left)) (y : Sp ℂ ⟶ Y) :
    ⊤ ≤ y ⁻¹ᵁ L.wchart φ (fun k => chartAt hL (y ≫ φ k)) :=
  (le_preimage_wchart y L φ _).2 fun _ => le_chartAt hL _

variable {u}

theorem IsLift.le_iff {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} (hz : IsLift u φ y z) (j : K → L.ι) :
    ⊤ ≤ y ⁻¹ᵁ L.wchart φ j ↔ ∀ k, ⊤ ≤ (u.ex (z k)).left ⁻¹ᵁ L.U (j k) := by
  refine (le_preimage_wchart y L φ j).trans (forall_congr' fun k => ?_)
  rw [hz k]

theorem frameProd_ne_zero {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} (hz : IsLift u φ y z) (ε : K → ℤ) {j : K → L.ι}
    (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) : frameProd u ε z j ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ ((hz.le_iff j).1 hj k))

theorem secValIn_eq (s : LB.Sec (LB.LinComb L φ ε)) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} (hz : IsLift u φ y z)
    {j j' : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) (hj' : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j') :
    secValIn u s y z j = secValIn u s y z j' := by
  have e₁ := val_sec y s j j' hj hj'
  have e₂ := val_linComb y valueRules L φ ε j j' hj hj'
  have e₃ : frameProd u ε z j = valAt' y (L.wchart φ j ⊓ L.wchart φ j') ((L.LinComb φ ε).g j j').val *
      frameProd u ε z j' := by
    rw [e₂, frameProd, frameProd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [u.fr_compat (j k) (j' k) (z k) ((le_preimage_inf _ _ _).2 ⟨(hz.le_iff j).1 hj k, (hz.le_iff j').1 hj' k⟩),
      mul_zpow, hz k]
  have n := val_unit_ne_zero y valueRules ((le_preimage_inf y _ _).2 ⟨hj, hj'⟩) ((L.LinComb φ ε).g j j')
  rw [secValIn, secValIn, e₃]
  exact (congrArg (· / _) e₁).trans (mul_div_mul_left _ _ n)

theorem genValIn_eq {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ}
    (hz : IsLift u φ y z) {j j' : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) (hj' : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j') :
    genValIn u t y z j = genValIn u t y z j' := secValIn_eq (genSec t ht) hz hj hj'

theorem secVal_eq (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε)) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ}
    (hz : IsLift u φ y z) {j : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) : secVal u hL s y z = secValIn u s y z j :=
  secValIn_eq s hz (le_wchart_chartAt hL φ y) hj

theorem genVal_eq (hL : L.IsLB) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ}
    (hz : IsLift u φ y z) {j : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) : genVal u hL t y z = genValIn u t y z j :=
  genValIn_eq ht hz (le_wchart_chartAt hL φ y) hj

theorem valAt'_sec (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε)) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ}
    (hz : IsLift u φ y z) {j : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) :
    valAt' y (L.wchart φ j) (s.f j) = secVal u hL s y z * frameProd u ε z j := by
  rw [secVal_eq hL s hz hj, secValIn, div_mul_cancel₀ _ (frameProd_ne_zero hz ε hj)]

theorem valAt'_gen (hL : L.IsLB) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ}
    (hz : IsLift u φ y z) {j : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) :
    valAt' y (L.wchart φ j) (t.s j).val = genVal u hL t y z * frameProd u ε z j :=
  valAt'_sec hL (genSec t ht) hz hj

theorem genVal_ne_zero (hL : L.IsLB) (t : LB.Gen (LB.LinComb L φ ε)) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ}
    (hz : IsLift u φ y z) : genVal u hL t y z ≠ 0 :=
  div_ne_zero (val_unit_ne_zero y valueRules (le_wchart_chartAt hL φ y) _)
    (frameProd_ne_zero hz ε (le_wchart_chartAt hL φ y))

theorem genVal_mul (hL : L.IsLB) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (y : Sp ℂ ⟶ Y)
    (z : K ⊕ K' → Fin g → ℂ) : genVal u hL (LB.mulGen L φ ε φ' ε' t t') y z =
      genVal u hL t y (fun k => z (.inl k)) * genVal u hL t' y (fun k => z (.inr k)) := by
  have h := le_wchart_chartAt hL (Sum.elim φ φ') y
  simp only [genVal, genValIn, frameProd]
  rw [div_mul_div_comm, Fintype.prod_sum_type]
  refine congrArg₂ (· / ·) ?_ rfl
  exact (val_unit_mul y valueRules h _ _).trans
    (congrArg₂ (· * ·) (val_res y valueRules _ h _) (val_res y valueRules _ h _))

theorem genVal_inv (hL : L.IsLB) (t : LB.Gen (LB.LinComb L φ ε)) (y : Sp ℂ ⟶ Y) (z : K → Fin g → ℂ) :
    genVal u hL (LB.invGen L φ ε t) y z = (genVal u hL t y z)⁻¹ := by
  obtain ⟨e, he⟩ := (valueRules Y y).2.1 _ (le_wchart_chartAt hL φ y)
  simp only [genVal, genValIn, frameProd, zpow_neg, Finset.prod_inv_distrib]
  refine Eq.trans ?_ ((inv_div_inv _ _).trans (inv_div _ _).symm)
  exact congrArg₂ (· / ·) ((he _).trans ((map_units_inv e _).trans (congrArg (·⁻¹) (he _).symm))) rfl

theorem genVal_pull (hL : L.IsLB) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (y : Sp ℂ ⟶ Y') (z : K → Fin g → ℂ) :
    genVal u hL (LB.pullGen L φ ε t h) y z = genVal u hL t (y ≫ h) z := by
  have e : (fun k => chartAt hL ((y ≫ h) ≫ φ k)) = fun k => chartAt hL (y ≫ h ≫ φ k) :=
    funext fun k => by rw [Category.assoc]
  rw [genVal, genVal, e]
  refine congrArg₂ (· / ·) ?_ rfl
  exact (val_res y valueRules _ (le_wchart_chartAt hL (fun k => h ≫ φ k) y) _).trans (val_pullU y valueRules h _ _)

theorem genVal_one (hL : L.IsLB) (y : Sp ℂ ⟶ Y) (z : PEmpty → Fin g → ℂ) : genVal u hL (LB.oneGen L) y z = 1 := by
  obtain ⟨e, he⟩ := (valueRules Y y).2.1 _ (le_wchart_chartAt hL (PEmpty.elim : PEmpty → (Y ⟶ A.left)) y)
  simp only [genVal, genValIn, frameProd, Fintype.prod_empty, div_one]
  exact (he _).trans (map_one e)

theorem genVal_corr (hL : L.IsLB) {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} {z' : K' → Fin g → ℂ}
    (hz : IsLift u φ y z) (hz' : IsLift u φ' y z')
    (hs : ∀ f : (Fin g → ℂ) → ℂˣ, ∏ k, f (z k) ^ ε k = ∏ k, f (z' k) ^ ε' k) :
    genVal u hL t y z = genVal u hL t' y z' := by
  have h₁ := le_wchart_chartAt hL φ y
  have h₂ := le_wchart_chartAt hL φ' y
  have h₃ := (le_preimage_inf y _ _).2 ⟨h₁, h₂⟩
  refine congrArg₂ (· / ·) ?_ ?_
  · refine (val_res y valueRules inf_le_left h₃ _).symm.trans (Eq.trans ?_ (val_res y valueRules inf_le_right h₃ _))
    exact congrArg (fun q : Γ(Y, _)ˣ => valAt' y _ q.val) (h _ _ (fun a b e => congrArg (fun q => chartAt hL (y ≫ q)) e)
      (fun a b e => congrArg (fun q => chartAt hL (y ≫ q)) e) (fun a b e => congrArg (fun q => chartAt hL (y ≫ q)) e))
  · have := congrArg (Units.coeHom ℂ) (hs fun w => Units.mk0 _ (u.fr_ne _ w (le_chartAt hL (u.ex w).left)))
    simp only [map_prod, map_zpow, Units.coeHom_apply, Units.val_mk0] at this
    simp only [frameProd, hz _, hz' _]
    exact this

theorem differentiable_secVal (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε)) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (p : A.left ⟶ Y) {q : E → Fin g → ℂ} (hq : Differentiable ℂ q) {z : E → K → Fin g → ℂ}
    (hd : ∀ k, Differentiable ℂ fun w => z w k) (hz : ∀ w, IsLift u φ ((u.ex (q w)).left ≫ p) (z w)) :
    Differentiable ℂ fun w => secVal u hL s ((u.ex (q w)).left ≫ p) (z w) := by
  intro w₀
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ ((u.ex (q w₀)).left ≫ p) ⁻¹ᵁ L.wchart φ j := ⟨_, le_wchart_chartAt hL φ _⟩
  obtain ⟨ho, hh⟩ := u.hol (p ⁻¹ᵁ L.wchart φ j) ((p.app _).hom (s.f j))
  have ho' : IsOpen {w | ⊤ ≤ ((u.ex (q w)).left ≫ p) ⁻¹ᵁ L.wchart φ j} := ho.preimage hq.continuous
  have hn := ho'.mem_nhds hj
  have d₁ : DifferentiableAt ℂ (fun w => valAt' ((u.ex (q w)).left ≫ p) (L.wchart φ j) (s.f j)) w₀ := by
    have := (hh.differentiableAt (ho.mem_nhds hj)).comp w₀ (hq w₀)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    exact ((valueRules _ (u.ex (q w)).left).2.2.2.1 _ p _ _).symm
  have d₂ : DifferentiableAt ℂ (fun w => frameProd u ε (z w) j) w₀ := by
    have a : ∀ k, DifferentiableAt ℂ (fun w => u.fr (j k) (z w k) ^ ε k) w₀ := fun k => by
      have hk := ((hz w₀).le_iff j).1 hj k
      refine DifferentiableAt.zpow ?_ (Or.inl (u.fr_ne _ _ hk))
      exact ((u.fr_hol (j k)).differentiableAt ((u.hol _ 0).1.mem_nhds hk)).comp w₀ (hd k w₀)
    classical
    exact (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (a k).hasFDerivAt).differentiableAt
  refine (d₁.fun_mul (d₂.fun_inv (frameProd_ne_zero (hz w₀) ε hj))).congr_of_eventuallyEq ?_
  filter_upwards [hn] with w hw
  exact (secVal_eq hL s (hz w) hw).trans (div_eq_mul_inv _ _)

theorem differentiable_genVal (hL : L.IsLB) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (p : A.left ⟶ Y) {q : E → Fin g → ℂ} (hq : Differentiable ℂ q)
    {z : E → K → Fin g → ℂ} (hd : ∀ k, Differentiable ℂ fun w => z w k)
    (hz : ∀ w, IsLift u φ ((u.ex (q w)).left ≫ p) (z w)) :
    Differentiable ℂ fun w => genVal u hL t ((u.ex (q w)).left ≫ p) (z w) :=
  differentiable_secVal hL (genSec t ht) p hq hd hz

def ahFactor (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (l : u.Λ) (z : Fin g → ℂ) : ℂ :=
  χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)

variable {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem chi_ne_zero (h : u.IsAH Hm χ) (l : u.Λ) : χ l ≠ 0 := fun h0 => by simpa [h0] using h.2.2.1 l

theorem ahFactor_ne_zero (h : u.IsAH Hm χ) (l : u.Λ) (z : Fin g → ℂ) : ahFactor Hm χ l z ≠ 0 :=
  mul_ne_zero (chi_ne_zero h l) (Complex.exp_ne_zero _)

theorem frameProd_add_period (h : u.IsAH Hm χ) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} (hz : IsLift u φ y z) (ε : K → ℤ)
    (l : K → u.Λ) {j : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) :
    frameProd u ε z j = (∏ k, ahFactor Hm χ (l k) (z k) ^ ε k) * frameProd u ε (fun k => z k + l k) j := by
  rw [frameProd, frameProd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h.2.2.2 (l k) (j k) (z k) ((hz.le_iff j).1 hj k), mul_zpow]
  rfl

theorem secVal_add_period (hL : L.IsLB) (h : u.IsAH Hm χ) (s : LB.Sec (LB.LinComb L φ ε)) {y : Sp ℂ ⟶ Y}
    {z : K → Fin g → ℂ} (hz : IsLift u φ y z) (l : K → u.Λ) :
    secVal u hL s y (fun k => z k + l k) = (∏ k, ahFactor Hm χ (l k) (z k) ^ ε k) * secVal u hL s y z := by
  have n : (∏ k, ahFactor Hm χ (l k) (z k) ^ ε k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (ahFactor_ne_zero h _ _)
  rw [secVal, secVal, secValIn, secValIn, frameProd_add_period h hz ε l (le_wchart_chartAt hL φ y),
    ← mul_div_assoc, mul_div_mul_left _ _ n]

theorem genVal_add_period (hL : L.IsLB) (h : u.IsAH Hm χ) (t : LB.Gen (LB.LinComb L φ ε)) {y : Sp ℂ ⟶ Y}
    {z : K → Fin g → ℂ} (hz : IsLift u φ y z) (l : K → u.Λ) :
    genVal u hL t y (fun k => z k + l k) = (∏ k, ahFactor Hm χ (l k) (z k) ^ ε k) * genVal u hL t y z := by
  have n : (∏ k, ahFactor Hm χ (l k) (z k) ^ ε k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (ahFactor_ne_zero h _ _)
  rw [genVal, genVal, genValIn, genValIn, frameProd_add_period h hz ε l (le_wchart_chartAt hL φ y),
    ← mul_div_assoc, mul_div_mul_left _ _ n]

theorem genVal_rig (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hr : u.IsRig rig) :
    genVal u hL rig (𝟙 (Sp ℂ)) (fun _ => 0) = 1 := by
  have h := le_wchart_chartAt hL (fun _ : PUnit => eSec A) (𝟙 (Sp ℂ))
  have hz : IsLift u (fun _ : PUnit => eSec A) (𝟙 (Sp ℂ)) (fun _ => 0) := fun _ => by
    rw [ex_zero, Hom.one_def]; simp [eSec]
  refine (div_eq_one_iff_eq (frameProd_ne_zero hz _ h)).2 ?_
  rw [frameProd, Fintype.prod_unique, zpow_one]
  exact (hr _ h).symm

end Calculus

section Main

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem const_of_norm_periodic (u : HolUnif A L g) {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (hp : ∀ (l : u.Λ) z, ‖F (z + l)‖ = ‖F z‖) (z w : Fin g → ℂ) : F z = F w := by
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have hc := (IsZLattice.isCompact_range_of_periodic u.Λ (fun z => ‖F z‖) hF.continuous.norm
    (fun z l hl => hp ⟨l, hl⟩ z)).isBounded
  obtain ⟨C, hC⟩ := hc.exists_norm_le
  refine hF.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩) z w
  rintro _ ⟨x, rfl⟩
  simpa using hC _ ⟨x, rfl⟩

theorem hermForm_zero_left (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by simp [hermForm]

theorem hermForm_zero_right (w : Fin g → ℂ) : hermForm Hm w 0 = 0 := by simp [hermForm]

theorem hermForm_neg_left (z w : Fin g → ℂ) : hermForm Hm (-z) w = -hermForm Hm z w := by simp [hermForm]

theorem hermForm_neg_right (z w : Fin g → ℂ) : hermForm Hm z (-w) = -hermForm Hm z w := by
  simp [hermForm, Matrix.mulVec_neg]

theorem ahFactor_add (hL : L.IsLB) (h : u.IsAH Hm χ) (l m : u.Λ) (z : Fin g → ℂ) :
    ahFactor Hm χ (l + m) z = ahFactor Hm χ l z * ahFactor Hm χ m (z + l) := by
  have hi := le_chartAt hL (u.ex z).left
  set i := chartAt hL (u.ex z).left
  have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rw [ex_add_period u _ _ l.2]; exact hi
  have hi'' : ⊤ ≤ (u.ex (z + (l + m : u.Λ))).left ⁻¹ᵁ L.U i := by rw [ex_add_period u _ _ (l + m).2]; exact hi
  have e := (h.2.2.2 (l + m) i z hi).symm.trans (h.2.2.2 l i z hi)
  rw [h.2.2.2 m i _ hi', add_assoc z, ← Submodule.coe_add, ← _root_.mul_assoc] at e
  exact mul_right_cancel₀ (u.fr_ne i _ hi'') e

theorem chi_add (hL : L.IsLB) (h : u.IsAH Hm χ) (l m : u.Λ) :
    χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im) := by
  have e := ahFactor_add hL h l m 0
  have e' := Complex.sub_conj (hermForm Hm l m)
  rw [← hermForm_conj Hm h.1] at e'
  push_cast at e'
  simp only [ahFactor, hermForm_zero_left, zero_add, mul_zero, Submodule.coe_add, hermForm_add_left,
    hermForm_add_right] at e
  refine mul_right_cancel₀ (Complex.exp_ne_zero _) (e.trans ?_)
  rw [_root_.mul_mul_mul_comm, ← Complex.exp_add, _root_.mul_assoc (χ l * χ m), ← Complex.exp_add]
  congr 2
  linear_combination (Real.pi / 2 : ℂ) * e'

theorem chi_zero (hL : L.IsLB) (h : u.IsAH Hm χ) : χ 0 = 1 := by
  have e := chi_add hL h 0 0
  simp only [add_zero, Submodule.coe_zero, hermForm_zero_left, Complex.zero_im, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, _root_.mul_one] at e
  exact mul_left_cancel₀ (chi_ne_zero h 0) (e.symm.trans (_root_.mul_one _).symm)

theorem ahFactor_zero (hL : L.IsLB) (h : u.IsAH Hm χ) (z : Fin g → ℂ) : ahFactor Hm χ 0 z = 1 := by
  simp [ahFactor, chi_zero hL h, hermForm_zero_right]

theorem exists_int_im (hL : L.IsLB) (h : u.IsAH Hm χ) (l m : u.Λ) : ∃ n : ℤ, (n : ℝ) = (hermForm Hm l m).im := by
  have e := (chi_add hL h l m).symm.trans ((congrArg χ (add_comm l m)).trans (chi_add hL h m l))
  rw [mul_comm (χ m), hermForm_conj Hm h.1 l m, Complex.conj_im] at e
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1
    (mul_left_cancel₀ (mul_ne_zero (chi_ne_zero h l) (chi_ne_zero h m)) e)
  refine ⟨n, ?_⟩
  have : ((n : ℝ) : ℂ) = ((hermForm Hm l m).im : ℂ) := by
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    push_cast at hn ⊢
    linear_combination -hn
  exact_mod_cast this

theorem prod_thK {U : Type} [DivisionCommMonoid U] (f : Finset (Fin 3) → U) :
    ∏ I : thK, f I.down ^ thε I =
      f {0, 1, 2} * (f {0, 1})⁻¹ * (f {0, 2})⁻¹ * (f {1, 2})⁻¹ * f {0} * f {1} * f {2} * (f ∅)⁻¹ := by
  refine (Fintype.prod_equiv (Equiv.ulift : thK ≃ Finset (Fin 3)) _
    (fun I => f I ^ ((-1 : ℤ) ^ (3 - I.card))) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  have q₀ : (-1 : ℤ) ^ (3 - (∅ : Finset (Fin 3)).card) = -1 := by decide
  have q₁ : ∀ i : Fin 3, (-1 : ℤ) ^ (3 - ({i} : Finset (Fin 3)).card) = 1 := by decide
  have q₄ : (-1 : ℤ) ^ (3 - ({0, 1} : Finset (Fin 3)).card) = -1 := by decide
  have q₅ : (-1 : ℤ) ^ (3 - ({0, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₆ : (-1 : ℤ) ^ (3 - ({1, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₇ : (-1 : ℤ) ^ (3 - ({0, 1, 2} : Finset (Fin 3)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₁, q₄, q₅, q₆, q₇]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem sum_three {M : Type} [AddCommMonoid M] (x : Fin 3 → M) :
    ∑ a ∈ ({0, 1, 2} : Finset (Fin 3)), x a = x 0 + x 1 + x 2 ∧ ∑ a ∈ ({0, 1} : Finset (Fin 3)), x a = x 0 + x 1 ∧
      ∑ a ∈ ({0, 2} : Finset (Fin 3)), x a = x 0 + x 2 ∧ ∑ a ∈ ({1, 2} : Finset (Fin 3)), x a = x 1 + x 2 :=
  ⟨by rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide), add_assoc], Finset.sum_pair (by decide),
    Finset.sum_pair (by decide), Finset.sum_pair (by decide)⟩

def cubeLift (x : Fin 3 → Fin g → ℂ) : thK → Fin g → ℂ := fun I => ∑ a ∈ I.down, x a

theorem isLift_cube (u : HolUnif A L g) (x : Fin 3 → Fin g → ℂ) :
    IsLift u (thφ A (x3 A)) (pt3 u x).left (cubeLift x) := fun I => tripleProductPoint_comp_partialSum u x I.down

theorem genVal_cube_of_face (hL : L.IsLB) (h : u.IsAH Hm χ) (t : LB.Gen (LB.LinComb L (thφ A (x3 A)) thε)) (ht : t.IsGen)
    (hf : LB.Gen.Corr L _ _ (Y := (G2 A).left) _ _ (LB.pullGen L (thφ A (x3 A)) thε t (faceMap A 0).left) (LB.oneGen L))
    (x : Fin 3 → Fin g → ℂ) : genVal u hL t (pt3 u x).left (cubeLift x) = 1 := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = ![a, b, c] := ⟨x 0, x 1, x 2, by ext i : 1; fin_cases i <;> rfl⟩
  let p : A ⟶ G3 A := lift (𝟙 A) (lift (toUnit A ≫ u.ex b) (toUnit A ≫ u.ex c))
  have hp : ∀ w, (u.ex w).left ≫ p.left = (pt3 u ![w, b, c]).left := fun w => by
    rw [← Over.comp_left]
    congr 1
    simp [p, pt3, comp_lift, Subsingleton.elim (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _)]
  have hd : Differentiable ℂ fun w => genVal u hL t (pt3 u ![w, b, c]).left (cubeLift ![w, b, c]) := by
    have := differentiable_genVal hL ht p.left (q := id) differentiable_id (z := fun w => cubeLift ![w, b, c])
      (fun I => Differentiable.fun_sum fun k _ => by fin_cases k <;> simp <;> fun_prop)
      (fun w => by rw [id, hp]; exact isLift_cube u _)
    simpa only [id, hp] using this
  have hper : ∀ w, ∀ l ∈ (u.Λ : Set (Fin g → ℂ)), genVal u hL t (pt3 u ![w + l, b, c]).left (cubeLift ![w + l, b, c]) =
      genVal u hL t (pt3 u ![w, b, c]).left (cubeLift ![w, b, c]) := fun w l hl => by
    have e₁ : pt3 u ![w + l, b, c] = pt3 u ![w, b, c] := by simp [pt3, ex_add_period u w l hl]
    have e₂ : cubeLift ![w + l, b, c] = fun I => cubeLift ![w, b, c] I +
        ((∑ a ∈ I.down, (![⟨l, hl⟩, 0, 0] : Fin 3 → u.Λ) a : u.Λ) : Fin g → ℂ) := by
      funext I
      rw [cubeLift, cubeLift, Submodule.coe_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by fin_cases k <;> simp
    rw [e₁, e₂, genVal_add_period hL h t (isLift_cube u _)]
    refine (congrArg (· * _) ?_).trans (_root_.one_mul _)
    refine (prod_thK fun I => ahFactor Hm χ (∑ a ∈ I, (![⟨l, hl⟩, 0, 0] : Fin 3 → u.Λ) a) (∑ a ∈ I, ![w, b, c] a)).trans ?_
    have n := chi_ne_zero h ⟨l, hl⟩
    simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val, add_zero, ahFactor_zero hL h]
    simp only [ahFactor, hermForm_add_left, mul_add, Complex.exp_add]
    field_simp
  rw [entire_apply_eq_of_periodic_of_span_real hd u.full hper a 0]
  have e : (pt3 u ![0, b, c]).left = (lift (u.ex b) (u.ex c)).left ≫ (faceMap A 0).left := by
    rw [← Over.comp_left]
    congr 1
    simp [faceMap, pt3, comp_lift, x2, pzero, ex_zero, Hom.one_def]
  have hz := isLift_cube u ![0, b, c]
  rw [e] at hz ⊢
  rw [← genVal_pull, ← genVal_one (u := u) hL (lift (u.ex b) (u.ex c)).left PEmpty.elim]
  refine genVal_corr hL hf (fun k => (Category.assoc _ _ _).symm.trans (hz k)) (fun k => k.elim) fun f => ?_
  refine (prod_thK fun I => f (∑ a ∈ I, ![0, b, c] a)).trans ?_
  simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val, zero_add, Fintype.prod_empty]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem isLift_sym (u : HolUnif A L g) (z : Fin g → ℂ) :
    IsLift u (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] (u.ex z).left ![-z, z] := fun k => by
  fin_cases k
  exacts [ex_neg_left u z, Category.comp_id _]

theorem genVal_sym (hL : L.IsLB) (h : u.IsAH Hm χ)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])) (hs : s.IsGen)
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec A)) (LB.oneGen L)) :
    (∀ z, genVal u hL s (u.ex z).left ![-z, z] = 1) ∧ ∀ l, χ (-l) = χ l := by
  have hd : Differentiable ℂ fun w => genVal u hL s (u.ex w).left ![-w, w] := by
    have := differentiable_genVal hL hs (𝟙 _) (q := id) differentiable_id (z := fun w => ![-w, w])
      (fun k => by fin_cases k <;> simp <;> fun_prop) (fun w => by rw [id, Category.comp_id]; exact isLift_sym u w)
    simpa only [id, Category.comp_id] using this
  have hper : ∀ (l : u.Λ) w, genVal u hL s (u.ex (w + l)).left ![-(w + l), w + l] =
      χ (-l) / χ l * genVal u hL s (u.ex w).left ![-w, w] := fun l w => by
    have e₂ : ![-(w + l), w + l] = fun k => ![-w, w] k + ((![-l, l] : Fin 2 → u.Λ) k : Fin g → ℂ) := by
      funext k
      fin_cases k <;> simp [add_comm]
    rw [ex_add_period u w l l.2, e₂, genVal_add_period hL h s (isLift_sym u w)]
    congr 1
    have n := chi_ne_zero h l
    simp [ahFactor, hermForm_neg_left, hermForm_neg_right]
    field_simp
  have hc := const_of_norm_periodic u hd (fun l w => by
    rw [hper, norm_mul, norm_div, h.2.2.1, h.2.2.1, div_one, _root_.one_mul])
  have e : (u.ex 0).left = 𝟙 (Sp ℂ) ≫ eSec A := by rw [ex_zero, Hom.one_def]; simp [eSec]
  have h1 : genVal u hL s (u.ex 0).left ![-0, 0] = 1 := by
    have hz := isLift_sym u 0
    rw [e] at hz ⊢
    rw [← genVal_pull, ← genVal_one (u := u) hL (𝟙 (Sp ℂ)) PEmpty.elim]
    refine genVal_corr hL h₀ (fun k => (Category.assoc _ _ _).symm.trans (hz k)) (fun k => k.elim) fun f => ?_
    simp
  refine ⟨fun z => (hc z 0).trans h1, fun l => ?_⟩
  have := hper l 0
  rw [hc _ 0, h1, _root_.mul_one] at this
  exact (div_eq_one_iff_eq (chi_ne_zero h l)).1 this.symm

variable [IsCommMonObj A] {f f' : A ⟶ A} {F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}

omit [IsCommMonObj A] in

theorem lift_mem (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) (l : u.Λ) : F l ∈ u.Λ := by
  rw [← u.ker, hF, (u.ker l).2 l.2, ← ex_zero u, ← hF, map_zero]

def rosatiLift (F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (x z : Fin g → ℂ) : Fin 6 → Fin g → ℂ :=
  ![F x + z, F x, z, x + G z, x, G z]

theorem isLift_rosati (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) (hG : ∀ z, u.ex (G z) = u.ex z ≫ f') (x z : Fin g → ℂ) :
    IsLift u (Out.rosatiφ A f f') (lift (u.ex x) (u.ex z)).left (rosatiLift F G x z) := fun k => by
  have e : ∀ (q : A ⊗ A ⟶ A) w, lift (u.ex x) (u.ex z) ≫ q = u.ex w →
      (lift (u.ex x) (u.ex z)).left ≫ q.left = (u.ex w).left := fun q w hq => congrArg (fun m => m.left) hq
  fin_cases k
  · exact e _ (F x + z) ((MonObj.comp_mul _ _ _).trans (by simp [u.ex_add, hF]))
  · exact e _ (F x) (by simp [hF])
  · exact e _ z (by simp)
  · exact e _ (x + G z) ((MonObj.comp_mul _ _ _).trans (by simp [u.ex_add, hG]))
  · exact e _ x (by simp)
  · exact e _ (G z) (by simp [hG])

theorem genVal_rosati (hL : L.IsLB) (h : u.IsAH Hm χ) (hF : ∀ z, u.ex (F z) = u.ex z ≫ f)
    (hG : ∀ z, u.ex (G z) = u.ex z ≫ f') (r : LB.Gen (LB.LinComb L (Out.rosatiφ A f f') Out.rosatiε)) (hr : r.IsGen)
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ r (Out.zero2 A)) (LB.oneGen L)) :
    (∀ x z, hermForm Hm (F x) z = hermForm Hm x (G z)) ∧
      ∀ x z, genVal u hL r (lift (u.ex x) (u.ex z)).left (rosatiLift F G x z) = 1 := by
  obtain ⟨V, hV⟩ : ∃ V : (Fin g → ℂ) → (Fin g → ℂ) → ℂ,
      ∀ x z, V x z = genVal u hL r (lift (u.ex x) (u.ex z)).left (rosatiLift F G x z) := ⟨_, fun _ _ => rfl⟩
  have dF : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have dG : Differentiable ℂ G := (LinearMap.toContinuousLinearMap G).differentiable
  have d₁ : ∀ z, Differentiable ℂ fun x => V x z := fun z => by
    have hp : ∀ w, (u.ex w).left ≫ (lift (𝟙 A) (toUnit A ≫ u.ex z)).left = (lift (u.ex w) (u.ex z)).left := fun w => by
      rw [← Over.comp_left]
      congr 1
      simp [comp_lift, Subsingleton.elim (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _)]
    have := differentiable_genVal hL hr _ (q := id) differentiable_id (z := fun w => rosatiLift F G w z)
      (fun k => by fin_cases k <;> simp [rosatiLift] <;> fun_prop)
      (fun w => by rw [id, hp]; exact isLift_rosati hF hG w z)
    simpa only [id, hp, hV] using this
  have d₂ : ∀ x, Differentiable ℂ fun z => V x z := fun x => by
    have hp : ∀ w, (u.ex w).left ≫ (lift (toUnit A ≫ u.ex x) (𝟙 A)).left = (lift (u.ex x) (u.ex w)).left := fun w => by
      rw [← Over.comp_left]
      congr 1
      simp [comp_lift, Subsingleton.elim (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _)]
    have := differentiable_genVal hL hr _ (q := id) differentiable_id (z := fun w => rosatiLift F G x w)
      (fun k => by fin_cases k <;> simp [rosatiLift] <;> fun_prop)
      (fun w => by rw [id, hp]; exact isLift_rosati hF hG x w)
    simpa only [id, hp, hV] using this
  have p₁ : ∀ (l : u.Λ) x z, V (x + l) z =
      Complex.exp (Real.pi * (hermForm Hm z (F l) - hermForm Hm (G z) l)) * V x z := fun l x z => by
    have e₂ : rosatiLift F G (x + l) z = fun k => rosatiLift F G x z k +
        ((![⟨F l, lift_mem hF l⟩, ⟨F l, lift_mem hF l⟩, 0, l, l, 0] : Fin 6 → u.Λ) k : Fin g → ℂ) := by
      funext k
      fin_cases k <;> simp [rosatiLift] <;> abel
    rw [hV, hV, ex_add_period u x l l.2, e₂, genVal_add_period hL h r (isLift_rosati hF hG x z)]
    congr 1
    have n := chi_ne_zero h l
    have n' := chi_ne_zero h ⟨F l, lift_mem hF l⟩
    simp only [Fin.prod_univ_six, rosatiLift, Out.rosatiε, Matrix.cons_val, ahFactor_zero hL h, zpow_neg, zpow_one]
    simp only [ahFactor, hermForm_add_left, mul_add, mul_sub, Complex.exp_add, Complex.exp_sub]
    field_simp
  have p₂ : ∀ (l : u.Λ) x z, V x (z + l) =
      Complex.exp (Real.pi * (hermForm Hm (F x) l - hermForm Hm x (G l))) * V x z := fun l x z => by
    have e₂ : rosatiLift F G x (z + l) = fun k => rosatiLift F G x z k +
        ((![l, 0, l, ⟨G l, lift_mem hG l⟩, 0, ⟨G l, lift_mem hG l⟩] : Fin 6 → u.Λ) k : Fin g → ℂ) := by
      funext k
      fin_cases k <;> simp [rosatiLift] <;> abel
    rw [hV, hV, ex_add_period u z l l.2, e₂, genVal_add_period hL h r (isLift_rosati hF hG x z)]
    congr 1
    have n := chi_ne_zero h l
    have n' := chi_ne_zero h ⟨G l, lift_mem hG l⟩
    simp only [Fin.prod_univ_six, rosatiLift, Out.rosatiε, Matrix.cons_val, ahFactor_zero hL h, zpow_neg, zpow_one]
    simp only [ahFactor, hermForm_add_left, mul_add, mul_sub, Complex.exp_add, Complex.exp_sub]
    field_simp
  have ne : ∀ x z, V x z ≠ 0 := fun x z => (hV x z).symm ▸ genVal_ne_zero hL r (isLift_rosati hF hG x z)

  obtain ⟨B, hB⟩ : ∃ B : (Fin g → ℂ) → (Fin g → ℂ) → ℂ, ∀ x z, B x z = hermForm Hm (F x) z - hermForm Hm x (G z) :=
    ⟨_, fun _ _ => rfl⟩
  have Bc : ∀ x z, hermForm Hm z (F x) - hermForm Hm (G z) x = starRingEnd ℂ (B x z) := fun x z => by
    rw [hB, map_sub, ← hermForm_conj Hm h.1, ← hermForm_conj Hm h.1]
  have Ba : ∀ x y z, B (x + y) z = B x z + B y z := fun x y z => by
    simp only [hB, map_add, hermForm_add_left]; ring
  have Bs : ∀ (c : ℂ) x z, B (c • x) z = c * B x z := fun c x z => by
    simp only [hB, map_smul, hermForm_smul_left]; ring
  have Bs' : ∀ (c : ℂ) x z, B x (c • z) = starRingEnd ℂ c * B x z := fun c x z => by
    simp only [hB, map_smul, hermForm_smul_right]; ring
  have Bd : ∀ z, Differentiable ℂ fun x => B x z := fun z => by
    simp only [hB, hermForm, dotProduct]
    fun_prop
  have k₁ : ∀ (l : u.Λ) z, Complex.exp (Real.pi * starRingEnd ℂ (B l z)) = Complex.exp (Real.pi * B l z) := fun l z => by
    have hc := const_of_norm_periodic u (F := fun x => V x z * Complex.exp (-(Real.pi * B x z)))
      ((d₁ z).mul (((Bd z).const_mul _).neg.cexp)) (fun m x => by
        simp only [p₁, Bc, Ba, norm_mul, Complex.norm_exp]
        rw [mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
        congr 2
        simp
        ring) (0 + l) 0
    have B0 : B 0 z = 0 := by simpa using Bs 0 0 z
    simp only [p₁] at hc
    simp only [Bc, B0, zero_add, mul_zero, neg_zero, Complex.exp_zero, _root_.mul_one, Complex.exp_neg] at hc
    have n := ne 0 z
    have n' := Complex.exp_ne_zero (Real.pi * B l z)
    field_simp at hc
    exact hc
  have k₂ : ∀ (l : u.Λ) z, (B l z).im = 0 := fun l z => by
    by_contra hne
    have := k₁ l ((((2 * (B l z).im)⁻¹ : ℝ) : ℂ) • z)
    rw [Bs', Complex.conj_ofReal] at this
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 this
    have hi := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.add_im, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, add_zero, sub_zero, _root_.mul_one] at hi
    have hpi := Real.pi_ne_zero
    field_simp at hi
    have : (2 * n + 1 : ℤ) = 0 := by
      have : (2 * n + 1 : ℝ) = 0 := by linarith
      exact_mod_cast this
    omega
  have k₃ : ∀ (l : u.Λ) z, B l z = 0 := fun l z => by
    have := k₂ l (Complex.I • z)
    rw [Bs'] at this
    exact Complex.ext (by simpa using this) (k₂ l z)
  have k₄ : ∀ x z, B x z = 0 := fun x z => by
    have hx : x ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) := by rw [u.full]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact k₃ ⟨y, hy⟩ z
    | zero => simpa using Bs 0 0 z
    | add a b _ _ ha hb => rw [Ba, ha, hb, add_zero]
    | smul c a _ ha => rw [← Complex.coe_smul, Bs, ha, mul_zero]
  have c₁ : ∀ x z, V x z = V 0 z := fun x z => entire_apply_eq_of_periodic_of_span_real (d₁ z) u.full
    (fun w l hl => by simpa [Bc, k₄] using p₁ ⟨l, hl⟩ w z) x 0
  have c₂ : ∀ x z, V x z = V x 0 := fun x z => entire_apply_eq_of_periodic_of_span_real (d₂ x) u.full
    (fun w l hl => by simpa [← hB, k₄] using p₂ ⟨l, hl⟩ x w) z 0
  refine ⟨fun x z => sub_eq_zero.1 ((hB x z).symm.trans (k₄ x z)), fun x z => ?_⟩
  rw [← hV, c₁, c₂, hV]
  have e : (lift (u.ex 0) (u.ex 0)).left = 𝟙 (Sp ℂ) ≫ Out.zero2 A := by rw [ex_zero, Hom.one_def]; simp
  have hz := isLift_rosati hF hG 0 0
  rw [e] at hz ⊢
  rw [← genVal_pull, ← genVal_one (u := u) hL (𝟙 (Sp ℂ)) PEmpty.elim]
  refine genVal_corr hL h₀ (fun k => (Category.assoc _ _ _).symm.trans (hz k)) (fun k => k.elim) fun f => ?_
  simp [Fin.prod_univ_six, rosatiLift, Out.rosatiε]

end Main

end GlobalTheory.FrameValue
