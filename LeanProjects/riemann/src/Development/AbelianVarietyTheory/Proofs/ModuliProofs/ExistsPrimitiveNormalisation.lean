import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PrimNorm

open GlobalTheory.MulPull

section Classes

variable {X Y Z : Scheme.{0}}

def trivialSums (L : LB X) (Y : Scheme.{0}) : Subgroup (Abelianization (FreeGroup (Y ⟶ X))) where
  carrier := {s | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ), HasGen L φ ε ∧
    ∏ k, Abelianization.of (FreeGroup.of (φ k)) ^ ε k = s}
  one_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ⟨LB.oneGen L, fun _ _ => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm⟩,
    Fintype.prod_empty _⟩
  mul_mem' := by
    rintro _ _ ⟨K, _, φ, ε, h, rfl⟩ ⟨K', _, φ', ε', h', rfl⟩
    exact ⟨K ⊕ K', inferInstance, _, _, h.mul h', Fintype.prod_sum_type _⟩
  inv_mem' := by
    rintro _ ⟨K, _, φ, ε, h, rfl⟩
    exact ⟨K, inferInstance, _, _, h.inv, by simp only [zpow_neg, Finset.prod_inv_distrib]⟩

abbrev PullClass (L : LB X) (Y : Scheme.{0}) : Type := Abelianization (FreeGroup (Y ⟶ X)) ⧸ trivialSums L Y

def cls (L : LB X) (ψ : Y ⟶ X) : PullClass L Y := QuotientGroup.mk' _ (Abelianization.of (FreeGroup.of ψ))

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem hasGen_iff (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    HasGen L φ ε ↔ ∏ k, cls L (φ k) ^ ε k = 1 := by
  have e : ∏ k, cls L (φ k) ^ ε k =
      QuotientGroup.mk' (trivialSums L Y) (∏ k, Abelianization.of (FreeGroup.of (φ k)) ^ ε k) := by
    simp only [map_prod, map_zpow, cls]
  rw [e, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨fun h => ⟨K, inferInstance, φ, ε, h, rfl⟩, ?_⟩
  rintro ⟨K', _, φ', ε', h, e⟩
  refine h.of_formEq hL fun U _ f => ?_
  simpa only [map_prod, map_zpow, Abelianization.lift_apply_of, FreeGroup.lift_apply_of] using
    congrArg (Abelianization.lift (FreeGroup.lift f)) e

def chartDivOut (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    ChartPull (LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε))
      (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)) (𝟙 Y) :=
  have le : ∀ p : (K' → L.ι) × (K → L.ι), LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2 ≤
      LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2) := fun p y hy => Set.mem_iInter.2 fun k => by
    rcases k with k | k
    exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
  { idx := fun p => Sum.elim p.1 p.2
    le := le
    g := fun y p q hp hq => by
      refine (gm_div _ _ (𝟙 Y) y p q ⟨hp, hq⟩).trans (Eq.trans ?_
        (gm_linComb L _ _ (𝟙 Y) y _ _ (le p hp) (le q hq)).symm)
      refine (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ' ε' (𝟙 Y) y p.1 q.1 hp.1 hq.1)
        (gm_linComb L φ ε (𝟙 Y) y p.2 q.2 hp.2 hq.2)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rfl }

def chartDivIn (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    ChartPull (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k))
      (LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) (𝟙 Y) :=
  have le : ∀ j : K' ⊕ K → L.ι, LB.wchart L (Sum.elim φ' φ) j ≤
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inr k)⟩
  { idx := fun j => (j ∘ Sum.inl, j ∘ Sum.inr)
    le := le
    g := fun y p q hp hq => by
      refine (gm_linComb L _ _ (𝟙 Y) y p q hp hq).trans (Eq.trans ?_
        (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr)
          ⟨le p hp, le q hq⟩).symm)
      refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ' ε' (𝟙 Y) y _ _ (le p hp).1 (le q hq).1)
        (gm_linComb L φ ε (𝟙 Y) y _ _ (le p hp).2 (le q hq).2)).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rfl }

theorem lbIso_iff (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔ ∏ k, cls L (φ k) ^ ε k = ∏ k, cls L (φ' k) ^ ε' k := by
  have e : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔ HasGen L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k) :=
    ⟨fun ⟨w, hw⟩ => gen_chartPull (chartDivIn L φ ε φ' ε') w hw,
      fun ⟨w, hw⟩ => gen_chartPull (chartDivOut L φ ε φ' ε') w hw⟩
  rw [e, hasGen_iff hL]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_eq_one]
  exact eq_comm

def chartFlat (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ) :
    ChartPull (LB.LinComb (LB.LinComb L φ ε) ψ δ)
      (LB.LinComb L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1)) (𝟙 Z) :=
  have le : ∀ j : K' → K → L.ι, LB.wchart (LB.LinComb L φ ε) ψ j ≤
      LB.wchart L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => j p.1 p.2) := fun j y hy =>
    Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
  { idx := fun j p => j p.1 p.2
    le := le
    g := fun y p q hp hq => by
      refine (gm_linComb (LB.LinComb L φ ε) ψ δ (𝟙 Z) y p q hp hq).trans (Eq.trans ?_
        (gm_linComb L _ _ (𝟙 Z) y _ _ (le p hp) (le q hq)).symm)
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun k _ => ?_
      refine (congrArg (· ^ δ k) (gm_linComb L φ ε (𝟙 Z ≫ ψ k) y (p k) (q k) (Set.mem_iInter.1 hp k)
        (Set.mem_iInter.1 hq k))).trans ?_
      simp only [← Finset.prod_zpow, zpow_mul, Category.assoc] }

theorem prod_flat (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ) :
    ∏ p : K' × K, cls L (ψ p.1 ≫ φ p.2) ^ (ε p.2 * δ p.1) = ∏ k, (∏ l, cls L (ψ k ≫ φ l) ^ ε l) ^ δ k := by
  simp only [Fintype.prod_prod_type, ← Finset.prod_zpow, zpow_mul]

theorem hasGen_nested (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ)
    (h : ∏ k, (∏ l, cls L (ψ k ≫ φ l) ^ ε l) ^ δ k = 1) : HasGen (LB.LinComb L φ ε) ψ δ := by
  obtain ⟨t, ht⟩ := (hasGen_iff hL _ _).2 ((prod_flat φ ε ψ δ).trans h)
  exact gen_chartPull (chartFlat L φ ε ψ δ) t ht

theorem lbIso_nested (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ)
    {K₃ : Type} [Fintype K₃] (χ : K₃ → (Z ⟶ X)) (κ : K₃ → ℤ)
    (h : ∏ k, (∏ l, cls L (ψ k ≫ φ l) ^ ε l) ^ δ k = ∏ k, cls L (χ k) ^ κ k) :
    LBIso (LB.LinComb (LB.LinComb L φ ε) ψ δ) (LB.LinComb L χ κ) :=
  ((lbIso_iff hL _ _ χ κ).2 ((prod_flat φ ε ψ δ).trans h)).chartPull (chartFlat L φ ε ψ δ) (chartPullId _)

end Classes

section Algebra

variable {A U : Type} [CommGroup A] [CommGroup U]

def diff₂ (m : A → U) (x y : A) : U := m (x * y) * (m x)⁻¹ * (m y)⁻¹ * m 1

def diff₃ (m : A → U) (x y z : A) : U :=
  m (x * y * z) * (m (x * y))⁻¹ * (m (x * z))⁻¹ * (m (y * z))⁻¹ * m x * m y * m z * (m 1)⁻¹

variable {m : A → U}

theorem diff₂_comm (x y : A) : diff₂ m x y = diff₂ m y x := by
  rw [diff₂, diff₂, mul_comm x, mul_right_comm (m (y * x))]

theorem diff₂_mul_left_eq (x y z : A) : diff₂ m (x * y) z = diff₃ m x y z * (diff₂ m x z * diff₂ m y z) := by
  apply Additive.ofMul.injective
  simp only [diff₂, diff₃, ofMul_mul, ofMul_inv]
  abel

variable (hc : ∀ x y z, diff₃ m x y z = 1)
include hc

theorem diff₂_mul_left (x y z : A) : diff₂ m (x * y) z = diff₂ m x z * diff₂ m y z := by
  rw [diff₂_mul_left_eq, hc, _root_.one_mul]

theorem diff₂_mul_right (x y z : A) : diff₂ m x (y * z) = diff₂ m x y * diff₂ m x z := by
  rw [diff₂_comm, diff₂_mul_left hc, diff₂_comm y, diff₂_comm z]

theorem diff₂_inv_inv (x y : A) : diff₂ m x⁻¹ y⁻¹ = diff₂ m x y := by
  have o : ∀ z, diff₂ m 1 z = 1 := fun z => mul_eq_left.1 ((diff₂_mul_left hc 1 1 z).symm.trans (by rw [_root_.mul_one]))
  have a := diff₂_mul_left hc x⁻¹ x y⁻¹
  have b := diff₂_mul_right hc x y y⁻¹
  rw [inv_mul_cancel, o] at a
  rw [mul_inv_cancel, diff₂_comm, o] at b
  exact mul_right_cancel (a.symm.trans b)

theorem diff₂_quadratic (w w' : A →* A) (hw : ∀ y, w y * w' y = y)
    (ha : ∀ x y, diff₂ m (w x) y = diff₂ m x (w' y)) (x y : A) :
    diff₂ (fun x => diff₂ m x (w x)) x y = diff₂ m x y := by
  have o : diff₂ m 1 (w 1) = 1 := mul_eq_left.1 ((diff₂_mul_left hc 1 1 _).symm.trans (by rw [_root_.mul_one]))
  have e : diff₂ m x y = diff₂ m x (w y) * diff₂ m y (w x) := by
    rw [diff₂_comm y, ha, ← diff₂_mul_right hc, hw]
  rw [e]
  show diff₂ m (x * y) (w (x * y)) * (diff₂ m x (w x))⁻¹ * (diff₂ m y (w y))⁻¹ * diff₂ m 1 (w 1) = _
  rw [o, map_mul, diff₂_mul_left hc, diff₂_mul_right hc, diff₂_mul_right hc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem diff₃_quadratic (w w' : A →* A) (hw : ∀ y, w y * w' y = y)
    (ha : ∀ x y, diff₂ m (w x) y = diff₂ m x (w' y)) (x y z : A) :
    diff₃ (fun x => diff₂ m x (w x)) x y z = 1 := by
  have e := diff₂_mul_left_eq (m := fun x => diff₂ m x (w x)) x y z
  rw [diff₂_quadratic hc w w' hw ha, diff₂_quadratic hc w w' hw ha, diff₂_quadratic hc w w' hw ha,
    diff₂_mul_left hc] at e
  exact mul_eq_right.1 e.symm

end Algebra

section Group

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

theorem psum_pre {T T' : Over S} (ρ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ B)) (x' : Fin n → (T' ⟶ B))
    (hx : ∀ i, x' i = ρ ≫ x i) (I : Finset (Fin n)) : (psum B x' I).left = ρ.left ≫ (psum B x I).left := by
  obtain rfl : x' = fun i => ρ ≫ x i := funext hx
  exact congrArg (fun q : T' ⟶ B => q.left) (foldr_padd_pre ρ x _)

def chartSquare (L : LB B.left) {T T' : Over S} (ρ : T' ⟶ T) {a b : T ⟶ B} {a' b' : T' ⟶ B} (ha : a' = ρ ≫ a)
    (hb : b' = ρ ≫ b) : ChartPull (cubeLB B ![a', b'] L) (cubeLB B ![a, b] L) ρ.left :=
  chartPullSame L _ _ _ ρ.left fun I => psum_pre ρ ![a, b] ![a', b'] (fun i => by
    fin_cases i
    exacts [ha, hb]) I.down

theorem prod_square {T T' : Over S} (ρ : T' ⟶ T) (x y : T ⟶ B) {U : Type} [CommGroup U] (h : (T'.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (ρ.left ≫ (psum B ![x, y] I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      diff₂ (fun q : T' ⟶ B => h q.left) (ρ ≫ x) (ρ ≫ y) := by
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum B ![ρ ≫ x, ρ ≫ y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    (fun I => congrArg (fun q => h q ^ ((-1 : ℤ) ^ (2 - I.down.card)))
      (psum_pre ρ ![x, y] _ (fun i => by fin_cases i <;> rfl) I.down).symm)).trans ?_
  generalize ρ ≫ x = a
  generalize ρ ≫ y = b
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum B ![a, b] ∅ = 1 := rfl
  have p₁ : psum B ![a, b] {0} = a := _root_.mul_one a
  have p₂ : psum B ![a, b] {1} = b := _root_.mul_one b
  have p₃ : psum B ![a, b] {0, 1} = a * b := congrArg (a * ·) (_root_.mul_one b)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one, diff₂]
  ac_rfl

theorem prod_square_id {T : Over S} (x y : T ⟶ B) {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum B ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      diff₂ (fun q : T ⟶ B => h q.left) x y := by
  have e := prod_square (𝟙 T) x y h
  simpa only [Over.id_left, Category.id_comp] using e

theorem isSymmetric_of_hasGen (P : RigLB B)
    (h : HasGen P.L (K := Fin 2) ![(GrpObj.inv (X := B)).left, 𝟙 _] ![1, -1]) : P.IsSymmetric := by
  obtain ⟨t, ht⟩ := h
  have he : eSec B ≫ (GrpObj.inv (X := B)).left = 𝟙 _ ≫ eSec B := by
    rw [Category.id_comp]
    exact congrArg (fun q => q.left) (show η[B] ≫ GrpObj.inv = η[B] by simp)
  let n : B.left ⟶ B.left := (toUnit B).left ≫ eSec B
  have hn : eSec B ≫ n = eSec B := by
    rw [← Category.assoc, show eSec B ≫ (toUnit B).left = 𝟙 _ from
      congrArg (fun q => q.left) (show η[B] ≫ toUnit B = 𝟙 _ by simp), Category.id_comp]
  obtain ⟨u, hu, hv⟩ := exists_gen P.isLB (K' := Fin 2) (φ' := ![(GrpObj.inv (X := B)).left, 𝟙 _]) (ε' := ![1, -1])
    (fun V _ k => by
      have e : n ≫ (GrpObj.inv (X := B)).left = n := by rw [Category.assoc, he, Category.id_comp]
      simp [Fintype.prod_sum_type, Fin.prod_univ_succ, e])
    (LB.mulGen P.L _ _ _ _ t (LB.invGen P.L _ _ (LB.pullGen P.L _ _ t n)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
  have le : ∀ p : (PUnit → P.L.ι) × P.L.ι, (P.L.pull (GrpObj.inv (X := B)).left).U p.1 ⊓ P.L.U p.2 ≤
      LB.wchart P.L (K := Fin 2) ![(GrpObj.inv (X := B)).left, 𝟙 _] ![p.1 PUnit.unit, p.2] := fun p y hy =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [mem_pull.1 hy.1, hy.2]
  let w : LB.Iso P.L (P.L.pull (GrpObj.inv (X := B)).left) := ⟨fun p => res (le p) (u.s ![p.1 PUnit.unit, p.2])⟩
  have gwv : ∀ (Y : Scheme.{0}) (f : Y ⟶ B.left) (y : Y) (j k : P.L.ι), (GrpObj.inv (X := B)).left (f y) ∈ P.L.U j →
      f y ∈ P.L.U k → gw w f y j k = gm f y _ (u.s ![j, k]) := fun Y f y j k hj hk =>
    gm_res f y (le (fun _ => j, k)) ⟨mem_pull.2 hj, hk⟩ _
  have tr : ∀ (Y : Scheme.{0}) (f : Y ⟶ B.left) (y : Y) (j j' k k' : P.L.ι),
      (GrpObj.inv (X := B)).left (f y) ∈ P.L.U j → (GrpObj.inv (X := B)).left (f y) ∈ P.L.U j' → f y ∈ P.L.U k →
      f y ∈ P.L.U k' → gw w f y j k = gm (f ≫ (GrpObj.inv (X := B)).left) y _ (P.L.g j j') *
        (gm f y _ (P.L.g k k'))⁻¹ * gw w f y j' k' := by
    intro Y f y j j' k k' hj hj' hk hk'
    rw [gwv Y f y j k hj hk, gwv Y f y j' k' hj' hk']
    refine (gen_trans hu f y (le (fun _ => j, k) ⟨mem_pull.2 hj, hk⟩) (le (fun _ => j', k') ⟨mem_pull.2 hj', hk'⟩)).trans
      (congrArg (· * _) ?_)
    rw [trF, Fin.prod_univ_two]
    show gm (f ≫ (GrpObj.inv (X := B)).left) y (P.L.U j ⊓ P.L.U j') (P.L.g j j') ^ (1 : ℤ) *
      gm (f ≫ 𝟙 _) y (P.L.U k ⊓ P.L.U k') (P.L.g k k') ^ (-1 : ℤ) = _
    rw [Category.comp_id, zpow_one, zpow_neg, zpow_one]
  refine ⟨he, w, (isGen_iff w).2 tr, (maps_iff w _ (fun _ : PUnit => eSec B) _ P.rig P.rig (𝟙 _) _
    (rigPull_le _ _ he P.L) (fun _ => rfl)).2 ?_⟩
  intro Z r z p q hp hq
  have hi : (r ≫ eSec B) ≫ (GrpObj.inv (X := B)).left = r ≫ eSec B := by
    rw [Category.assoc, he, Category.id_comp]
  have hq' : (r ≫ eSec B) z ∈ P.L.U (q PUnit.unit) := hq PUnit.unit
  have hp₁ : (GrpObj.inv (X := B)).left ((r ≫ eSec B) z) ∈ P.L.U (p PUnit.unit) := hp PUnit.unit
  have pt : (GrpObj.inv (X := B)).left ((r ≫ eSec B) z) = (r ≫ eSec B) z := congrArg (fun g => g z) hi
  have hq₁ : (GrpObj.inv (X := B)).left ((r ≫ eSec B) z) ∈ P.L.U (q PUnit.unit) := by rw [pt]; exact hq'
  have hp' : (r ≫ eSec B) z ∈ P.L.U (p PUnit.unit) := by rw [← pt]; exact hp₁
  obtain ⟨J, hJ, eJ⟩ := exists_good P.L P.isLB z (fun _ : PUnit => r ≫ eSec B) q (fun _ _ _ => rfl) (fun _ => hq')
  have one : gw w (r ≫ eSec B) z (q PUnit.unit) (q PUnit.unit) = 1 := by
    refine (gwv Z _ z _ _ hq₁ hq').trans ((val_of u (r ≫ eSec B) z J _ (fun k => by
      fin_cases k
      · exact (congrArg J hi).trans (eJ PUnit.unit)
      · exact (congrArg J (Category.comp_id _)).trans (eJ PUnit.unit))).symm.trans ?_)
    rw [hv Z _ z J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, hn, mul_inv_cancel]
  rw [Category.comp_id, Fintype.prod_unique, zpow_one,
    tr Z _ z _ (q PUnit.unit) _ (q PUnit.unit) hp₁ hq₁ hq' hq', one, gm_self P.isLB _ z hq', hi, inv_one,
    _root_.mul_one, _root_.mul_one]
  refine (gen_trans P.rigGen r z (Set.mem_iInter.2 fun _ => hp') (Set.mem_iInter.2 hq)).trans (congrArg (· * _) ?_)
  rw [trF, Fintype.prod_unique, zpow_one]

end Group

section Main

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left}

omit [IsCommMonObj B] in

def postHom (f : B ⟶ B) [IsMonHom f] (T : Over S) : (T ⟶ B) →* (T ⟶ B) :=
  MonoidHom.mk' (· ≫ f) fun x y => MonObj.mul_comp x y f

abbrev ptCls (M : LB B.left) (T : Over S) : (T ⟶ B) → PullClass M T.left := fun q => cls M q.left

theorem diff₃_ptCls (hM : M.IsLB) (h : ∃ t : LB.Gen (Theta B M), t.IsGen) {T : Over S} (x y z : T ⟶ B) :
    diff₃ (ptCls M T) x y z = 1 :=
  (prod_cub x y z (cls M)).symm.trans
    ((hasGen_iff hM _ _).1 (HasGen.pull (φ := thφ B (x3 B)) (ε := thε) h (lift x (lift y z)).left))

theorem diff₂_ptCls_adj (hM : M.IsLB) {f g : B ⟶ B}
    (h : LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M)) {T : Over S} (x y : T ⟶ B) :
    diff₂ (ptCls M T) (x ≫ f) y = diff₂ (ptCls M T) x (y ≫ g) :=
  (prod_square_id _ _ (cls M)).symm.trans (((lbIso_iff hM _ _ _ _).1
    (h.chartPull (chartSquare M (lift x y) (by simp) (by simp)) (chartSquare M (lift x y) (by simp) (by simp)))).trans
    (prod_square_id _ _ (cls M)))

def normCls (M : LB B.left) (w : B ⟶ B) {Y : Scheme.{0}} (ψ : Y ⟶ B.left) : PullClass M Y :=
  ∏ I : ULift.{0} (Finset (Fin 2)), cls M (ψ ≫ (psum B ![𝟙 B, w] I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card))

theorem normCls_left (w : B ⟶ B) {T : Over S} (x : T ⟶ B) : normCls M w x.left = diff₂ (ptCls M T) x (x ≫ w) :=
  (prod_square x (𝟙 B) w (cls M)).trans (by rw [Category.comp_id])

theorem exists_normalised_bundle (hG : Out.GlobalFnsSt) (hB : IsAbelianScheme B) (hM : M.IsLB)
    (hT : ∃ t : LB.Gen (Theta B M), t.IsGen) (w w' : B ⟶ B) [IsMonHom w] [IsMonHom w'] (hw : w * w' = 𝟙 B)
    (ha : LBIso (cubeLB B ![fst B B ≫ w, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ w'] M)) :
    ∃ (P : RigLB B) (_ : CubicalStr B P), P.L = cubeLB B ![𝟙 B, w] M ∧ P.IsSymmetric ∧
      ∀ (T : Over S) (x y : T ⟶ B), LBIso (cubeLB B ![x, y] P.L) (cubeLB B ![x, y] M) := by
  have hc := fun T : Over S => diff₃_ptCls (T := T) hM hT
  have hq : ∀ T : Over S, (fun x : T ⟶ B => normCls M w x.left) =
      fun x => diff₂ (ptCls M T) x (postHom w T x) := fun T => funext fun x => normCls_left w x
  have hs : ∀ (T : Over S) (y : T ⟶ B), postHom w T y * postHom w' T y = y := fun T y =>
    (MonObj.comp_mul y w w').symm.trans (by rw [hw, Category.comp_id])
  have hadj : ∀ (T : Over S) (x y : T ⟶ B),
      diff₂ (ptCls M T) (postHom w T x) y = diff₂ (ptCls M T) x (postHom w' T y) := fun T x y =>
    diff₂_ptCls_adj hM ha x y
  have hL : (cubeLB B ![𝟙 B, w] M).IsLB := DVR.linComb_isLB _ hM _ _
  obtain ⟨rig, hrig⟩ : HasGen (cubeLB B ![𝟙 B, w] M) (K := PUnit) (fun _ => eSec B) (fun _ => 1) := by
    refine hasGen_nested hM _ _ _ _ ?_
    rw [Fintype.prod_unique, zpow_one]
    refine (normCls_left w η[B]).trans ?_
    have e : η[B] = (1 : 𝟙_ (Over S) ⟶ B) := by simp [Hom.one_def]
    rw [e, MonObj.one_comp]
    simp [diff₂]
  let P : RigLB B := ⟨_, rig, hL, hrig⟩
  obtain ⟨t, ht⟩ : HasGen (cubeLB B ![𝟙 B, w] M) (thφ B (x3 B)) thε := by
    refine hasGen_nested hM _ _ _ _ ((GlobalTheory.AbLaw.Cube.prod_theta (normCls M w)).trans
      ((prod_cub _ _ _ (normCls M w)).trans ?_))
    have := diff₃_quadratic (hc (G3 B)) _ _ (hs _) (hadj _) (x3 B 0) (x3 B 1) (x3 B 2)
    rw [← hq] at this
    exact this
  obtain ⟨t', ht', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised hL t ht
  refine ⟨P, GlobalTheory.AbLaw.Cube.cubicalOfNormalised hG hB P t' ht' hn, rfl, isSymmetric_of_hasGen P ?_, fun T x y => ?_⟩
  · refine hasGen_nested hM _ _ _ _ ?_
    rw [Fin.prod_univ_two]
    show normCls M w (GrpObj.inv (X := B)).left ^ (1 : ℤ) * normCls M w (𝟙 B : B ⟶ B).left ^ (-1 : ℤ) = 1
    have e : GrpObj.inv (X := B) = (𝟙 B)⁻¹ := by simp [Hom.inv_def]
    have e' : (𝟙 B)⁻¹ ≫ w = (𝟙 B ≫ w)⁻¹ := map_inv (postHom w B) _
    rw [normCls_left, normCls_left, e, e', diff₂_inv_inv (hc B), zpow_neg, mul_inv_cancel]
  · refine lbIso_nested hM _ _ _ _ _ _ ((prod_square_id x y (normCls M w)).trans
      (Eq.trans ?_ (prod_square_id x y (cls M)).symm))
    rw [hq]
    exact diff₂_quadratic (hc T) _ _ (hs _) (hadj _) x y

end Main

theorem exists_primitive_normalisation :
    Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (B : Over S)
      [GrpObj B] [IsCommMonObj B] (act : OAct (𝓞 E) B) (M : LB B.left), IsAbelianScheme B → M.IsLB →
      (∃ t : LB.Gen (Theta B M), t.IsGen) →
      (∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M)) →
      ∃ (PP : RigLB B) (_ : CubicalStr B PP), PP.IsSymmetric ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0] M) ∧
        LBIso (abelian₂ B PP.L) (abelian₂ B M) ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0] PP.L) ∧
        ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] PP.L)
          (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] PP.L) := by
  intro hG E _ _ _ H S B _ _ act M hB hM hT ha
  have := act.hom H.w0
  have := act.hom (H.bar H.w0)
  obtain ⟨P, c, e, sym, iso⟩ := exists_normalised_bundle hG hB hM hT (act.act H.w0) (act.act (H.bar H.w0))
    (by rw [← act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, act.one]) (ha H.w0)
  have lb : ∀ {T : Over S} (x : Fin 2 → (T ⟶ B)) {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB := fun x L hL =>
    DVR.linComb_isLB _ hL _ _
  refine ⟨P, c, sym, ?_, iso _ _ _, ?_, fun a => ?_⟩
  · rw [e]
    exact (lbIso_iff hM _ _ _ _).2 rfl
  · have := (iso B (𝟙 B) (act.act H.w0)).symm
    rwa [← e] at this
  · exact LBIso.trans (lb _ P.isLB) (lb _ hM) (lb _ P.isLB) (iso _ _ _)
      (LBIso.trans (lb _ hM) (lb _ hM) (lb _ P.isLB) (ha a) (iso _ _ _).symm)

end GlobalTheory.PrimNorm
