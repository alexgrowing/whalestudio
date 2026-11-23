import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open Simplicial

namespace GlobalTheory.CompanionTheory.Hodge.Prism

theorem sum_pairs {M : Type} [AddCommGroup M] (n : ℕ) (T : Fin (n + 3) → Fin (n + 2) → M)
    (S : Fin (n + 2) → Fin (n + 1) → M)
    (h1 : ∀ i j, i ≤ j.castSucc → T i.castSucc j.succ = - S i j)
    (h2 : ∀ i j, j.castSucc < i → T i.succ j.castSucc = - S i j) :
    ∑ i, ∑ j, S i j + ∑ j, ∑ i, T i j = ∑ j : Fin (n + 2), (T j.castSucc j + T j.succ j) := by
  have key : ∑ j, ∑ i, T i j = ∑ p ∈ (Finset.univ : Finset (Fin (n + 3) × Fin (n + 2))).filter
        (fun p ↦ p.1 ≠ p.2.castSucc ∧ p.1 ≠ p.2.succ), T p.1 p.2 +
      ∑ j : Fin (n + 2), (T j.castSucc j + T j.succ j) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hne : j.castSucc ≠ j.succ := by simp [Fin.ext_iff]
    have e : ∀ i, T i j = (if i ≠ j.castSucc ∧ i ≠ j.succ then T i j else 0) +
        ((if i = j.castSucc then T i j else 0) + (if i = j.succ then T i j else 0)) := by
      intro i
      by_cases a : i = j.castSucc
      · subst a; simp [hne]
      · by_cases b : i = j.succ
        · subst b; simp [a]
        · simp [a, b]
    conv_lhs => rw [Finset.sum_congr rfl fun i _ ↦ e i]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp
  have key2 : ∑ p ∈ (Finset.univ : Finset (Fin (n + 3) × Fin (n + 2))).filter
        (fun p ↦ p.1 ≠ p.2.castSucc ∧ p.1 ≠ p.2.succ), T p.1 p.2 = - ∑ i, ∑ j, S i j := by
    rw [← Finset.sum_product', ← Finset.sum_neg_distrib]
    symm
    refine Finset.sum_bij
      (fun (p : Fin (n + 2) × Fin (n + 1)) _ ↦
        if p.1 ≤ p.2.castSucc then ((p.1.castSucc, p.2.succ) : Fin (n + 3) × Fin (n + 2))
        else (p.1.succ, p.2.castSucc)) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ -
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h <;> simp [Fin.ext_iff, Fin.le_def, Fin.lt_def] at h ⊢ <;> omega
    · rintro ⟨i, j⟩ - ⟨i', j'⟩ - h
      simp only at h
      split_ifs at h with h₁ h₂ h₂ <;>
        simp [Prod.ext_iff, Fin.ext_iff, Fin.le_def] at h h₁ h₂ ⊢ <;> omega
    · rintro ⟨i, j⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, ne_eq, Fin.val_castSucc, Fin.val_succ] at hp
      rcases lt_or_gt_of_ne hp.1 with h | h
      · refine ⟨(⟨i, by omega⟩, ⟨j - 1, by omega⟩), Finset.mem_univ _, ?_⟩
        simp only
        rw [if_pos (by simp [Fin.le_def]; omega)]
        simp [Prod.ext_iff, Fin.ext_iff]; omega
      · refine ⟨(⟨i - 1, by omega⟩, ⟨j, by omega⟩), Finset.mem_univ _, ?_⟩
        simp only
        rw [if_neg (by simp [Fin.le_def]; omega)]
        simp [Prod.ext_iff, Fin.ext_iff]; omega
    · rintro ⟨i, j⟩ -
      simp only
      split_ifs with h
      · simp [h1 i j h]
      · simp [h2 i j (not_le.1 h)]
  rw [key, key2]; abel

section Ops

variable {R : Type} [CommRing R] {D : Type} [Category.{0} D] (G : D ⥤ CommAlgCat.{0} R)

abbrev Cyl : D × Bool ⥤ CommAlgCat.{0} R := CategoryTheory.Prod.fst D Bool ⋙ G

def P {k n : ℕ} (a : ⦋k⦌ ⟶ ⦋n⦌) (l : Fin (k + 1) →o Bool) : Cn (Cyl G) k →ₗ[R] Cn G n where
  toFun f c := mp G (c.map (homOfLE (Fin.le_last (a.toOrderHom (Fin.last k)))))
    (f ((a.toOrderHom.monotone.functor ⋙ c).prod' l.monotone.functor))
  map_add' f g := funext fun c ↦ map_add _ _ _
  map_smul' r f := funext fun c ↦ map_smul _ _ _

theorem cof_P {k n : ℕ} (a : ⦋k⦌ ⟶ ⦋n⦌) (l : Fin (k + 1) →o Bool) (i : Fin (n + 2)) (f : Cn (Cyl G) k) :
    cof G n i (P G a l f) = P G (a ≫ SimplexCategory.δ i) l f := by
  funext c
  refine (mp_comp G _ _ _).symm.trans ?_
  exact congrArg (fun t ↦ mp G t _) ((c.map_comp _ _).symm.trans (congrArg c.map (Subsingleton.elim _ _)))

theorem P_cof {k n : ℕ} (a : ⦋k + 1⦌ ⟶ ⦋n⦌) (l : Fin (k + 2) →o Bool) (i : Fin (k + 2)) (f : Cn (Cyl G) k) :
    P G a l (cof (Cyl G) k i f) =
      P G (SimplexCategory.δ i ≫ a) (l.comp (Fin.succAboveOrderEmb i).toOrderHom) f := by
  funext c
  refine (mp_comp G _ _ _).symm.trans ?_
  exact congrArg (fun t ↦ mp G t _) ((c.map_comp _ _).symm.trans (congrArg c.map (Subsingleton.elim _ _)))

end Ops

section Ops2

variable {R : Type} [CommRing R] {D : Type} [Category.{0} D] (G : D ⥤ CommAlgCat.{0} R)

def lab (m k : ℕ) : Fin m →o Bool where
  toFun x := decide (k ≤ x.val)
  monotone' x y h := by
    have h' : x.val ≤ y.val := h
    by_cases a : k ≤ x.val
    · have b : k ≤ y.val := a.trans h'
      simp [a, b]
    · simp [a]

theorem lab_comp {m : ℕ} (i : Fin (m + 1)) (k k' : ℕ)
    (h : ∀ x : Fin m, k ≤ (i.succAbove x).val ↔ k' ≤ x.val) :
    (lab (m + 1) k).comp (Fin.succAboveOrderEmb i).toOrderHom = lab m k' := by
  ext x
  exact decide_eq_decide.2 (h x)

theorem val_succAbove {m : ℕ} (i : Fin (m + 1)) (x : Fin m) :
    (i.succAbove x).val = if x.val < i.val then x.val else x.val + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

def hop (n : ℕ) : Cn (Cyl G) (n + 1) →ₗ[R] Cn G n :=
  ∑ j : Fin (n + 1), ((-1 : R) ^ (j : ℕ)) • P G (SimplexCategory.σ j) (lab (n + 2) (j + 1))

theorem homotopy (n : ℕ) (f : Cn (Cyl G) (n + 1)) :
    dn G n (hop G n f) + hop G (n + 1) (dn (Cyl G) (n + 1) f) =
      P G (𝟙 _) (lab (n + 2) 0) f - P G (𝟙 _) (lab (n + 2) (n + 2)) f := by
  let S : Fin (n + 2) → Fin (n + 1) → Cn G (n + 1) := fun i j ↦
    ((-1 : R) ^ ((i : ℕ) + (j : ℕ))) • P G (SimplexCategory.σ j ≫ SimplexCategory.δ i) (lab (n + 2) (j + 1)) f
  let T : Fin (n + 3) → Fin (n + 2) → Cn G (n + 1) := fun i j ↦
    ((-1 : R) ^ ((i : ℕ) + (j : ℕ))) • P G (SimplexCategory.δ i ≫ SimplexCategory.σ j)
      ((lab (n + 3) (j + 1)).comp (Fin.succAboveOrderEmb i).toOrderHom) f
  have e1 : dn G n (hop G n f) = ∑ i, ∑ j, S i j := by
    simp only [dn, hop, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, cof_P, Finset.smul_sum,
      smul_smul, S, pow_add]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    first | rfl | exact congrArg₂ (· • ·) (mul_comm _ _) rfl
  have e2 : hop G (n + 1) (dn (Cyl G) (n + 1) f) = ∑ j, ∑ i, T i j := by
    simp only [dn, hop, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, P_cof, Finset.smul_sum,
      smul_smul, T, pow_add]
    rw [Finset.sum_comm]
  have h1 : ∀ i j, i ≤ j.castSucc → T i.castSucc j.succ = - S i j := by
    intro i j h
    have hl : (lab (n + 3) ((j : ℕ) + 1 + 1)).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom =
        lab (n + 2) (j + 1) := by
      refine lab_comp _ _ _ fun x ↦ ?_
      have h' : i.val ≤ j.val := h
      rw [val_succAbove]
      simp only [Fin.val_castSucc]
      split_ifs <;> omega
    have s : ((-1 : R) ^ ((i : ℕ) + ((j : ℕ) + 1))) = -(-1) ^ ((i : ℕ) + (j : ℕ)) := by
      rw [← add_assoc, pow_succ]; simp
    simp only [T, S, Fin.val_castSucc, Fin.val_succ, hl, SimplexCategory.δ_comp_σ_of_le h, s, neg_smul]
  have h2 : ∀ i j, j.castSucc < i → T i.succ j.castSucc = - S i j := by
    intro i j h
    have hl : (lab (n + 3) ((j : ℕ) + 1)).comp (Fin.succAboveOrderEmb i.succ).toOrderHom =
        lab (n + 2) (j + 1) := by
      refine lab_comp _ _ _ fun x ↦ ?_
      have h' : j.val < i.val := h
      rw [val_succAbove]
      simp only [Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
    have s : ((-1 : R) ^ ((i : ℕ) + 1 + (j : ℕ))) = -(-1) ^ ((i : ℕ) + (j : ℕ)) := by
      rw [show (i : ℕ) + 1 + (j : ℕ) = (i : ℕ) + (j : ℕ) + 1 by omega, pow_succ]; simp
    simp only [T, S, Fin.val_castSucc, Fin.val_succ, hl, SimplexCategory.δ_comp_σ_of_gt h, s, neg_smul]
  have d1 : ∀ j : Fin (n + 2), T j.castSucc j + T j.succ j =
      P G (𝟙 _) (lab (n + 2) j) f - P G (𝟙 _) (lab (n + 2) (j + 1)) f := by
    intro j
    have hl1 : (lab (n + 3) ((j : ℕ) + 1)).comp (Fin.succAboveOrderEmb j.castSucc).toOrderHom =
        lab (n + 2) j := by
      refine lab_comp _ _ _ fun x ↦ ?_
      rw [val_succAbove]
      simp only [Fin.val_castSucc]
      split_ifs <;> omega
    have hl2 : (lab (n + 3) ((j : ℕ) + 1)).comp (Fin.succAboveOrderEmb j.succ).toOrderHom =
        lab (n + 2) (j + 1) := by
      refine lab_comp _ _ _ fun x ↦ ?_
      rw [val_succAbove]
      simp only [Fin.val_succ]
      split_ifs <;> omega
    simp only [T, hl1, hl2, SimplexCategory.δ_comp_σ_self, SimplexCategory.δ_comp_σ_succ, Fin.val_castSucc,
      Fin.val_succ]
    have s1 : ((-1 : R) ^ ((j : ℕ) + (j : ℕ))) = 1 := by rw [← two_mul, pow_mul]; simp
    have s2 : ((-1 : R) ^ ((j : ℕ) + 1 + (j : ℕ))) = -1 := by
      rw [show (j : ℕ) + 1 + (j : ℕ) = (j : ℕ) + (j : ℕ) + 1 by omega, pow_succ, s1]; simp
    rw [s1, s2]
    simp [sub_eq_add_neg]
  rw [e1, e2, sum_pairs n T S h1 h2, Finset.sum_congr rfl fun j _ ↦ d1 j,
    Fin.sum_univ_eq_sum_range (fun k ↦ P G (𝟙 _) (lab (n + 2) k) f - P G (𝟙 _) (lab (n + 2) (k + 1)) f) (n + 2),
    Finset.sum_range_sub']

end Ops2

section Deg0

variable {R : Type} [CommRing R] {D : Type} [Category.{0} D] (G : D ⥤ CommAlgCat.{0} R)

theorem homotopy_zero (f : Cn (Cyl G) 0) :
    hop G 0 (dn (Cyl G) 0 f) = P G (𝟙 _) (lab 1 0) f - P G (𝟙 _) (lab 1 1) f := by
  have hl1 : (lab 2 1).comp (Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom = lab 1 0 :=
    lab_comp _ _ _ fun x ↦ by rw [val_succAbove]; simp
  have hl2 : (lab 2 1).comp (Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom = lab 1 1 :=
    lab_comp _ _ _ fun x ↦ by rw [val_succAbove]; simp
  have e0 : (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.σ (0 : Fin 1)) = 𝟙 _ :=
    SimplexCategory.δ_comp_σ_self (i := (0 : Fin 1))
  have e1 : (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.σ (0 : Fin 1)) = 𝟙 _ :=
    SimplexCategory.δ_comp_σ_succ (i := (0 : Fin 1))
  simp [dn, hop, Fin.sum_univ_two, P_cof, hl1, hl2, e0, e1, sub_eq_add_neg]

end Deg0

section Cylinder

variable {C D : Type} [Category.{0} C] [Category.{0} D] {A B : D ⥤ C} (θ : A ⟶ B)

theorem no_back {T T' : D} (φ : ((T, true) : D × Bool) ⟶ (T', false)) : False := by
  have h : true ≤ false := leOfHom φ.2
  exact absurd h (by decide)

def cylObj (A B : D ⥤ C) (p : D × Bool) : C :=
  match p with
  | (T, false) => A.obj T
  | (T, true) => B.obj T

def cylMap {p q : D × Bool} (φ : p ⟶ q) : cylObj A B p ⟶ cylObj A B q :=
  match p, q, φ with
  | (_, false), (_, false), φ => A.map φ.1
  | (_, false), (T', true), φ => A.map φ.1 ≫ θ.app T'
  | (_, true), (_, false), φ => (no_back φ).elim
  | (_, true), (_, true), φ => B.map φ.1

def cyl : D × Bool ⥤ C where
  obj := cylObj A B
  map := cylMap θ
  map_id := by
    rintro ⟨T, _ | _⟩ <;> simp [cylMap, cylObj]
  map_comp := by
    rintro ⟨T, _ | _⟩ ⟨T', _ | _⟩ ⟨T'', _ | _⟩ φ ψ <;>
      first
      | exact (no_back φ).elim
      | exact (no_back ψ).elim
      | simp [cylMap, cylObj]

end Cylinder

section Coef

variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R} (m m' : CoefMap (RingHom.id R) F G) (θ : m.G ⟶ m'.G)

def cylAl (p : D × Bool) : F.obj ((cyl θ).obj p) →+* (Cyl G).obj p :=
  match p with
  | (T, false) => m.α T
  | (T, true) => m'.α T

def cylCoef (hθ : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b) : CoefMap (RingHom.id R) F (Cyl G) where
  G := cyl θ
  α := cylAl m m' θ
  naturality := by
    rintro ⟨T, _ | _⟩ ⟨T', _ | _⟩ φ b
    · exact m.naturality φ.1 b
    · refine Eq.trans ?_ (m.naturality φ.1 b)
      refine Eq.trans ?_ (hθ T' _)
      exact congrArg (m'.α T') (mp_comp F _ _ _)
    · exact (no_back φ).elim
    · exact m'.naturality φ.1 b
  smul := by
    rintro ⟨T, _ | _⟩ r b
    · exact m.smul T r b
    · exact m'.smul T r b

variable (hθ : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b)

theorem lab_false (k : ℕ) : lab (k + 1) (k + 1) = OrderHom.const _ false := by
  ext x
  have := x.2
  simp [lab]; omega

theorem lab_true (k : ℕ) : lab (k + 1) 0 = OrderHom.const _ true := by
  ext x
  simp [lab]

theorem P_pull_false (k : ℕ) (z : Cn F k) :
    P G (𝟙 _) (lab (k + 1) (k + 1)) (pulln (cylCoef m m' θ hθ) k z) = pulln m k z := by
  rw [lab_false]
  funext c
  refine (congrArg (fun t ↦ mp G t _) (?_ : c.map _ = 𝟙 _)).trans ((mp_id G _ _).trans ?_)
  · exact (congrArg c.map (Subsingleton.elim _ _)).trans (c.map_id _)
  · rfl

theorem P_pull_true (k : ℕ) (z : Cn F k) :
    P G (𝟙 _) (lab (k + 1) 0) (pulln (cylCoef m m' θ hθ) k z) = pulln m' k z := by
  rw [lab_true]
  funext c
  refine (congrArg (fun t ↦ mp G t _) (?_ : c.map _ = 𝟙 _)).trans ((mp_id G _ _).trans ?_)
  · exact (congrArg c.map (Subsingleton.elim _ _)).trans (c.map_id _)
  · rfl

end Coef

end GlobalTheory.CompanionTheory.Hodge.Prism

namespace GlobalTheory.CompanionTheory.Hodge

open Prism in

theorem htpySt_of_cxSt : CxSt → HtpySt := by
  intro hC R _ C _ F D _ G m m' θ hθ
  have hx := fun (k : ℕ) (z : Cn F k) ↦
    LinearMap.congr_fun ((hC R C F).2 (D × Bool) (Cyl G) (cylCoef m m' θ hθ) k) z
  simp only [LinearMap.comp_apply] at hx
  refine ⟨fun z hz ↦ ?_, fun n z hz ↦ ?_⟩
  · have h0 := homotopy_zero G (pulln (cylCoef m m' θ hθ) 0 z)
    have a : P G (𝟙 _) (lab 1 0) (pulln (cylCoef m m' θ hθ) 0 z) = pulln m' 0 z := P_pull_true m m' θ hθ 0 z
    have b : P G (𝟙 _) (lab 1 1) (pulln (cylCoef m m' θ hθ) 0 z) = pulln m 0 z := P_pull_false m m' θ hθ 0 z
    rw [← hx, hz, map_zero, map_zero, a, b] at h0
    exact (sub_eq_zero.1 h0.symm).symm
  · have h0 := homotopy G n (pulln (cylCoef m m' θ hθ) (n + 1) z)
    have a : P G (𝟙 _) (lab (n + 2) 0) (pulln (cylCoef m m' θ hθ) (n + 1) z) = pulln m' (n + 1) z :=
      P_pull_true m m' θ hθ (n + 1) z
    have b : P G (𝟙 _) (lab (n + 2) (n + 2)) (pulln (cylCoef m m' θ hθ) (n + 1) z) = pulln m (n + 1) z :=
      P_pull_false m m' θ hθ (n + 1) z
    rw [← hx, hz, map_zero, map_zero, add_zero, a, b] at h0
    exact ⟨-hop G n (pulln (cylCoef m m' θ hθ) (n + 1) z), by rw [map_neg, h0]; abel⟩

end GlobalTheory.CompanionTheory.Hodge
