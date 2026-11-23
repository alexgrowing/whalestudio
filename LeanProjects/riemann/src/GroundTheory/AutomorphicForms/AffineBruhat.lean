import Mathlib
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.AutomorphicForms.GLnLattice
import GroundTheory.AutomorphicForms.FiniteBruhat

noncomputable section

namespace GroundTheory.Automorphic

open Matrix DoubleCoset ValuativeRel

namespace GLnLocal

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)

section Iwahori

def residueReduction : GL (Fin n) 𝒪[F] →* GL (Fin n) (IsLocalRing.ResidueField 𝒪[F]) :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F])

theorem residueReduction_apply (u : GL (Fin n) 𝒪[F]) (i j : Fin n) :
    (residueReduction F n u : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField 𝒪[F])) i j =
      IsLocalRing.residue 𝒪[F] (u i j) :=
  rfl

def iwahori : Subgroup (GL (Fin n) F) :=
  ((borel n (IsLocalRing.ResidueField 𝒪[F])).comap (residueReduction F n)).map (integralGLHom F n)

theorem residue_eq_zero_iff_valuation_lt_one (x : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x = 0 ↔ valuation F (x : F) < 1 := by
  rw [← not_iff_not, ← ne_eq, IsLocalRing.residue_ne_zero_iff_isUnit,
    (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm ((Valuation.mem_integer_iff _ _).mp x.2) h⟩

theorem residue_ne_zero_iff_valuation_eq_one (x : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x ≠ 0 ↔ valuation F (x : F) = 1 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit,
    (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one]
  exact Iff.rfl

theorem exists_mem_iwahori (M : Matrix (Fin n) (Fin n) F)
    (h1 : ∀ i j, valuation F (M i j) ≤ 1) (h2 : ∀ i j, j < i → valuation F (M i j) < 1)
    (h3 : ∀ i, valuation F (M i i) = 1) :
    ∃ x ∈ iwahori F n, (x : Matrix (Fin n) (Fin n) F) = M := by
  classical
  let A : Matrix (Fin n) (Fin n) 𝒪[F] :=
    Matrix.of fun i j => ⟨M i j, (Valuation.mem_integer_iff _ _).mpr (h1 i j)⟩
  let Ā := (IsLocalRing.residue 𝒪[F]).mapMatrix A
  have hup : Ā.IsUpperTriangular := by
    intro i j hij
    exact (residue_eq_zero_iff_valuation_lt_one F (A i j)).mpr (h2 i j hij)
  have hdiag : ∀ i, Ā i i ≠ 0 := fun i => (residue_ne_zero_iff_valuation_eq_one F (A i i)).mpr (h3 i)
  have hdetĀ : IsUnit Ā.det := by
    rw [det_of_isUpperTriangular hup, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i
  have hdetA : IsUnit A.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    exact hdetĀ.ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr hdetA
  refine ⟨integralGLHom F n u, ⟨u, ?_, rfl⟩, ?_⟩
  · change residueReduction F n u ∈ borel n _
    rw [mem_borel_iff]
    intro i j hij
    rw [residueReduction_apply, hu]
    exact hup hij
  · ext i j
    rw [integralGLHom_apply, hu]
    rfl

theorem mem_iwahori_iff {g : GL (Fin n) F} :
    g ∈ iwahori F n ↔ (∀ i j, valuation F (g i j) ≤ 1) ∧
      (∀ i j, j < i → valuation F (g i j) < 1) ∧ ∀ i, valuation F (g i i) = 1 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    change residueReduction F n u ∈ borel n _ at hu
    refine ⟨fun i j => (Valuation.mem_integer_iff _ _).mp (u i j).2, fun i j hij => ?_,
      fun i => ?_⟩
    · exact (residue_eq_zero_iff_valuation_lt_one F (u i j)).mp ((mem_borel_iff _).mp hu i j hij)
    · exact (residue_ne_zero_iff_valuation_eq_one F (u i i)).mp (borel_diag_ne_zero hu i)
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨x, hx, hxg⟩ := exists_mem_iwahori F n (g : Matrix (Fin n) (Fin n) F) h1 h2 h3
    rwa [show x = g from Units.ext hxg] at hx

theorem iwahori_le_integralGL : iwahori F n ≤ integralGL F n :=
  Subgroup.map_le_range _ _

theorem congruenceSubgroup_one_le_iwahori : congruenceSubgroup F n 1 ≤ iwahori F n := by
  intro g hg
  obtain ⟨hK, hg⟩ := (mem_congruenceSubgroup_iff F n).mp hg
  have hK' := ((mem_integralGL_iff F n).mp hK).1
  rw [mem_iwahori_iff]
  refine ⟨fun i j => (Valuation.mem_integer_iff _ _).mp (hK' i j), fun i j hij => ?_, fun i => ?_⟩
  · have h := hg i j
    rw [Matrix.one_apply_ne hij.ne', sub_zero, pow_one] at h
    exact h.trans_lt (valuation_uniformizer_lt_one F)
  · have h := hg i i
    rw [Matrix.one_apply_eq, pow_one] at h
    have hlt : valuation F (g i i - 1) < valuation F 1 := by
      rw [map_one]
      exact h.trans_lt (valuation_uniformizer_lt_one F)
    rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]

theorem isOpen_iwahori : IsOpen (iwahori F n : Set (GL (Fin n) F)) :=
  Subgroup.isOpen_mono (congruenceSubgroup_one_le_iwahori F n) (isOpen_congruenceSubgroup F n 1)

theorem isCompact_iwahori : IsCompact (iwahori F n : Set (GL (Fin n) F)) :=
  (isCompact_integralGL F n).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_iwahori F n)) (iwahori_le_integralGL F n)

end Iwahori

section AffineWeyl

theorem uniformizer_ne_zero : ϖ ≠ 0 := fun h =>
  (irreducible_uniformizer F).ne_zero (Subtype.ext h)

theorem valuation_uniformizer_pos : 0 < valuation F ϖ :=
  zero_lt_iff.mpr (valuation_uniformizer_ne_zero F)

def diagPow : (Fin n → Multiplicative ℤ) →* GL (Fin n) F where
  toFun a :=
    { val := diagonal fun i => ϖ ^ (a i).toAdd
      inv := diagonal fun i => ϖ ^ (-(a i).toAdd)
      val_inv := by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        rw [← zpow_add₀ (uniformizer_ne_zero F), add_neg_cancel, zpow_zero]
      inv_val := by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        rw [← zpow_add₀ (uniformizer_ne_zero F), neg_add_cancel, zpow_zero] }
  map_one' := by
    refine Units.ext ?_
    change (diagonal fun i => ϖ ^ ((1 : Fin n → Multiplicative ℤ) i).toAdd) = 1
    rw [← diagonal_one]
    congr 1
    funext i
    simp
  map_mul' a b := by
    refine Units.ext ?_
    change (diagonal fun i => ϖ ^ ((a * b) i).toAdd) =
      (diagonal fun i => ϖ ^ (a i).toAdd) * (diagonal fun i => ϖ ^ (b i).toAdd)
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    rw [Pi.mul_apply, toAdd_mul, zpow_add₀ (uniformizer_ne_zero F)]

theorem diagPow_val (a : Fin n → Multiplicative ℤ) :
    (diagPow F n a : Matrix (Fin n) (Fin n) F) = diagonal fun i => ϖ ^ (a i).toAdd :=
  rfl

def permAct : Equiv.Perm (Fin n) →* MulAut (Fin n → Multiplicative ℤ) where
  toFun σ :=
    { toFun := fun a i => a (σ⁻¹ i)
      invFun := fun a i => a (σ i)
      left_inv := fun a => funext fun i => by simp
      right_inv := fun a => funext fun i => by simp
      map_mul' := fun _ _ => rfl }
  map_one' := by
    ext a i
    rfl
  map_mul' σ τ := by
    ext a i
    show a ((σ * τ)⁻¹ i) = a (τ⁻¹ (σ⁻¹ i))
    rw [_root_.mul_inv_rev, Equiv.Perm.mul_apply]

theorem permAct_apply (σ : Equiv.Perm (Fin n)) (a : Fin n → Multiplicative ℤ) (i : Fin n) :
    permAct n σ a i = a (σ⁻¹ i) :=
  rfl

theorem permAct_symm_apply (σ : Equiv.Perm (Fin n)) (a : Fin n → Multiplicative ℤ) (i : Fin n) :
    (permAct n σ).symm a i = a (σ i) :=
  rfl

abbrev ExtendedAffineWeyl := (Fin n → Multiplicative ℤ) ⋊[permAct n] Equiv.Perm (Fin n)

theorem permGL_mul_diagPow_mul_inv (σ : Equiv.Perm (Fin n)) (a : Fin n → Multiplicative ℤ) :
    permGL F σ * diagPow F n a * (permGL F σ)⁻¹ = diagPow F n (permAct n σ a) := by
  refine Units.ext ?_
  ext i j
  rw [← map_inv, Units.val_mul, mul_permGL_apply, Units.val_mul, permGL_mul_apply, diagPow_val,
    diagPow_val, diagonal_apply, diagonal_apply]
  simp only [permAct_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij, if_neg]
    intro h
    exact hij (σ⁻¹.injective h)

def affineWeylGL : ExtendedAffineWeyl n →* GL (Fin n) F :=
  SemidirectProduct.lift (diagPow F n) (permGL F) fun σ => by
    ext a : 1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [permGL_mul_diagPow_mul_inv]

theorem affineWeylGL_apply (w : ExtendedAffineWeyl n) (i j : Fin n) :
    (affineWeylGL F n w : Matrix (Fin n) (Fin n) F) i j =
      if i = w.right j then ϖ ^ (w.left i).toAdd else 0 := by
  show ((diagPow F n w.left * permGL F w.right : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = _
  rw [Units.val_mul, diagPow_val, diagonal_mul, permGL_apply]
  split_ifs <;> simp

theorem valuation_le_of_mem_doubleCoset {w w' : ExtendedAffineWeyl n}
    (h : affineWeylGL F n w' ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n))
    (c : Fin n) :
    valuation F ϖ ^ (w'.left (w'.right c)).toAdd ≤ valuation F ϖ ^ (w.left (w.right c)).toAdd ∧
      (w.right c < w'.right c →
        valuation F ϖ ^ (w'.left (w'.right c)).toAdd <
          valuation F ϖ ^ (w.left (w.right c)).toAdd) := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp h
  have hy' : y⁻¹ ∈ iwahori F n := (iwahori F n).inv_mem hy
  have hmat : (x : Matrix (Fin n) (Fin n) F) * (affineWeylGL F n w : Matrix (Fin n) (Fin n) F) =
      (affineWeylGL F n w' : Matrix (Fin n) (Fin n) F) *
        ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [← Units.val_mul, ← Units.val_mul, hxy]
    congr 1
    group
  have hent := congrFun (congrFun hmat (w'.right c)) c
  rw [mul_apply, Fintype.sum_eq_single (w.right c), mul_apply,
    Fintype.sum_eq_single c] at hent
  rotate_left
  · intro l hl
    rw [affineWeylGL_apply, if_neg, zero_mul]
    exact fun e => hl (w'.right.injective e).symm
  · intro l hl
    rw [affineWeylGL_apply, if_neg, mul_zero]
    exact hl
  rw [affineWeylGL_apply, if_pos rfl, affineWeylGL_apply, if_pos rfl] at hent
  have hv := congrArg (valuation F) hent
  rw [map_mul, map_mul, map_zpow₀, map_zpow₀, ((mem_iwahori_iff F n).mp hy').2.2 c, mul_one] at hv
  obtain ⟨hx1, hx2, -⟩ := (mem_iwahori_iff F n).mp hx
  have hpos : 0 < valuation F ϖ ^ (w.left (w.right c)).toAdd :=
    zpow_pos (valuation_uniformizer_pos F) _
  refine ⟨?_, fun hlt => ?_⟩
  · rw [← hv]
    calc valuation F (x (w'.right c) (w.right c)) * valuation F ϖ ^ (w.left (w.right c)).toAdd
        ≤ 1 * valuation F ϖ ^ (w.left (w.right c)).toAdd := mul_le_mul_of_nonneg_right
          (hx1 _ _) hpos.le
      _ = _ := one_mul _
  · rw [← hv]
    calc valuation F (x (w'.right c) (w.right c)) * valuation F ϖ ^ (w.left (w.right c)).toAdd
        < 1 * valuation F ϖ ^ (w.left (w.right c)).toAdd := mul_lt_mul_of_pos_right
          (hx2 _ _ hlt) hpos
      _ = _ := one_mul _

theorem eq_of_affineWeylGL_mem_doubleCoset {w w' : ExtendedAffineWeyl n}
    (h : affineWeylGL F n w' ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n)) :
    w = w' := by
  have h' : affineWeylGL F n w ∈
      doubleCoset (affineWeylGL F n w') (iwahori F n) (iwahori F n) := by
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp h
    refine mem_doubleCoset.mpr ⟨x⁻¹, (iwahori F n).inv_mem hx, y⁻¹, (iwahori F n).inv_mem hy, ?_⟩
    rw [hxy]
    group
  have heq : ∀ c, valuation F ϖ ^ (w'.left (w'.right c)).toAdd =
      valuation F ϖ ^ (w.left (w.right c)).toAdd := fun c =>
    le_antisymm (valuation_le_of_mem_doubleCoset F n h c).1
      (valuation_le_of_mem_doubleCoset F n h' c).1
  have hle : ∀ c, w'.right c ≤ w.right c := by
    intro c
    by_contra hlt
    push Not at hlt
    exact ((valuation_le_of_mem_doubleCoset F n h c).2 hlt).ne (heq c)
  have hπ := perm_eq_one_of_forall_le (w'.right * w.right⁻¹) (fun x => by
    simpa using hle (w.right⁻¹ x))
  have hright : w.right = w'.right := by
    have := congrArg (· * w.right) hπ
    simpa using this.symm
  have hinj := (zpow_right_strictAnti₀ (valuation_uniformizer_pos F)
    (valuation_uniformizer_lt_one F)).injective
  refine SemidirectProduct.ext ?_ hright
  funext i
  have := heq (w.right⁻¹ i)
  rw [← hright, show w.right (w.right⁻¹ i) = i from w.right.apply_symm_apply i] at this
  exact Multiplicative.toAdd.injective (hinj this).symm

theorem affineWeylGL_injective : Function.Injective (affineWeylGL F n) := by
  intro w w' h
  apply eq_of_affineWeylGL_mem_doubleCoset F n
  rw [← h]
  exact mem_doubleCoset_self _ _ _

end AffineWeyl

section Existence

variable {F n} in

def RowsReducedOn (M : Matrix (Fin n) (Fin n) F) (R : Finset (Fin n)) : Prop :=
  ∃ p : Fin n → Fin n, ∀ i ∈ R,
    M i (p i) ≠ 0 ∧ (∀ c, c ≠ p i → M i c = 0) ∧ (∀ r, r ≠ i → M r (p i) = 0)

theorem rowsReducedOn_step (h : GL (Fin n) F) (R : Finset (Fin n)) (hR : R ≠ Finset.univ)
    (hred : RowsReducedOn (h : Matrix (Fin n) (Fin n) F) R) :
    ∃ x ∈ iwahori F n, ∃ y ∈ iwahori F n, ∃ r ∉ R,
      RowsReducedOn ((x * h * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (insert r R) := by
  classical
  obtain ⟨p, hp⟩ := hred
  obtain ⟨i₀, hi₀⟩ : ∃ i, i ∉ R := by
    by_contra hcon
    push Not at hcon
    exact hR (Finset.eq_univ_of_forall hcon)
  have hrow : ∀ i, ∃ j, (h : Matrix (Fin n) (Fin n) F) i j ≠ 0 := by
    intro i
    by_contra hcon
    push Not at hcon
    exact ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
      (det_eq_zero_of_row_eq_zero i hcon)
  let M : Matrix (Fin n) (Fin n) F := h
  let S : Finset (Fin n × Fin n) := Finset.univ.filter fun e => e.1 ∉ R
  have hS : S.Nonempty := ⟨(i₀, i₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
  obtain ⟨e₀, he₀S, he₀⟩ := S.exists_max_image (fun e => valuation F (M e.1 e.2)) hS
  let S₀ := S.filter fun e => valuation F (M e.1 e.2) = valuation F (M e₀.1 e₀.2)
  have hS₀ : S₀.Nonempty := ⟨e₀, Finset.mem_filter.mpr ⟨he₀S, rfl⟩⟩
  obtain ⟨⟨r₁, c⟩, he₁S₀, he₁⟩ := S₀.exists_min_image (fun e => e.2) hS₀
  let S₁ := S₀.filter fun e => e.2 = c
  have hS₁ : S₁.Nonempty := ⟨(r₁, c), Finset.mem_filter.mpr ⟨he₁S₀, rfl⟩⟩
  obtain ⟨⟨r, c₂⟩, he₂S₁, he₂⟩ := S₁.exists_max_image (fun e => e.1) hS₁
  obtain ⟨he₂S₀, hc₂⟩ := Finset.mem_filter.mp he₂S₁
  obtain ⟨he₂S, hv⟩ := Finset.mem_filter.mp he₂S₀
  have hr : r ∉ R := (Finset.mem_filter.mp he₂S).2
  simp only at hc₂ hv
  subst hc₂

  have F1 : ∀ i, i ∉ R → ∀ j, valuation F (M i j) ≤ valuation F (M r c₂) := fun i hi j => by
    rw [hv]
    exact he₀ (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have F2 : ∀ i, i ∉ R → ∀ j, valuation F (M i j) = valuation F (M r c₂) → c₂ ≤ j :=
    fun i hi j hij => he₁ (i, j) (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hij.trans hv⟩)
  have F3 : ∀ i, i ∉ R → valuation F (M i c₂) = valuation F (M r c₂) → i ≤ r :=
    fun i hi hij => he₂ (i, c₂) (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hij.trans hv⟩, rfl⟩)
  have hP : M r c₂ ≠ 0 := by
    obtain ⟨j, hj⟩ := hrow i₀
    intro h0
    have := F1 i₀ hi₀ j
    rw [h0, map_zero] at this
    exact hj ((Valuation.zero_iff _).mp (le_antisymm this zero_le))
  have hvP : 0 < valuation F (M r c₂) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hP)
  have hpc : ∀ i ∈ R, p i ≠ c₂ := by
    intro i hi e
    exact hP (e ▸ (hp i hi).2.2 r (fun e' => hr (e' ▸ hi)))
  have hRc : ∀ i ∈ R, M i c₂ = 0 := fun i hi => (hp i hi).2.1 c₂ (Ne.symm (hpc i hi))
  have hrp : ∀ i ∈ R, M r (p i) = 0 := fun i hi => (hp i hi).2.2 r (fun e => hr (e ▸ hi))

  let u : Fin n → F := fun i => if i = r then 0 else -(M i c₂ / M r c₂)
  have hu_val : ∀ i, i ≠ r → valuation F (u i) = valuation F (M i c₂) / valuation F (M r c₂) := by
    intro i hi
    simp only [u, if_neg hi, Valuation.map_neg, map_div₀]
  have hu_le : ∀ i, valuation F (u i) ≤ 1 := by
    intro i
    by_cases hi : i = r
    · simp [u, hi]
    rw [hu_val i hi, div_le_one₀ hvP]
    by_cases hiR : i ∈ R
    · rw [hRc i hiR, map_zero]
      exact hvP.le
    · exact F1 i hiR c₂
  have hu_lt : ∀ i, r < i → valuation F (u i) < 1 := by
    intro i hri
    have hi : i ≠ r := hri.ne'
    rw [hu_val i hi, div_lt_one₀ hvP]
    by_cases hiR : i ∈ R
    · rw [hRc i hiR, map_zero]
      exact hvP
    · exact lt_of_le_of_ne (F1 i hiR c₂) fun e => absurd (F3 i hiR e) (not_le.mpr hri)
  have hur : u r = 0 := by simp [u]
  have huR : ∀ i ∈ R, u i = 0 := by
    intro i hi
    have hir : i ≠ r := fun e => hr (e ▸ hi)
    simp [u, hir, hRc i hi]
  let X : Matrix (Fin n) (Fin n) F := 1 + vecMulVec u (Pi.single r 1)
  have hX : ∀ i j, X i j = (1 : Matrix (Fin n) (Fin n) F) i j + if j = r then u i else 0 := by
    intro i j
    simp only [X, Matrix.add_apply, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp
  obtain ⟨x, hx, hxX⟩ := exists_mem_iwahori F n X
    (fun i j => by
      rw [hX]
      by_cases hij : i = j
      · subst hij
        rw [one_apply_eq]
        by_cases hir : i = r
        · rw [if_pos hir, hir, hur, add_zero, map_one]
        · rw [if_neg hir, add_zero, map_one]
      · rw [one_apply_ne hij, zero_add]
        split_ifs
        · exact hu_le i
        · rw [map_zero]
          exact zero_le)
    (fun i j hji => by
      rw [hX, one_apply_ne hji.ne', zero_add]
      split_ifs with hjr
      · exact hu_lt i (hjr ▸ hji)
      · rw [map_zero]
        exact zero_lt_one)
    (fun i => by
      rw [hX, one_apply_eq]
      by_cases hir : i = r
      · rw [if_pos hir, hir, hur, add_zero, map_one]
      · rw [if_neg hir, add_zero, map_one])

  let t : Fin n → F := fun j => if j = c₂ then 0 else -(M r j / M r c₂)
  have ht_val : ∀ j, j ≠ c₂ → valuation F (t j) = valuation F (M r j) / valuation F (M r c₂) := by
    intro j hj
    simp only [t, if_neg hj, Valuation.map_neg, map_div₀]
  have htc : t c₂ = 0 := by simp [t]
  have ht_le : ∀ j, valuation F (t j) ≤ 1 := by
    intro j
    by_cases hj : j = c₂
    · simp [t, hj]
    rw [ht_val j hj, div_le_one₀ hvP]
    exact F1 r hr j
  have ht_lt : ∀ j, j < c₂ → valuation F (t j) < 1 := by
    intro j hj
    rw [ht_val j hj.ne, div_lt_one₀ hvP]
    exact lt_of_le_of_ne (F1 r hr j) fun e => absurd (F2 r hr j e) (not_le.mpr hj)
  let Y : Matrix (Fin n) (Fin n) F := 1 + vecMulVec (Pi.single c₂ 1) t
  have hY : ∀ i j, Y i j = (1 : Matrix (Fin n) (Fin n) F) i j + if i = c₂ then t j else 0 := by
    intro i j
    simp only [Y, Matrix.add_apply, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp
  obtain ⟨y, hy, hyY⟩ := exists_mem_iwahori F n Y
    (fun i j => by
      rw [hY]
      by_cases hij : i = j
      · subst hij
        rw [one_apply_eq]
        by_cases hic : i = c₂
        · rw [if_pos hic, hic, htc, add_zero, map_one]
        · rw [if_neg hic, add_zero, map_one]
      · rw [one_apply_ne hij, zero_add]
        split_ifs
        · exact ht_le j
        · rw [map_zero]
          exact zero_le)
    (fun i j hji => by
      rw [hY, one_apply_ne hji.ne', zero_add]
      split_ifs with hic
      · exact ht_lt j (hic ▸ hji)
      · rw [map_zero]
        exact zero_lt_one)
    (fun i => by
      rw [hY, one_apply_eq]
      by_cases hic : i = c₂
      · rw [if_pos hic, hic, htc, add_zero, map_one]
      · rw [if_neg hic, add_zero, map_one])

  let M₁ : Matrix (Fin n) (Fin n) F := X * M
  have hM₁ : ∀ a b, M₁ a b = M a b + u a * M r b := fun a b =>
    one_add_vecMulVec_mul_apply M r u a b
  have hM₁c : ∀ a, a ≠ r → M₁ a c₂ = 0 := by
    intro a ha
    rw [hM₁]
    simp only [u, if_neg ha]
    rw [neg_mul, div_mul_cancel₀ _ hP, add_neg_cancel]
  have hN : ∀ a b, ((x * h * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b =
      M₁ a b + M₁ a c₂ * t b := by
    intro a b
    rw [Units.val_mul, Units.val_mul, hxX, hyY]
    exact mul_one_add_vecMulVec_apply M₁ c₂ t a b
  refine ⟨x, hx, y, hy, r, hr, Function.update p r c₂, fun i hi => ?_⟩
  rcases Finset.mem_insert.mp hi with rfl | hiR
  · rw [Function.update_self]
    refine ⟨?_, fun b hb => ?_, fun a ha => ?_⟩
    · rw [hN, htc, mul_zero, add_zero, hM₁, hur, zero_mul, add_zero]
      exact hP
    · rw [hN, hM₁, hM₁, hur, zero_mul, zero_mul, add_zero, add_zero]
      simp only [t, if_neg hb]
      rw [mul_neg, mul_div_cancel₀ _ hP, add_neg_cancel]
    · rw [hN, hM₁c a ha, zero_mul, add_zero]
  · have hir : i ≠ r := fun e => hr (e ▸ hiR)
    rw [Function.update_of_ne hir]
    obtain ⟨h1, h2, h3⟩ := hp i hiR
    have hrow_i : ∀ b, ((x * h * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i b = M i b := by
      intro b
      rw [hN, hM₁c i hir, zero_mul, add_zero, hM₁, huR i hiR, zero_mul, add_zero]
    refine ⟨by rw [hrow_i]; exact h1, fun b hb => by rw [hrow_i]; exact h2 b hb, fun a ha => ?_⟩
    rw [hN]
    by_cases har : a = r
    · subst har
      have htp : t (p i) = 0 := by
        simp only [t, if_neg (hpc i hiR), hrp i hiR, zero_div, neg_zero]
      rw [htp, mul_zero, add_zero, hM₁, hrp i hiR, mul_zero, add_zero]
    · have h3' : M a (p i) = 0 := h3 a ha
      rw [hM₁c a har, zero_mul, add_zero, hM₁, h3', hrp i hiR, mul_zero, add_zero]

theorem exists_rowsReducedOn_univ (g : GL (Fin n) F) :
    ∃ x ∈ iwahori F n, ∃ y ∈ iwahori F n,
      RowsReducedOn ((x * g * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) Finset.univ := by
  have key : ∀ d, d ≤ n → ∃ x ∈ iwahori F n, ∃ y ∈ iwahori F n, ∃ R : Finset (Fin n),
      R.card = d ∧ RowsReducedOn ((x * g * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) R := by
    intro d
    induction d with
    | zero =>
      intro _
      exact ⟨1, (iwahori F n).one_mem, 1, (iwahori F n).one_mem, ∅, rfl, id, fun i hi =>
        absurd hi (Finset.notMem_empty i)⟩
    | succ d ih =>
      intro hd
      obtain ⟨x, hx, y, hy, R, hRc, hred⟩ := ih (by omega)
      have hRne : R ≠ Finset.univ := by
        intro e
        rw [e, Finset.card_univ, Fintype.card_fin] at hRc
        omega
      obtain ⟨x', hx', y', hy', r, hr, hred'⟩ := rowsReducedOn_step F n _ R hRne hred
      refine ⟨x' * x, (iwahori F n).mul_mem hx' hx, y * y', (iwahori F n).mul_mem hy hy',
        insert r R, by rw [Finset.card_insert_of_notMem hr, hRc], ?_⟩
      simpa only [mul_assoc] using hred'
  obtain ⟨x, hx, y, hy, R, hRc, hred⟩ := key n le_rfl
  have hR : R = Finset.univ := Finset.eq_univ_of_card R (by rw [hRc, Fintype.card_fin])
  exact ⟨x, hx, y, hy, hR ▸ hred⟩

theorem exists_valuation_div_zpow_eq_one {x : F} (hx : x ≠ 0) :
    ∃ m : ℤ, valuation F (x / ϖ ^ m) = 1 := by
  obtain ⟨N, hN⟩ := (eventually_pow_mul_mem F x).exists
  have hϖ := uniformizer_ne_zero F
  have hy : (⟨ϖ ^ N * x, hN⟩ : 𝒪[F]) ≠ 0 := by
    intro h0
    have := congrArg Subtype.val h0
    exact mul_ne_zero (pow_ne_zero N hϖ) hx this
  obtain ⟨k, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy (irreducible_uniformizer F)
  have hu' : ϖ ^ N * x = ((u : 𝒪[F]) : F) * ϖ ^ k := by
    have := congrArg (fun z : 𝒪[F] => (z : F)) hu
    simpa using this
  refine ⟨(k : ℤ) - N, ?_⟩
  have hxu : x / ϖ ^ ((k : ℤ) - N) = ((u : 𝒪[F]) : F) := by
    rw [zpow_sub₀ hϖ, zpow_natCast, zpow_natCast, div_div_eq_mul_div, mul_comm x, hu',
      mul_div_assoc, div_self (pow_ne_zero _ hϖ), mul_one]
  rw [hxu]
  exact (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.mp u.isUnit

theorem exists_eq_mul_affineWeylGL_of_rowsReducedOn (g : GL (Fin n) F)
    (hred : RowsReducedOn (g : Matrix (Fin n) (Fin n) F) Finset.univ) :
    ∃ w : ExtendedAffineWeyl n, ∃ t ∈ iwahori F n, g = t * affineWeylGL F n w := by
  classical
  obtain ⟨p, hp⟩ := hred
  have hp' := fun i => hp i (Finset.mem_univ i)
  have hinj : Function.Injective p := by
    intro i i' e
    by_contra hii
    exact (hp' i').1 (e ▸ (hp' i).2.2 i' (Ne.symm hii))
  let τ : Equiv.Perm (Fin n) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj)
  have hτ : ∀ i, τ i = p i := fun i => rfl
  choose m hm using fun i => exists_valuation_div_zpow_eq_one F (hp' i).1
  let w : ExtendedAffineWeyl n := ⟨fun i => Multiplicative.ofAdd (m i), τ⁻¹⟩
  let d : Fin n → F := fun i => (g : Matrix (Fin n) (Fin n) F) i (p i) / ϖ ^ m i
  obtain ⟨t, ht, htd⟩ := exists_mem_iwahori F n (diagonal d)
    (fun i j => by
      rw [diagonal_apply]
      split_ifs with hij
      · exact (hm i).le
      · rw [map_zero]
        exact zero_le)
    (fun i j hji => by
      rw [diagonal_apply, if_neg hji.ne', map_zero]
      exact zero_lt_one)
    (fun i => by rw [diagonal_apply_eq]; exact hm i)
  refine ⟨w, t, ht, Units.ext ?_⟩
  ext i j
  rw [Units.val_mul, htd, diagonal_mul, affineWeylGL_apply]
  have hϖm : ϖ ^ m i ≠ 0 := zpow_ne_zero _ (uniformizer_ne_zero F)
  by_cases hj : j = p i
  · subst hj
    rw [if_pos (by simp [w, ← hτ])]
    simp only [d, w, toAdd_ofAdd]
    rw [div_mul_cancel₀ _ hϖm]
  · rw [(hp' i).2.1 j hj, if_neg, mul_zero]
    intro e
    apply hj
    simp only [w] at e
    rw [← hτ, e]
    simp

theorem exists_mem_doubleCoset_affineWeylGL (g : GL (Fin n) F) :
    ∃ w : ExtendedAffineWeyl n,
      g ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n) := by
  obtain ⟨x, hx, y, hy, hred⟩ := exists_rowsReducedOn_univ F n g
  obtain ⟨w, t, ht, hgt⟩ := exists_eq_mul_affineWeylGL_of_rowsReducedOn F n _ hred
  refine ⟨w, mem_doubleCoset.mpr ⟨x⁻¹ * t, (iwahori F n).mul_mem ((iwahori F n).inv_mem hx) ht,
    y⁻¹, (iwahori F n).inv_mem hy, ?_⟩⟩
  rw [mul_assoc x⁻¹ t, ← hgt]
  group

end Existence

section Decomposition

theorem doubleCoset_affineWeylGL_injective {w w' : ExtendedAffineWeyl n} {g : GL (Fin n) F}
    (hw : g ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n))
    (hw' : g ∈ doubleCoset (affineWeylGL F n w') (iwahori F n) (iwahori F n)) : w = w' := by
  have e : doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n) =
      doubleCoset (affineWeylGL F n w') (iwahori F n) (iwahori F n) :=
    (doubleCoset_eq_of_mem hw).symm.trans (doubleCoset_eq_of_mem hw')
  have hmem := mem_doubleCoset_self (iwahori F n) (iwahori F n) (affineWeylGL F n w')
  rw [← e] at hmem
  exact eq_of_affineWeylGL_mem_doubleCoset F n hmem

theorem affineBruhat_decomposition (g : GL (Fin n) F) :
    ∃! w : ExtendedAffineWeyl n,
      g ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n) := by
  obtain ⟨w, hw⟩ := exists_mem_doubleCoset_affineWeylGL F n g
  exact ⟨w, hw, fun w' hw' => (doubleCoset_affineWeylGL_injective F n hw hw').symm⟩

theorem iUnion_doubleCoset_affineWeylGL :
    ⋃ w : ExtendedAffineWeyl n, doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n) =
      Set.univ :=
  Set.eq_univ_of_forall fun g =>
    Set.mem_iUnion.mpr (exists_mem_doubleCoset_affineWeylGL F n g)

theorem pairwise_disjoint_doubleCoset_affineWeylGL :
    Pairwise (Function.onFun Disjoint fun w : ExtendedAffineWeyl n =>
      doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n)) := by
  intro w w' hww'
  rw [Function.onFun, Set.disjoint_left]
  intro g hw hw'
  exact hww' (doubleCoset_affineWeylGL_injective F n hw hw')

theorem bijective_mk_affineWeylGL :
    Function.Bijective fun w : ExtendedAffineWeyl n =>
      DoubleCoset.mk (iwahori F n) (iwahori F n) (affineWeylGL F n w) := by
  constructor
  · intro w w' hww'
    obtain ⟨x, hx, y, hy, hxy⟩ := (DoubleCoset.eq _ _ _ _).mp hww'
    exact eq_of_affineWeylGL_mem_doubleCoset F n (mem_doubleCoset.mpr ⟨x, hx, y, hy, hxy⟩)
  · intro q
    obtain ⟨w, hw⟩ := exists_mem_doubleCoset_affineWeylGL F n q.out
    refine ⟨w, ?_⟩
    simp only
    rw [← mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hw), out_eq']

end Decomposition

section Integral

theorem affineWeylGL_inr (σ : Equiv.Perm (Fin n)) :
    affineWeylGL F n (SemidirectProduct.inr σ) = permGL F σ :=
  SemidirectProduct.lift_inr _ _ _ _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem permGL_mem_integralGL (σ : Equiv.Perm (Fin n)) : permGL F σ ∈ integralGL F n := by
  rw [mem_integralGL_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [permGL_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · rw [← map_inv, permGL_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

theorem affineWeylGL_mem_integralGL_iff (w : ExtendedAffineWeyl n) :
    affineWeylGL F n w ∈ integralGL F n ↔ w.left = 1 := by
  constructor
  · intro hw
    obtain ⟨h1, h2⟩ := (mem_integralGL_iff F n).mp hw
    have hle : ∀ i, valuation F ϖ ^ (w.left i).toAdd ≤ 1 := by
      intro i
      have := h1 i (w.right⁻¹ i)
      rw [affineWeylGL_apply, if_pos (by simp)] at this
      rwa [Valuation.mem_integer_iff, map_zpow₀] at this
    have hle' : ∀ i, valuation F ϖ ^ (-(w.left i).toAdd) ≤ 1 := by
      intro i
      have := h2 (w.right⁻¹ i) i
      rw [← map_inv, affineWeylGL_apply, if_pos (by simp)] at this
      rw [Valuation.mem_integer_iff, map_zpow₀] at this
      simpa [permAct_symm_apply] using this
    funext i
    have hq := valuation_uniformizer_pos F
    have h0 : valuation F ϖ ^ (w.left i).toAdd = valuation F ϖ ^ (0 : ℤ) := by
      rw [zpow_zero]
      refine le_antisymm (hle i) ?_
      have hmul : valuation F ϖ ^ (w.left i).toAdd * valuation F ϖ ^ (-(w.left i).toAdd) = 1 := by
        rw [← zpow_add₀ hq.ne', add_neg_cancel, zpow_zero]
      by_contra hlt
      push Not at hlt
      have : valuation F ϖ ^ (w.left i).toAdd * valuation F ϖ ^ (-(w.left i).toAdd) < 1 :=
        mul_lt_one_of_lt_of_le hlt (hle' i)
      rw [hmul] at this
      exact lt_irrefl _ this
    have := (zpow_right_strictAnti₀ hq (valuation_uniformizer_lt_one F)).injective h0
    exact Multiplicative.toAdd.injective this
  · intro hw
    have : w = SemidirectProduct.inr w.right := SemidirectProduct.ext hw rfl
    rw [this, affineWeylGL_inr]
    exact permGL_mem_integralGL F n _

theorem integralGL_eq_iUnion_doubleCoset_permGL :
    (integralGL F n : Set (GL (Fin n) F)) =
      ⋃ σ : Equiv.Perm (Fin n), doubleCoset (permGL F σ) (iwahori F n) (iwahori F n) := by
  ext k
  constructor
  · intro hk
    obtain ⟨w, hw⟩ := exists_mem_doubleCoset_affineWeylGL F n k
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp hw
    have hwK : affineWeylGL F n w ∈ integralGL F n := by
      have : affineWeylGL F n w = x⁻¹ * k * y⁻¹ := by
        rw [hxy]
        group
      rw [this]
      exact (integralGL F n).mul_mem ((integralGL F n).mul_mem
        ((integralGL F n).inv_mem (iwahori_le_integralGL F n hx)) hk)
        ((integralGL F n).inv_mem (iwahori_le_integralGL F n hy))
    have hleft := (affineWeylGL_mem_integralGL_iff F n w).mp hwK
    have hw' : w = SemidirectProduct.inr w.right := SemidirectProduct.ext hleft rfl
    refine Set.mem_iUnion.mpr ⟨w.right, ?_⟩
    rw [← affineWeylGL_inr, ← hw']
    exact hw
  · intro hk
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hk
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_doubleCoset.mp hσ
    exact (integralGL F n).mul_mem ((integralGL F n).mul_mem (iwahori_le_integralGL F n hx)
      (permGL_mem_integralGL F n σ)) (iwahori_le_integralGL F n hy)

end Integral

end GLnLocal

end GroundTheory.Automorphic
