import Mathlib
import Formalism.SubspaceCounting.ChoiceOfTopsRefined
import Formalism.SatakeDualWeyl.Statement
import Formalism.SatakeDualWeyl.StatementE
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc

noncomputable section

open Matrix Module

namespace Formalism.IndefR.Fin.HCount

variable {L : Type} [Field L] (O : Subring L)

def IntM {m n : Type*} (M : Matrix m n L) : Prop := ∀ i j, M i j ∈ O

def IsReps {G : Type*} [Group G] (K : Subgroup G) (α : G) (R : Finset G) : Prop :=
  (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) ∧
    ∀ x, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K

theorem intM_mul {l m n : Type*} [Fintype m] {M : Matrix l m L} {N : Matrix m n L} (hM : IntM O M) (hN : IntM O N) :
    IntM O (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)

def liftM {m n : Type*} (M : Matrix m n L) (h : IntM O M) : Matrix m n O := fun i j => ⟨M i j, h i j⟩

theorem liftM_map {m n : Type*} (M : Matrix m n L) (h : IntM O M) : (liftM O M h).map O.subtype = M := by
  ext i j; rfl

theorem intM_map {m n : Type*} (N : Matrix m n O) : IntM O (N.map O.subtype) := fun i j => (N i j).2

theorem map_subtype_injective {m n : Type*} : Function.Injective (fun N : Matrix m n O => N.map O.subtype) :=
  Matrix.map_injective Subtype.val_injective

theorem liftM_mul {l m n : Type*} [Fintype m] (M : Matrix l m L) (N : Matrix m n L) (hM : IntM O M) (hN : IntM O N) :
    (liftM O M hM * liftM O N hN).map O.subtype = M * N := by
  rw [Matrix.map_mul, liftM_map, liftM_map]

theorem mem_GLint {n : Type} [Fintype n] [DecidableEq n] (g : GL n L) :
    g ∈ Formalism.UG.GLint n O ↔ IntM O (g : Matrix n n L) ∧ IntM O ((g⁻¹ : GL n L) : Matrix n n L) := by
  constructor
  · rintro ⟨g', rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · change (g' : Matrix n n O).map O.subtype i j ∈ O
      exact ((g' : Matrix n n O) i j).2
    · rw [← map_inv]
      change ((g'⁻¹ : GL n O) : Matrix n n O).map O.subtype i j ∈ O
      exact (((g'⁻¹ : GL n O) : Matrix n n O) i j).2
  · rintro ⟨h1, h2⟩
    have e1 : liftM O _ h1 * liftM O _ h2 = 1 := by
      apply map_subtype_injective O
      change (liftM O _ h1 * liftM O _ h2).map O.subtype = (1 : Matrix n n O).map O.subtype
      rw [liftM_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have e2 : liftM O _ h2 * liftM O _ h1 = 1 := by
      apply map_subtype_injective O
      change (liftM O _ h2 * liftM O _ h1).map O.subtype = (1 : Matrix n n O).map O.subtype
      rw [liftM_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨⟨liftM O _ h1, liftM O _ h2, e1, e2⟩, ?_⟩
    ext i j
    rfl

theorem intM_of_GLint {n : Type} [Fintype n] [DecidableEq n] {g : GL n L} (hg : g ∈ Formalism.UG.GLint n O) :
    IntM O (g : Matrix n n L) := ((mem_GLint O g).1 hg).1

theorem intM_inv_of_GLint {n : Type} [Fintype n] [DecidableEq n] {g : GL n L} (hg : g ∈ Formalism.UG.GLint n O) :
    IntM O ((g⁻¹ : GL n L) : Matrix n n L) := ((mem_GLint O g).1 hg).2

section Red

variable [IsDiscreteValuationRing O]

open Classical in

def resL (x : L) : IsLocalRing.ResidueField O :=
  if h : x ∈ O then IsLocalRing.residue O ⟨x, h⟩ else 0

theorem resL_coe (x : O) : resL O (x : L) = IsLocalRing.residue O x := by
  simp [resL, x.2]

def redM {m n : Type*} (M : Matrix m n L) : Matrix m n (IsLocalRing.ResidueField O) := M.map (resL O)

theorem redM_map {m n : Type*} (N : Matrix m n O) : redM O (N.map O.subtype) = N.map (IsLocalRing.residue O) := by
  ext i j
  simp only [redM, Matrix.map_apply, Subring.coe_subtype, resL_coe]

theorem redM_eq {m n : Type*} (M : Matrix m n L) (h : IntM O M) :
    redM O M = (liftM O M h).map (IsLocalRing.residue O) := by
  rw [← redM_map, liftM_map]

theorem redM_mul {l m n : Type*} [Fintype m] {M : Matrix l m L} {N : Matrix m n L} (hM : IntM O M) (hN : IntM O N) :
    redM O (M * N) = redM O M * redM O N := by
  rw [← liftM_mul O M N hM hN, redM_map, Matrix.map_mul, redM_eq O M hM, redM_eq O N hN]

theorem exists_GLint_lift {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n (IsLocalRing.ResidueField O))
    (hP : P.det ≠ 0) : ∃ g : GL n L, g ∈ Formalism.UG.GLint n O ∧ redM O (g : Matrix n n L) = P := by
  let Q : Matrix n n O := fun i j => Function.surjInv IsLocalRing.residue_surjective (P i j)
  have hQ : Q.map (IsLocalRing.residue O) = P := by
    ext i j; exact Function.surjInv_eq _ _
  have hdet : IsUnit Q.det := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    have : (IsLocalRing.residue O).mapMatrix Q = P := hQ
    rw [this]; exact hP
  have hU : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2 hdet
  refine ⟨Formalism.UG.bc O.subtype hU.unit, ⟨hU.unit, rfl⟩, ?_⟩
  change redM O (Q.map O.subtype) = P
  rw [redM_map, hQ]

end Red

section Rank

variable [IsDiscreteValuationRing O]

theorem finrank_ker_mulVecLin {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K) :
    finrank K (LinearMap.ker A.mulVecLin) = Fintype.card n - A.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_pi] at h
  have : A.rank = finrank K (LinearMap.range A.mulVecLin) := rfl
  omega

theorem residue_unif_eq_zero {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalRing.residue O ϖ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  exact hϖ.not_isUnit

theorem dvd_of_residue_eq_zero {ϖ : O} (hϖ : Irreducible ϖ) {x : O} (hx : IsLocalRing.residue O x = 0) : ϖ ∣ x := by
  rw [IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ] at hx
  exact Ideal.mem_span_singleton.1 hx

theorem prodEquivOfIsCompl_inl {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (W C : Submodule K V)
    (h : IsCompl W C) (y : W) : W.prodEquivOfIsCompl C h (y, 0) = y := by
  have := Submodule.prodEquivOfIsCompl_symm_apply_left W C h y
  rw [← this, LinearEquiv.apply_symm_apply]

theorem det_eq_pow_mul {ϖ : O} (hϖ : Irreducible ϖ) {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n O) :
    ∃ c : O, N.det = ϖ ^ (Fintype.card n - (N.map (IsLocalRing.residue O)).rank) * c := by
  classical
  set Nb := N.map (IsLocalRing.residue O) with hNb
  set W := LinearMap.ker Nb.mulVecLin with hW
  obtain ⟨C, hC⟩ := W.exists_isCompl
  let bW := Module.finBasis (IsLocalRing.ResidueField O) W
  let bC := Module.finBasis (IsLocalRing.ResidueField O) C
  let b0 := (bW.prod bC).map (W.prodEquivOfIsCompl C hC)
  have hcard : Fintype.card (Fin (finrank (IsLocalRing.ResidueField O) W) ⊕
      Fin (finrank (IsLocalRing.ResidueField O) C)) = Fintype.card n := by
    have h1 := Module.finrank_eq_card_basis b0
    rw [Module.finrank_pi] at h1
    exact h1.symm
  let e := Fintype.equivOfCardEq hcard
  let b := b0.reindex e
  have hb : ∀ w, b (e (Sum.inl w)) ∈ W := by
    intro w
    have : b (e (Sum.inl w)) = (bW w : n → IsLocalRing.ResidueField O) := by
      simp only [b, b0, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply,
        Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply]
      exact prodEquivOfIsCompl_inl W C hC (bW w)
    rw [this]; exact (bW w).2
  let Qb : Matrix n n (IsLocalRing.ResidueField O) := (Pi.basisFun (IsLocalRing.ResidueField O) n).toMatrix b
  have hQb : ∀ i j, Qb i j = b j i := by
    intro i j
    simp only [Qb, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hQbdet : Qb.det ≠ 0 := by
    have := (Pi.basisFun (IsLocalRing.ResidueField O) n).invertibleToMatrix b
    exact (isUnit_det_of_invertible Qb).ne_zero
  let Q : Matrix n n O := fun i j => Function.surjInv IsLocalRing.residue_surjective (Qb i j)
  have hQ : Q.map (IsLocalRing.residue O) = Qb := by
    ext i j; exact Function.surjInv_eq _ _
  have hQu : IsUnit Q.det := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    have : (IsLocalRing.residue O).mapMatrix Q = Qb := hQ
    rw [this]; exact hQbdet
  let J : Finset n := Finset.univ.map ⟨fun w => e (Sum.inl w), e.injective.comp Sum.inl_injective⟩
  have hJcard : J.card = finrank (IsLocalRing.ResidueField O) W := by
    simp [J]
  have hres : ∀ j ∈ J, ∀ i, IsLocalRing.residue O ((N * Q) i j) = 0 := by
    intro j hj i
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hj
    change IsLocalRing.residue O ((N * Q) i (e (Sum.inl w))) = 0
    have h1 : IsLocalRing.residue O ((N * Q) i (e (Sum.inl w))) = (Nb * Qb) i (e (Sum.inl w)) := by
      rw [← hQ, hNb, ← Matrix.map_mul]; rfl
    rw [h1]
    have h2 : (Nb * Qb) i (e (Sum.inl w)) = (Nb *ᵥ b (e (Sum.inl w))) i := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hQb]
    rw [h2]
    have h3 : Nb *ᵥ b (e (Sum.inl w)) = 0 := hb w
    rw [h3]; rfl
  have hdiv : ∀ j ∈ J, ∀ i, ϖ ∣ (N * Q) i j := fun j hj i => dvd_of_residue_eq_zero O hϖ (hres j hj i)
  let c : n → n → O := fun i j => if h : j ∈ J then Classical.choose (hdiv j h i) else 0
  let N' : Matrix n n O := fun i j => if j ∈ J then c i j else (N * Q) i j
  let d : n → O := fun j => if j ∈ J then ϖ else 1
  have heq : N * Q = N' * Matrix.diagonal d := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_diagonal]
    by_cases h : j ∈ J
    · have hN' : N' i j = c i j := if_pos h
      have hd : d j = ϖ := if_pos h
      have hc : c i j = Classical.choose (hdiv j h i) := dif_pos h
      rw [hN', hd, hc, mul_comm]
      exact Classical.choose_spec (hdiv j h i)
    · have hN' : N' i j = (N * Q) i j := if_neg h
      have hd : d j = 1 := if_neg h
      rw [hN', hd, mul_one]
  have hprod : ∏ j, d j = ϖ ^ J.card := by
    simp only [d]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  have hdet : N.det * Q.det = N'.det * ϖ ^ J.card := by
    rw [← Matrix.det_mul, heq, Matrix.det_mul, Matrix.det_diagonal, hprod]
  refine ⟨N'.det * ↑(hQu.unit⁻¹), ?_⟩
  have hJ : J.card = Fintype.card n - Nb.rank := by
    rw [hJcard, hW, finrank_ker_mulVecLin]
  rw [← hJ]
  calc N.det = N.det * Q.det * ↑(hQu.unit⁻¹) := by
        rw [mul_assoc]
        have : Q.det * ↑(hQu.unit⁻¹) = 1 := by
          exact hQu.mul_val_inv
        rw [this, mul_one]
    _ = ϖ ^ J.card * (N'.det * ↑(hQu.unit⁻¹)) := by rw [hdet]; ring

theorem nat_le_of_enat_add {a b : ℕ} {x : ℕ∞} (h : (a : ℕ∞) + x = b) : a ≤ b := by
  have : (a : ℕ∞) ≤ b := h ▸ le_self_add
  exact_mod_cast this

theorem rank_red {ϖ : O} (hϖ : Irreducible ϖ) {n : Type} [Fintype n] [DecidableEq n] {e : ℕ} {γ : GL n L}
    (h1 : IntM O (γ : Matrix n n L)) (h2 : IntM O ((ϖ : L) • ((γ⁻¹ : GL n L) : Matrix n n L)))
    {u : O} (hu : IsUnit u) (hd : (γ : Matrix n n L).det = (ϖ : L) ^ e * u) :
    e ≤ Fintype.card n ∧ (redM O (γ : Matrix n n L)).rank = Fintype.card n - e := by
  classical
  set M := liftM O _ h1 with hMdef
  set M2 := liftM O _ h2 with hM2def
  have hMM : M * M2 = ϖ • (1 : Matrix n n O) := by
    apply map_subtype_injective O
    change (M * M2).map O.subtype = (ϖ • (1 : Matrix n n O)).map O.subtype
    rw [hMdef, hM2def, liftM_mul, Matrix.mul_smul, Units.mul_inv]
    ext i j
    simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, smul_eq_mul]
    split_ifs <;> simp
  have hdetM : M.det = ϖ ^ e * u := by
    apply Subtype.val_injective
    have h := RingHom.map_det O.subtype M
    simp only [Subring.coe_subtype] at h
    rw [h]
    change (M.map O.subtype).det = _
    rw [hMdef, liftM_map, hd]
    push_cast; rfl
  have hprod : M.det * M2.det = ϖ ^ Fintype.card n := by
    rw [← Matrix.det_mul, hMM, Matrix.det_smul, Matrix.det_one, mul_one]
  have hredM : redM O (γ : Matrix n n L) = M.map (IsLocalRing.residue O) := redM_eq O _ h1
  set r1 := (M.map (IsLocalRing.residue O)).rank with hr1
  set r2 := (M2.map (IsLocalRing.residue O)).rank with hr2
  have hz : M.map (IsLocalRing.residue O) * M2.map (IsLocalRing.residue O) = 0 := by
    rw [← Matrix.map_mul, hMM]
    ext i j
    simp [Matrix.smul_apply, residue_unif_eq_zero O hϖ]
  have hr12 : r2 ≤ Fintype.card n - r1 := by
    rw [hr2, ← finrank_ker_mulVecLin]
    apply Submodule.finrank_mono
    rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hz,
      Matrix.zero_mulVec]
  have hr1le : r1 ≤ Fintype.card n := Matrix.rank_le_card_width _
  have hr2le : r2 ≤ Fintype.card n := Matrix.rank_le_card_width _
  obtain ⟨c1, hc1⟩ := det_eq_pow_mul O hϖ M
  obtain ⟨c2, hc2⟩ := det_eq_pow_mul O hϖ M2
  set v := IsDiscreteValuationRing.addVal O with hv
  have hvϖ : v ϖ = 1 := IsDiscreteValuationRing.addVal_uniformizer hϖ
  have hvu : v u = 0 := by
    have := IsDiscreteValuationRing.addVal_eq_zero_of_unit hu.unit
    simpa using this
  have hvpow : ∀ m : ℕ, v (ϖ ^ m) = m := by
    intro m; rw [IsDiscreteValuationRing.addVal_pow, hvϖ]; simp
  have hvM : v M.det = e := by
    rw [hdetM, IsDiscreteValuationRing.addVal_mul, hvpow, hvu, add_zero]
  have hA : Fintype.card n - r1 ≤ e := by
    have := hvM
    rw [hc1, IsDiscreteValuationRing.addVal_mul, hvpow] at this
    exact nat_le_of_enat_add this
  have hsum : (e : ℕ∞) + v M2.det = Fintype.card n := by
    rw [← hvM, ← IsDiscreteValuationRing.addVal_mul, hprod, hvpow]
  have hne : v M2.det ≠ ⊤ := by
    intro h; rw [h] at hsum; simp at hsum
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
  have hem : e + m = Fintype.card n := by
    rw [← hm] at hsum
    have h' : ((e + m : ℕ) : ℕ∞) = (Fintype.card n : ℕ∞) := by push_cast; exact hsum
    exact_mod_cast h'
  have hB : Fintype.card n - (M2.map (IsLocalRing.residue O)).rank ≤ m := by
    have h := hm.symm
    rw [hc2, IsDiscreteValuationRing.addVal_mul, hvpow] at h
    exact nat_le_of_enat_add h
  refine ⟨by omega, ?_⟩
  rw [hredM]
  omega

end Rank

section Crit

variable [IsDiscreteValuationRing O]

theorem coe_unif_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) : (ϖ : L) ≠ 0 := by
  intro h; exact hϖ.ne_zero (Subtype.val_injective (by simpa using h))

theorem intM_add {m n : Type*} {M N : Matrix m n L} (hM : IntM O M) (hN : IntM O N) : IntM O (M + N) :=
  fun i j => Subring.add_mem _ (hM i j) (hN i j)

theorem exists_smul_of_map_residue_eq_zero {ϖ : O} (hϖ : Irreducible ϖ) {m n : Type*} (N : Matrix m n O)
    (h : N.map (IsLocalRing.residue O) = 0) : ∃ Z : Matrix m n O, N = ϖ • Z := by
  have hd : ∀ i j, ∃ c, N i j = ϖ * c := fun i j =>
    dvd_of_residue_eq_zero O hϖ (by simpa using congrFun (congrFun h i) j)
  choose Z hZ using hd
  exact ⟨Matrix.of Z, Matrix.ext fun i j => by simp [hZ i j]⟩

theorem exists_mul_of_range_le {K : Type*} [Field K] {n m p : Type*} [Fintype m] [DecidableEq m] [Fintype p]
    {A : Matrix n m K} {B : Matrix n p K} (h : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    ∃ Y : Matrix p m K, A = B * Y := by
  have hcol : ∀ j, ∃ y, B *ᵥ y = fun i => A i j := by
    intro j
    have hj : (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
      refine ⟨Pi.single j 1, ?_⟩
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    obtain ⟨y, hy⟩ := h hj
    exact ⟨y, hy⟩
  choose y hy using hcol
  refine ⟨Matrix.of fun i j => y j i, Matrix.ext fun i j => ?_⟩
  have := congrFun (hy j) i
  simp only [Matrix.mulVec, dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact this.symm

theorem redM_one {n : Type*} [DecidableEq n] : redM O (1 : Matrix n n L) = 1 := by
  have : (1 : Matrix n n L) = (1 : Matrix n n O).map O.subtype := (Matrix.map_one _ (map_zero _) (map_one _)).symm
  rw [this, redM_map, Matrix.map_one _ (map_zero _) (map_one _)]

theorem intM_inv_mul_iff {ϖ : O} (hϖ : Irreducible ϖ) {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] {M : GL n L} (h1 : IntM O (M : Matrix n n L))
    (h2 : IntM O ((ϖ : L) • ((M⁻¹ : GL n L) : Matrix n n L))) {t : Matrix n m L} (ht : IntM O t) :
    IntM O (((M⁻¹ : GL n L) : Matrix n n L) * t) ↔
      LinearMap.range (redM O t).mulVecLin ≤ LinearMap.range (redM O (M : Matrix n n L)).mulVecLin := by
  constructor
  · intro hX
    have ht' : t = (M : Matrix n n L) * (((M⁻¹ : GL n L) : Matrix n n L) * t) := by
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [ht', redM_mul O h1 hX, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · intro hle
    obtain ⟨Yb, hYb⟩ := exists_mul_of_range_le hle
    let Y : Matrix n m O := fun i j => Function.surjInv IsLocalRing.residue_surjective (Yb i j)
    have hY : Y.map (IsLocalRing.residue O) = Yb := by
      ext i j; exact Function.surjInv_eq _ _
    have hz : (liftM O t ht - liftM O _ h1 * Y).map (IsLocalRing.residue O) = 0 := by
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_mul, hY, ← redM_eq O t ht, ← redM_eq O _ h1, hYb,
        sub_self]
    obtain ⟨Z, hZ⟩ := exists_smul_of_map_residue_eq_zero O hϖ _ hz
    have htL : t = (M : Matrix n n L) * Y.map O.subtype + (ϖ : L) • Z.map O.subtype := by
      have e1 : (liftM O t ht - liftM O _ h1 * Y).map O.subtype = t - (M : Matrix n n L) * Y.map O.subtype := by
        rw [Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_mul, liftM_map, liftM_map]
      have e2 : (ϖ • Z).map O.subtype = (ϖ : L) • Z.map O.subtype := by
        ext i j; simp
      have := congrArg (fun N : Matrix n m O => N.map O.subtype) hZ
      rw [e1, e2, sub_eq_iff_eq_add] at this
      rw [this, add_comm]
    rw [htL, Matrix.mul_add, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_smul, ← Matrix.smul_mul]
    exact intM_add O (intM_map O Y) (intM_mul O h2 (intM_map O Z))

theorem inv_mul_mem_GLint {ϖ : O} (hϖ : Irreducible ϖ) {n : Type} [Fintype n] [DecidableEq n] {M M' : GL n L}
    (h1 : IntM O (M : Matrix n n L)) (h2 : IntM O ((ϖ : L) • ((M⁻¹ : GL n L) : Matrix n n L)))
    (h1' : IntM O (M' : Matrix n n L)) (h2' : IntM O ((ϖ : L) • ((M'⁻¹ : GL n L) : Matrix n n L)))
    (h : LinearMap.range (redM O (M : Matrix n n L)).mulVecLin = LinearMap.range (redM O (M' : Matrix n n L)).mulVecLin) :
    M⁻¹ * M' ∈ Formalism.UG.GLint n O := by
  rw [mem_GLint]
  refine ⟨?_, ?_⟩
  · have := (intM_inv_mul_iff O hϖ h1 h2 h1').2 h.ge
    simpa [Units.val_mul] using this
  · have := (intM_inv_mul_iff O hϖ h1' h2' h1).2 h.le
    simpa [Units.val_mul, _root_.mul_inv_rev, inv_inv] using this

end Crit

section Bij

variable [IsDiscreteValuationRing O]

structure IsType (ϖ : O) {n : Type} [Fintype n] [DecidableEq n] (e : ℕ) (γ : GL n L) : Prop where
  int : IntM O (γ : Matrix n n L)
  intInv : IntM O ((ϖ : L) • ((γ⁻¹ : GL n L) : Matrix n n L))
  det : ∃ u : O, IsUnit u ∧ (γ : Matrix n n L).det = (ϖ : L) ^ e * u

theorem isUnit_det_of_GLint {n : Type} [Fintype n] [DecidableEq n] {k : GL n L} (hk : k ∈ Formalism.UG.GLint n O) :
    ∃ u : O, IsUnit u ∧ (k : Matrix n n L).det = u := by
  obtain ⟨k', rfl⟩ := hk
  refine ⟨(k' : Matrix n n O).det, Matrix.isUnits_det_units k', ?_⟩
  change ((k' : Matrix n n O).map O.subtype).det = _
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

theorem IsType.mul_GLint {ϖ : O} {n : Type} [Fintype n] [DecidableEq n] {e : ℕ} {γ : GL n L} (hγ : IsType O ϖ e γ)
    {k₁ k₂ : GL n L} (h₁ : k₁ ∈ Formalism.UG.GLint n O) (h₂ : k₂ ∈ Formalism.UG.GLint n O) : IsType O ϖ e (k₁ * γ * k₂) := by
  obtain ⟨u, hu, hd⟩ := hγ.det
  obtain ⟨u₁, hu₁, hd₁⟩ := isUnit_det_of_GLint O h₁
  obtain ⟨u₂, hu₂, hd₂⟩ := isUnit_det_of_GLint O h₂
  refine ⟨?_, ?_, ⟨u₁ * u * u₂, (hu₁.mul hu).mul hu₂, ?_⟩⟩
  · simp only [Units.val_mul]
    exact intM_mul O (intM_mul O (intM_of_GLint O h₁) hγ.int) (intM_of_GLint O h₂)
  · have : ((k₁ * γ * k₂)⁻¹ : GL n L) = k₂⁻¹ * γ⁻¹ * k₁⁻¹ := by group
    rw [this]
    simp only [Units.val_mul]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    exact intM_mul O (intM_mul O (intM_inv_of_GLint O h₂) hγ.intInv) (intM_inv_of_GLint O h₁)
  · simp only [Units.val_mul, Matrix.det_mul, hd, hd₁, hd₂]
    push_cast; ring

theorem exists_linearEquiv_map {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (W U : Submodule K V) (h : finrank K W = finrank K U) : ∃ φ : V ≃ₗ[K] V, W.map (φ : V →ₗ[K] V) = U := by
  obtain ⟨C, hC⟩ := W.exists_isCompl
  obtain ⟨C', hC'⟩ := U.exists_isCompl
  have hCC : finrank K C = finrank K C' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 := Submodule.finrank_add_eq_of_isCompl hC'
    omega
  let e1 := LinearEquiv.ofFinrankEq W U h
  let e2 := LinearEquiv.ofFinrankEq C C' hCC
  let φ : V ≃ₗ[K] V := ((W.prodEquivOfIsCompl C hC).symm.trans (e1.prodCongr e2)).trans (U.prodEquivOfIsCompl C' hC')
  refine ⟨φ, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro x ⟨w, hw, rfl⟩
    have : φ w = (e1 ⟨w, hw⟩ : V) := by
      have hs : (W.prodEquivOfIsCompl C hC).symm w = (⟨w, hw⟩, 0) :=
        Submodule.prodEquivOfIsCompl_symm_apply_left W C hC ⟨w, hw⟩
      simp only [φ, LinearEquiv.trans_apply, hs, LinearEquiv.prodCongr_apply, map_zero]
      exact prodEquivOfIsCompl_inl U C' hC' (e1 ⟨w, hw⟩)
    rw [LinearEquiv.coe_coe, this]; exact (e1 ⟨w, hw⟩).2
  · rw [LinearEquiv.finrank_map_eq, h]

theorem range_redM_mul_GLint {n m : Type} [Fintype n] [DecidableEq n] {M : Matrix m n L} (hM : IntM O M) {k : GL n L}
    (hk : k ∈ Formalism.UG.GLint n O) :
    LinearMap.range (redM O (M * (k : Matrix n n L))).mulVecLin = LinearMap.range (redM O M).mulVecLin := by
  rw [redM_mul O hM (intM_of_GLint O hk), Matrix.mulVecLin_mul]
  apply LinearMap.range_comp_of_range_eq_top
  rw [LinearMap.range_eq_top]
  intro x
  refine ⟨redM O ((k⁻¹ : GL n L) : Matrix n n L) *ᵥ x, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← redM_mul O (intM_of_GLint O hk) (intM_inv_of_GLint O hk),
    Units.mul_inv, redM_one, Matrix.one_mulVec]

theorem exists_GLint_map {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n L} (hM : IntM O M)
    (U : Submodule (IsLocalRing.ResidueField O) (n → IsLocalRing.ResidueField O))
    (hU : finrank (IsLocalRing.ResidueField O) (LinearMap.range (redM O M).mulVecLin) =
      finrank (IsLocalRing.ResidueField O) U) :
    ∃ g : GL n L, g ∈ Formalism.UG.GLint n O ∧ LinearMap.range (redM O ((g : Matrix n n L) * M)).mulVecLin = U := by
  obtain ⟨φ, hφ⟩ := exists_linearEquiv_map _ U hU
  have hdet : (LinearMap.toMatrix' (φ : (n → IsLocalRing.ResidueField O) →ₗ[_] _)).det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' φ).ne_zero
  obtain ⟨g, hg, hred⟩ := exists_GLint_lift O _ hdet
  refine ⟨g, hg, ?_⟩
  rw [redM_mul O (intM_of_GLint O hg) hM, hred, Matrix.mulVecLin_mul, LinearMap.range_comp, ← hφ]
  congr 1
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

open Classical in

def dgl {ϖ : L} (hϖ : ϖ ≠ 0) (n e : ℕ) : GL (Fin n) L :=
  ⟨Matrix.diagonal fun i => if (i : ℕ) < e then ϖ else 1, Matrix.diagonal fun i => if (i : ℕ) < e then ϖ⁻¹ else 1,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> field_simp,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> field_simp⟩

theorem card_filter_lt (n e : ℕ) (h : e ≤ n) : (Finset.univ.filter fun i : Fin n => (i : ℕ) < e).card = e := by
  have : (Finset.univ.filter fun i : Fin n => (i : ℕ) < e) = (Finset.univ : Finset (Fin e)).map (Fin.castLEEmb h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro hi; exact ⟨⟨i, hi⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩; exact j.2
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem isType_dgl {ϖ : O} (hϖ : Irreducible ϖ) {n e : ℕ} (he : e ≤ n) :
    IsType O ϖ e (dgl (coe_unif_ne_zero O hϖ) n e) := by
  classical
  have hne := coe_unif_ne_zero O hϖ
  refine ⟨fun i j => ?_, fun i j => ?_, ⟨1, isUnit_one, ?_⟩⟩
  · change Matrix.diagonal (fun i : Fin n => if (i : ℕ) < e then (ϖ : L) else 1) i j ∈ O
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact ϖ.2
    · exact O.one_mem
    · exact O.zero_mem
  · change ((ϖ : L) • Matrix.diagonal (fun i : Fin n => if (i : ℕ) < e then (ϖ : L)⁻¹ else 1)) i j ∈ O
    rw [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs
    · rw [mul_inv_cancel₀ hne]; exact O.one_mem
    · rw [mul_one]; exact ϖ.2
    · rw [mul_zero]; exact O.zero_mem
  · change (Matrix.diagonal fun i : Fin n => if (i : ℕ) < e then (ϖ : L) else 1).det = _
    rw [Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one,
      card_filter_lt n e he]
    simp

open Classical in

theorem card_filter_reps {ϖ : O} (hϖ : Irreducible ϖ) {n e : ℕ} {γ : GL (Fin n) L} (hγ : IsType O ϖ e γ)
    {R : Finset (GL (Fin n) L)} (hR : IsReps (Formalism.UG.GLint (Fin n) O) γ R)
    (P : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O) → Prop) :
    (R.filter fun h : GL (Fin n) L => P (LinearMap.range (redM O (h : Matrix (Fin n) (Fin n) L)).mulVecLin)).card =
      Nat.card {U : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O) //
        finrank (IsLocalRing.ResidueField O) U = n - e ∧ P U} := by
  set K := Formalism.UG.GLint (Fin n) O
  have htype : ∀ h ∈ R, IsType O ϖ e h := by
    intro h hh
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hR.1 h hh
    exact hγ.mul_GLint O hk₁ hk₂
  have hrank : ∀ h ∈ R, finrank (IsLocalRing.ResidueField O)
      (LinearMap.range (redM O (h : Matrix (Fin n) (Fin n) L)).mulVecLin) = n - e := by
    intro h hh
    obtain ⟨u, hu, hd⟩ := (htype h hh).det
    have := (rank_red O hϖ (htype h hh).int (htype h hh).intInv hu hd).2
    rw [Fintype.card_fin] at this
    exact this
  have he : e ≤ n := by
    obtain ⟨u, hu, hd⟩ := hγ.det
    have := (rank_red O hϖ hγ.int hγ.intInv hu hd).1
    rwa [Fintype.card_fin] at this
  have hne := coe_unif_ne_zero O hϖ
  set γ0 := dgl hne n e
  have h0 := isType_dgl O hϖ he
  have hr0 : finrank (IsLocalRing.ResidueField O)
      (LinearMap.range (redM O (γ0 : Matrix (Fin n) (Fin n) L)).mulVecLin) = n - e := by
    obtain ⟨u, hu, hd⟩ := h0.det
    have := (rank_red O hϖ h0.int h0.intInv hu hd).2
    rw [Fintype.card_fin] at this
    exact this
  have hrγ : finrank (IsLocalRing.ResidueField O)
      (LinearMap.range (redM O (γ : Matrix (Fin n) (Fin n) L)).mulVecLin) = n - e := by
    obtain ⟨u, hu, hd⟩ := hγ.det
    have := (rank_red O hϖ hγ.int hγ.intInv hu hd).2
    rw [Fintype.card_fin] at this
    exact this

  obtain ⟨g, hg, hgr⟩ := exists_GLint_map O h0.int _ (hr0.trans hrγ.symm)
  have hg0 : IsType O ϖ e (g * γ0) := by
    have := h0.mul_GLint O hg K.one_mem
    simpa using this
  have hk : (g * γ0)⁻¹ * γ ∈ K := by
    refine inv_mul_mem_GLint O hϖ hg0.int hg0.intInv hγ.int hγ.intInv ?_
    rw [Units.val_mul]; exact hgr

  let f : {h // h ∈ R.filter fun h : GL (Fin n) L => P (LinearMap.range (redM O (h : Matrix (Fin n) (Fin n) L)).mulVecLin)} →
      {U : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O) //
        finrank (IsLocalRing.ResidueField O) U = n - e ∧ P U} := fun h =>
    ⟨LinearMap.range (redM O (h.1 : Matrix (Fin n) (Fin n) L)).mulVecLin,
      hrank h.1 (Finset.mem_filter.1 h.2).1, (Finset.mem_filter.1 h.2).2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨h, hh⟩ ⟨h', hh'⟩ heq
      have hmem := (Finset.mem_filter.1 hh).1
      have hmem' := (Finset.mem_filter.1 hh').1
      have heq' : LinearMap.range (redM O (h : Matrix (Fin n) (Fin n) L)).mulVecLin =
          LinearMap.range (redM O (h' : Matrix (Fin n) (Fin n) L)).mulVecLin := congrArg Subtype.val heq
      have hk' : h⁻¹ * h' ∈ K := inv_mul_mem_GLint O hϖ (htype h hmem).int (htype h hmem).intInv
        (htype h' hmem').int (htype h' hmem').intInv heq'
      have hu := hR.2 h' (hR.1 h' hmem')
      have : h = h' := hu.unique ⟨hmem, hk'⟩ ⟨hmem', by simpa using K.one_mem⟩
      exact Subtype.ext this
    · rintro ⟨U, hU, hP⟩
      obtain ⟨g', hg', hg'r⟩ := exists_GLint_map O h0.int U (hr0.trans hU.symm)

      have hx : ∃ k₁ ∈ K, ∃ k₂ ∈ K, g' * γ0 = k₁ * γ * k₂ := by
        refine ⟨g' * g⁻¹, K.mul_mem hg' (K.inv_mem hg), ((g * γ0)⁻¹ * γ)⁻¹, K.inv_mem hk, ?_⟩
        group
      obtain ⟨h, ⟨hh, hhx⟩, -⟩ := hR.2 _ hx
      have hrange : LinearMap.range (redM O (h : Matrix (Fin n) (Fin n) L)).mulVecLin = U := by
        have e1 : g' * γ0 = h * (h⁻¹ * (g' * γ0)) := by group
        rw [← hg'r, ← Units.val_mul, e1, Units.val_mul]
        exact (range_redM_mul_GLint O (htype h hh).int hhx).symm
      refine ⟨⟨h, Finset.mem_filter.2 ⟨hh, ?_⟩⟩, ?_⟩
      · rw [hrange]; exact hP
      · exact Subtype.ext hrange
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_eq_of_bijective f hf

end Bij

section Count

variable [IsDiscreteValuationRing O]

def scU {ϖ : L} (hϖ : ϖ ≠ 0) (n : Type) [Fintype n] [DecidableEq n] : GL n L :=
  ⟨ϖ • (1 : Matrix n n L), ϖ⁻¹ • (1 : Matrix n n L),
    by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hϖ, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hϖ, one_smul]⟩

theorem countBelow_zero_space {K : Type} [Field K] (A : Submodule K (Fin 0 → K)) (j : ℕ) :
    Formalism.G0.countBelow A j = if j = 0 then 1 else 0 := by
  unfold Formalism.G0.countBelow
  have hfr : ∀ U : Submodule K (Fin 0 → K), finrank K U = 0 := fun U => by
    have := Submodule.finrank_le U
    rw [Module.finrank_fin_fun] at this
    omega
  have : Subsingleton (Submodule K (Fin 0 → K)) := (Submodule.subsingleton_iff K).2 inferInstance
  split_ifs with hj
  · subst hj
    have : Unique {U : Submodule K (Fin 0 → K) // U ≤ A ∧ finrank K U = 0} :=
      ⟨⟨⟨⊥, bot_le, hfr ⊥⟩⟩, fun U => Subtype.ext (Subsingleton.elim _ _)⟩
    exact Nat.card_unique
  · rw [Nat.card_eq_zero]
    left
    exact ⟨fun U => hj (by have h1 := U.2.2; have h2 := hfr U.1; omega)⟩

theorem card_subspaces_eq {K : Type} [Field K] [Fintype K] {n k : ℕ} (hk : k ≤ n) :
    Nat.card {U : Submodule K (Fin n → K) // finrank K U = n - k ∧ True} = Formalism.G0.gaussBinom (Fintype.card K) n k := by
  have H := Formalism.G0.Top.typeIIDown (F := K) (P := Fin 0 → K) (Q := Fin n → K) 0 0 n k (by simp) (by simp)
  have hL : Nat.card {U : Submodule K (Fin n → K) // LinearMap.range (0 : (Fin 0 → K) →ₗ[K] (Fin n → K)) ≤ U ∧
      finrank K U + k = 0 + n} = Nat.card {U : Submodule K (Fin n → K) // finrank K U = n - k ∧ True} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun U => ?_
    simp only [LinearMap.range_zero, bot_le, true_and, zero_add, and_true]
    omega
  rw [hL] at H
  have hR : ∑ l ∈ Finset.range (k + 1), (Fintype.card K : ℤ) ^ ((k - l) * (n - l)) *
      Formalism.G0.gaussBinom (Fintype.card K) n l *
        Formalism.G0.countBelow (LinearMap.ker (0 : (Fin 0 → K) →ₗ[K] (Fin n → K))) (k - l) =
      Formalism.G0.gaussBinom (Fintype.card K) n k := by
    rw [Finset.sum_eq_single k]
    · simp [countBelow_zero_space]
    · intro l hl hlk
      have : k - l ≠ 0 := by
        have := Finset.mem_range.1 hl
        omega
      simp [countBelow_zero_space, this]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self k)) h
  rw [hR] at H
  exact_mod_cast H

theorem card_reps {ϖ : O} (hϖ : Irreducible ϖ) [Fintype (IsLocalRing.ResidueField O)] {n k : ℕ} {α : GL (Fin n) L}
    (hα : IsType O ϖ k α) {R : Finset (GL (Fin n) L)} (hR : IsReps (Formalism.UG.GLint (Fin n) O) α R) :
    R.card = Formalism.G0.gaussBinom (Fintype.card (IsLocalRing.ResidueField O)) n k := by
  classical
  have h1 := card_filter_reps O hϖ hα hR (fun _ => True)
  first
    | simp only [Finset.filter_True] at h1
    | rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at h1
    | simp only [Finset.filter_true_of_mem, implies_true] at h1
  obtain ⟨u, hu, hd⟩ := hα.det
  have hk : k ≤ n := by
    have := (rank_red O hϖ hα.int hα.intInv hu hd).1
    rwa [Fintype.card_fin] at this
  rw [h1]
  exact card_subspaces_eq hk

end Count

section Main

variable [IsDiscreteValuationRing O]

end Main

section Index

variable [IsDiscreteValuationRing O]

def redV (n : Type) : (n → O) →ₗ[O] (n → IsLocalRing.ResidueField O) :=
  (Algebra.linearMap O (IsLocalRing.ResidueField O)).compLeft n

end Index

section Mirror

variable [IsDiscreteValuationRing O]

def invT {n : Type} [Fintype n] [DecidableEq n] (x : GL n L) : GL n L :=
  ⟨((x⁻¹ : GL n L) : Matrix n n L)ᵀ, (x : Matrix n n L)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

end Mirror

section Completion

open IsDedekindDomain NumberField

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

instance instDVROv : IsDiscreteValuationRing ↥(Formalism.UG.Ov F v) :=
  inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))

theorem card_residue_Ov : Nat.card (IsLocalRing.ResidueField ↥(Formalism.UG.Ov F v)) = Nat.card (𝓞 F ⧸ v.asIdeal) :=
  Formalism.MainNotions.Gaps.LG.fm_card_residue v

theorem finite_residue_Ov : Finite (IsLocalRing.ResidueField ↥(Formalism.UG.Ov F v)) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_residue_Ov, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  intro h
  exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

noncomputable instance instFintypeResidueOv : Fintype (IsLocalRing.ResidueField ↥(Formalism.UG.Ov F v)) :=
  @Fintype.ofFinite _ (finite_residue_Ov F v)

theorem irreducible_of_unif (x : ↥(Formalism.UG.Ov F v)) (hx : Formalism.UG.IsUnifV F v (x : v.adicCompletion F)) :
    Irreducible x := by
  have hle : ∀ y : ↥(Formalism.UG.Ov F v), Valued.v (y : v.adicCompletion F) ≤ 1 := fun y => y.2
  have hunit : ∀ y : ↥(Formalism.UG.Ov F v), Valued.v (y : v.adicCompletion F) = 1 → IsUnit y := by
    intro y hy
    have hy0 : (y : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h, map_zero] at hy; exact zero_ne_one hy
    have hmem : (y : v.adicCompletion F)⁻¹ ∈ Formalism.UG.Ov F v := by
      show Valued.v ((y : v.adicCompletion F)⁻¹) ≤ 1
      rw [map_inv₀, hy, inv_one]
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, Subtype.ext (by simp [hy0])⟩
  have hval_unit : ∀ y : ↥(Formalism.UG.Ov F v), IsUnit y → Valued.v (y : v.adicCompletion F) = 1 := by
    intro y hy
    obtain ⟨z, hz⟩ := hy.exists_right_inv
    have h1 := congrArg (fun w : ↥(Formalism.UG.Ov F v) => Valued.v (w : v.adicCompletion F)) hz
    simp only [Subring.coe_mul, map_mul, Subring.coe_one, map_one] at h1
    have := hle y; have := hle z
    by_contra hne
    have hlt : Valued.v (y : v.adicCompletion F) < 1 := lt_of_le_of_ne (hle y) hne
    have : Valued.v (y : v.adicCompletion F) * Valued.v (z : v.adicCompletion F) < 1 :=
      mul_lt_one_of_lt_of_le hlt (hle z)
    rw [h1] at this; exact lt_irrefl _ this
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := hval_unit x hu
    rw [hx] at this
    exact absurd this (by decide)
  · by_contra hcon
    push Not at hcon
    have ha : Valued.v (a : v.adicCompletion F) < 1 := lt_of_le_of_ne (hle a) (fun h => hcon.1 (hunit a h))
    have hb : Valued.v (b : v.adicCompletion F) < 1 := lt_of_le_of_ne (hle b) (fun h => hcon.2 (hunit b h))
    have hprod : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F) =
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      rw [← map_mul, ← Subring.coe_mul, ← hab]; exact hx
    have ha0 : Valued.v (a : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h, zero_mul] at hprod; exact WithZero.zero_ne_coe hprod
    have hb0 : Valued.v (b : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h, mul_zero] at hprod; exact WithZero.zero_ne_coe hprod
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 ha0
    obtain ⟨n, hn⟩ := WithZero.ne_zero_iff_exists.1 hb0
    rw [← hm] at ha hprod; rw [← hn] at hb hprod
    rw [← WithZero.coe_mul, WithZero.coe_inj] at hprod
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at ha hb
    have h1 : Multiplicative.toAdd m < 0 := ha
    have h2 : Multiplicative.toAdd n < 0 := hb
    have h3 : Multiplicative.toAdd m + Multiplicative.toAdd n = -1 := by
      rw [← toAdd_mul, hprod]; rfl
    omega

end Completion

end Formalism.IndefR.Fin.HCount
