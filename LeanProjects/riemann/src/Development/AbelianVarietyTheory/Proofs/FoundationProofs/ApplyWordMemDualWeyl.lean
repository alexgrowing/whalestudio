import Mathlib
import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.WeylDuality

theorem intQ_apply {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n F = map (Int.castRingHom ℚ) F := rfl

theorem applyWord_mem_dualWeyl (R : Type) [CommRing R] {r n : ℕ} (ν : Fin n → ℕ)
    (w : List (Fin r × Fin r × ℕ)) {F : MvPolynomial (Fin r × Fin n) R} (hF : F ∈ dualWeyl R r n ν) :
    applyWord R w F ∈ dualWeyl R r n ν := by
  induction w with
  | nil => simpa [applyWord] using hF
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    exact rowDivStable R r n ν x.1 x.2.1 x.2.2 _ ih

private theorem rowGen_map_intCast {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    Polynomial.map (MvPolynomial.map φ) (rowGen R a b f) = rowGen S a b (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [rowGen]
  | add p q hp hq => rw [map_add, map_add, Polynomial.map_add, hp, hq, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.map_mul, hp, map_mul, map_mul, map_X]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp

private theorem rowDiv_map_intCast {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (rowDiv R a b k f) = rowDiv S a b k (map φ f) := by
  unfold rowDiv
  rw [← rowGen_map_intCast, Polynomial.coeff_map]

private theorem map_intCast_applyWord {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) ℤ) :
    map (Int.castRingHom ℚ) (applyWord ℤ w f) = applyWord ℚ w (map (Int.castRingHom ℚ) f) := by
  induction w with
  | nil => simp [applyWord]
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [rowDiv_map_intCast, ih]

private theorem map_intCast_hw {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    map (Int.castRingHom ℚ) (hw ℤ hn ν) = hw ℚ hn ν := by
  unfold hw lpMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext p q
  simp

theorem intQ_word {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ)) :
    intQ r n (applyWord ℤ w (hw ℤ hn ν)) = applyWord ℚ w (hw ℚ hn ν) := by
  rw [intQ_apply, map_intCast_applyWord, map_intCast_hw]

theorem eval_idFrame_int {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) ℤ) :
    eval (idFrame ℚ r n) (map (Int.castRingHom ℚ) F) = ((eval (idFrame ℤ r n) F : ℤ) : ℚ) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, Int.cast_add]
  | mul_X p v hp =>
    simp only [map_mul, map_X, eval_X, hp, Int.cast_mul]
    congr 1
    unfold idFrame
    split_ifs <;> simp

theorem fockQ_symm {σ : Type} (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := by
  exact (fockQPos σ f g).1

theorem fockQ_hw_pos {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : 0 < fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by
  exact (fockQPos _ (hw ℚ hn ν) (hw ℚ hn ν)).2 (hwNe ℚ r n hn ν)

def fockB (σ : Type) : LinearMap.BilinForm ℚ (MvPolynomial σ ℚ) :=
  LinearMap.mk₂ ℚ fockQ (fun f f' g => (fockQBilin σ f f' g 1).1)
    (fun c f g => (fockQBilin σ f 0 g c).2)
    (fun f g g' => by rw [fockQ_symm, (fockQBilin σ g g' f 1).1, fockQ_symm g, fockQ_symm g'])
    (fun c f g => by rw [fockQ_symm, (fockQBilin σ g 0 f c).2, fockQ_symm g]; rfl)

theorem fockB_apply {σ : Type} (f g : MvPolynomial σ ℚ) : fockB σ f g = fockQ f g := rfl

theorem mem_bDual {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ))
    (P : MvPolynomial (Fin r × Fin n) ℚ) :
    P ∈ bDual r n hn ν M ↔
      P ∈ dualWeyl ℚ r n ν ∧ ∀ Q ∈ M, ∃ z : ℤ, fockQ P Q = z * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by
  exact Iff.rfl

private theorem fockQ_zero_right {σ : Type} (f : MvPolynomial σ ℚ) : fockQ f 0 = 0 := by
  rw [← fockB_apply, map_zero]

private theorem fockQ_add_right {σ : Type} (f g g' : MvPolynomial σ ℚ) :
    fockQ f (g + g') = fockQ f g + fockQ f g' := by
  rw [← fockB_apply, map_add, fockB_apply, fockB_apply]

private theorem fockQ_smul_right' {σ : Type} (f g : MvPolynomial σ ℚ) (c : ℚ) :
    fockQ f (c • g) = c * fockQ f g := by
  rw [← fockB_apply, map_smul, fockB_apply, smul_eq_mul]

private theorem weight_colW_apply' {r n : ℕ} (e : Fin r × Fin n →₀ ℕ) (s : Fin n) :
    Finsupp.weight (colW r n) e s = ∑ a : Fin r, e (a, s) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [colW, Pi.single_apply]

theorem nablaEqDualWeylOf : NablaEqDualWeylOf := by
  intro hCW hHW hAdj hLT r n hn ν hν
  have hc := fockQ_hw_pos hn ν
  ext P
  rw [mem_bDual]
  constructor
  · rintro ⟨F, hF, rfl⟩
    have hFQ : intQ r n F ∈ dualWeyl ℚ r n ν := by
      rw [intQ_apply]
      exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν F hF
    refine ⟨hFQ, ?_⟩
    rintro Q ⟨G, hG, rfl⟩
    unfold weyl at hG
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      refine ⟨eval (idFrame ℤ r n) (applyWord ℤ (transposeWord w) F), ?_⟩
      rw [intQ_word hn ν w, fockQ_symm (intQ r n F), hAdj,
        hHW r n hn ν hν _ (applyWord_mem_dualWeyl ℚ ν _ hFQ), intQ_apply, ← map_intCast_applyWord,
        eval_idFrame_int]
    | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, fockQ_zero_right]
      simp
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      rw [map_add, fockQ_add_right, ha, hb]
      push_cast
      ring
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨c * a, ?_⟩
      have hcx : intQ r n (c • x) = (c : ℚ) • intQ r n x := by
        rw [map_zsmul]
        exact (Int.cast_smul_eq_zsmul ℚ c _).symm
      rw [hcx, fockQ_smul_right', ha]
      push_cast
      ring
  · rintro ⟨hP, hPQ⟩
    have hhom : IsWeightedHomogeneous (colW r n) P ν := by
      unfold dualWeyl at hP
      exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hP).1
    have hint : ∀ w : List (Fin r × Fin r × ℕ),
        ∃ z : ℤ, fockQ (hw ℚ hn ν) (applyWord ℚ w P) = z * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by
      intro w
      have hmem : applyWord ℚ (transposeWord w) (hw ℚ hn ν) ∈ (weyl ℤ r n hn ν).map (intQ r n) := by
        refine ⟨applyWord ℤ (transposeWord w) (hw ℤ hn ν), ?_, intQ_word hn ν _⟩
        unfold weyl
        exact Submodule.subset_span ⟨_, rfl⟩
      obtain ⟨z, hz⟩ := hPQ _ hmem
      exact ⟨z, by rw [fockQ_symm, hAdj, hz]⟩
    have hcoef : ∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e P = z := by
      intro e he
      by_cases hs : ∀ s : Fin n, ∑ a : Fin r, e (a, s) = ν s
      · obtain ⟨z, hz⟩ := hint (wordOf e)
        refine ⟨z, ?_⟩
        rw [hCW ℚ r n ν P e hhom he hs]
        rw [hHW r n hn ν hν _ (applyWord_mem_dualWeyl ℚ ν _ hP)] at hz
        exact mul_right_cancel₀ hc.ne' hz
      · refine ⟨0, ?_⟩
        by_contra hne
        apply hs
        intro s
        have hwt := hhom (d := e) (by simpa using hne)
        rw [← weight_colW_apply' e s, hwt]
    obtain ⟨Q', hQ'⟩ := hLT r n ν P hP hcoef
    refine ⟨Q', (dualWeylIntRat r n ν Q').mpr ?_, hQ'.symm⟩
    rw [← intQ_apply, ← hQ']
    exact hP

theorem dual_dual_of_isLattice {V : Type} [AddCommGroup V] [Module ℚ V] (B : LinearMap.BilinForm ℚ V)
    (hB : B.Nondegenerate) (hB' : B.IsSymm) (M : Submodule ℤ V) [M.IsLattice ℚ] :
    B.dualSubmodule (B.dualSubmodule M) = M := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  let b' := b.extendOfIsLattice ℚ
  have hrange : (Set.range b' : Set V) = M.subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    funext k
    simp [b']
  have hM : Submodule.span ℤ (Set.range b') = M := by
    rw [hrange, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  rw [← hM]
  exact B.dualSubmodule_dualSubmodule_of_basis hB hB' b'

def normB {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : LinearMap.BilinForm ℚ (dualWeyl ℚ r n ν) :=
  (fockQ (hw ℚ hn ν) (hw ℚ hn ν))⁻¹ • (fockB _).restrict (dualWeyl ℚ r n ν)

theorem normB_apply {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (x y : dualWeyl ℚ r n ν) :
    normB hn ν x y = (fockQ (hw ℚ hn ν) (hw ℚ hn ν))⁻¹ * fockQ x.1 y.1 := rfl

theorem normB_symm {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : (normB hn ν).IsSymm := by
  exact ⟨fun x y => by rw [normB_apply, normB_apply, fockQ_symm x.1]⟩

theorem normB_nondeg {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : (normB hn ν).Nondegenerate := by
  have hc := fockQ_hw_pos hn ν
  have key : ∀ x : dualWeyl ℚ r n ν, normB hn ν x x = 0 → x = 0 := by
    intro x hx
    rw [normB_apply, mul_eq_zero, inv_eq_zero] at hx
    rcases hx with h | h
    · exact absurd h hc.ne'
    · by_contra hne
      have hx0 : (x : MvPolynomial (Fin r × Fin n) ℚ) ≠ 0 := fun h0 => hne (Subtype.ext h0)
      exact ((fockQPos _ x.1 x.1).2 hx0).ne' h
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩

def inV {r n : ℕ} (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)) :
    Submodule ℤ (dualWeyl ℚ r n ν) :=
  M.comap ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ)

theorem mem_inV {r n : ℕ} (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ))
    (x : dualWeyl ℚ r n ν) : x ∈ inV ν M ↔ x.1 ∈ M := by
  exact Iff.rfl

theorem inV_bDual {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ))
    (hM : ∀ Q ∈ M, Q ∈ dualWeyl ℚ r n ν) :
    inV ν (bDual r n hn ν M) = (normB hn ν).dualSubmodule (inV ν M) := by
  have hc := fockQ_hw_pos hn ν
  ext x
  rw [mem_inV, mem_bDual, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · rintro ⟨-, h⟩ y hy
    rw [mem_inV] at hy
    obtain ⟨z, hz⟩ := h y.1 hy
    rw [Submodule.mem_one]
    refine ⟨z, ?_⟩
    rw [normB_apply, hz, algebraMap_int_eq, eq_intCast]
    field_simp
  · intro h
    refine ⟨x.2, fun Q hQ => ?_⟩
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp (h ⟨Q, hM Q hQ⟩ ((mem_inV _ _ _).mpr hQ))
    refine ⟨z, ?_⟩
    rw [normB_apply, algebraMap_int_eq, eq_intCast, eq_inv_mul_iff_mul_eq₀ hc.ne'] at hz
    rw [← hz, mul_comm]

theorem dualWeyl_int_fg (r n : ℕ) (ν : Fin n → ℕ) : (dualWeyl ℤ r n ν).FG := by
  obtain ⟨b, hb, -⟩ := sSBasis ℤ r n ν
  obtain ⟨-, hspan, -⟩ := hb
  have := (sSIdxFinite r n ν).to_subtype
  rw [← hspan]
  exact Submodule.fg_span (Set.finite_range b)

private theorem mem_dualWeyl_rat_of_mem_map_weyl {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∀ P ∈ (weyl ℤ r n hn ν).map (intQ r n), P ∈ dualWeyl ℚ r n ν := by
  rintro P ⟨G, hG, rfl⟩
  rw [intQ_apply]
  exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν G (weylLeDual ℤ r n hn ν hν hG)

theorem weyl_isLattice {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    (inV ν ((weyl ℤ r n hn ν).map (intQ r n))).IsLattice ℚ where
  fg := by
    have hW : (weyl ℤ r n hn ν).FG := by
      have := isNoetherian_of_fg_of_noetherian _ (dualWeyl_int_fg r n ν)
      exact Submodule.FG.of_le_of_isNoetherian (weylLeDual ℤ r n hn ν hν)
    have hsub := mem_dualWeyl_rat_of_mem_map_weyl hn ν hν
    refine Submodule.fg_of_fg_map_injective ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ)
      Subtype.val_injective ?_
    have heq : (inV ν ((weyl ℤ r n hn ν).map (intQ r n))).map
        ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ) = (weyl ℤ r n hn ν).map (intQ r n) := by
      apply le_antisymm
      · exact Submodule.map_comap_le _ _
      · intro P hP
        exact ⟨⟨P, hsub P hP⟩, hP, rfl⟩
    rw [heq]
    exact hW.map _
  span_eq_top := by
    have hsub := mem_dualWeyl_rat_of_mem_map_weyl hn ν hν
    apply Submodule.map_injective_of_injective (f := (dualWeyl ℚ r n ν).subtype) Subtype.val_injective
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    · refine le_trans (le_of_eq (weylEqNablaQ r n hn ν hν).symm) (Submodule.span_le.mpr ?_)
      rintro _ ⟨w, rfl⟩
      apply Submodule.subset_span
      have hmem : applyWord ℚ w (hw ℚ hn ν) ∈ (weyl ℤ r n hn ν).map (intQ r n) := by
        refine ⟨applyWord ℤ w (hw ℤ hn ν), ?_, intQ_word hn ν _⟩
        unfold weyl
        exact Submodule.subset_span ⟨_, rfl⟩
      exact ⟨⟨_, hsub _ hmem⟩, (mem_inV _ _ _).mpr hmem, rfl⟩

private theorem mem_dualWeyl_rat_of_mem_map_intQ {r n : ℕ} (ν : Fin n → ℕ) :
    ∀ P ∈ (dualWeyl ℤ r n ν).map (intQ r n), P ∈ dualWeyl ℚ r n ν := by
  rintro P ⟨G, hG, rfl⟩
  rw [intQ_apply]
  exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν G hG

theorem weylEqDualNablaOf : WeylEqDualNablaOf := by
  intro hN r n hn ν hν
  have := weyl_isLattice hn ν hν
  have hW := mem_dualWeyl_rat_of_mem_map_weyl hn ν hν
  have hD := mem_dualWeyl_rat_of_mem_map_intQ (r := r) ν
  have key : inV ν (bDual r n hn ν ((dualWeyl ℤ r n ν).map (intQ r n))) =
      inV ν ((weyl ℤ r n hn ν).map (intQ r n)) := by
    rw [inV_bDual hn ν _ hD, hN r n hn ν hν, inV_bDual hn ν _ hW]
    exact dual_dual_of_isLattice _ (normB_nondeg hn ν) (normB_symm hn ν) _
  ext P
  constructor
  · intro hP
    have h1 : (⟨P, hW P hP⟩ : dualWeyl ℚ r n ν) ∈ inV ν ((weyl ℤ r n hn ν).map (intQ r n)) :=
      (mem_inV _ _ _).mpr hP
    rw [← key, mem_inV] at h1
    exact h1
  · intro hP
    have h1 : (⟨P, ((mem_bDual hn ν _ P).mp hP).1⟩ : dualWeyl ℚ r n ν) ∈
        inV ν (bDual r n hn ν ((dualWeyl ℤ r n ν).map (intQ r n))) := (mem_inV _ _ _).mpr hP
    rw [key, mem_inV] at h1
    exact h1

theorem weyl_dualities : NablaEqDualWeylOf ∧ WeylEqDualNablaOf := by
  exact ⟨nablaEqDualWeylOf, weylEqDualNablaOf⟩

end GlobalTheory.WeylDuality
