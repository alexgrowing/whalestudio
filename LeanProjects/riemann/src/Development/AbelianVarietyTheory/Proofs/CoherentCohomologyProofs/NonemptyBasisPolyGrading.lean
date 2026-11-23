import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HomologyRestrictScalarsBijective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexExactAtOfMonomialBasis
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TopClassSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMonomialBasisCechCubePolynomialGrading
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexPolyGradingFiniteExact

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial

noncomputable section

namespace GlobalTheory.ProjCoh

section Top

variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]

def topCech (A : Cube.{0} ι R) {N : ℕ} (hN : Fintype.card ι = N + 1) :
    A.obj Finset.univ →ₗ[R] (cechComplex A).homology N :=
  cechClass A N ∘ₗ (CubeTop.topTerm A hN).codRestrict _ fun _ =>
    (Cube.subsingleton_term A (p := N + 1 + 1) (by omega)).elim _ _

theorem topCech_surjective (A : Cube.{0} ι R) {N : ℕ} (hN : Fintype.card ι = N + 1) :
    Function.Surjective (topCech A hN) := fun y => by
  obtain ⟨x, rfl⟩ := cechClass_surjective A N y
  obtain ⟨z, hz⟩ := CubeTop.topTerm_surjective A hN x.1
  exact ⟨z, congrArg (cechClass A N) (Subtype.ext hz)⟩

theorem topCech_zero_bijective (A : Cube.{0} ι R) (hN : Fintype.card ι = 0 + 1) :
    Function.Bijective (topCech A hN) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, topCech_surjective A hN⟩
  have h := congrFun (congrArg Subtype.val ((cechClass_zero_eq_zero_iff A _).1 hx))
    ⟨Finset.univ, hN⟩
  exact (Cube.res_self A _ x).symm.trans h

theorem topCech_eq_zero_iff (A : Cube.{0} ι R) {N : ℕ} (hN : Fintype.card ι = N + 1 + 1)
    (x : A.obj Finset.univ) :
    topCech A hN x = 0 ↔ ∃ y, Cube.d A (N + 1) y = CubeTop.topTerm A hN x :=
  cechClass_succ_eq_zero_iff A N _

theorem exists_basis_top {κ : Type} (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) {N : ℕ} (hN : Fintype.card ι = N + 1 + 1) :
    ∃ c : Module.Basis {a : κ // T a = Finset.univ} R ((cechComplex A).homology (N + 1)),
      ∀ a, c a = topCech A hN (b Finset.univ ⟨a.1, Finset.subset_univ _⟩) := by
  classical
  let j : {a : κ // T a = Finset.univ} → {a : κ // T a ⊆ Finset.univ} :=
    fun a => ⟨a.1, Finset.subset_univ _⟩
  have hj : Function.Injective j := fun a a' h => Subtype.ext (congrArg (·.1) h)
  have h0 : ∀ (a) (i : ι) (x : A.obj (Finset.univ.erase i)),
      (b Finset.univ).coord (j a) (Cube.res A (Finset.erase_subset i _) x) = 0 := fun a i x => by
    have : (b Finset.univ).coord (j a) ∘ₗ Cube.res A (Finset.erase_subset i _) = 0 :=
      (b _).ext fun a' => by
        rw [LinearMap.comp_apply, hb, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_of_ne, LinearMap.zero_apply]
        intro e
        have h1 := a'.2
        rw [← show a.1 = a'.1 from congrArg (·.1) e, a.2] at h1
        simpa using h1 (Finset.mem_univ i)
    exact congr($this x)
  have hli : LinearIndependent R (topCech A hN ∘ (b Finset.univ ∘ j)) := by
    refine ((b Finset.univ).linearIndependent.comp j hj).map (Submodule.disjoint_def.2 ?_)
    intro z hz hz'
    obtain ⟨y, hy⟩ := (topCech_eq_zero_iff A hN z).1 hz'
    have e := congrFun hy ⟨Finset.univ, hN⟩
    rw [Cube.d_apply] at e
    replace e := e.trans (Cube.res_self A _ z)
    rw [Set.range_comp, Module.Basis.mem_span_image] at hz
    refine (b _).ext_elem fun a => ?_
    rw [map_zero, Finsupp.zero_apply]
    by_contra ha
    obtain ⟨a, rfl⟩ := hz (Finsupp.mem_support_iff.2 ha)
    refine ha ?_
    rw [← Module.Basis.coord_apply, ← e, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_zsmul, h0, smul_zero]
  refine ⟨Module.Basis.mk hli ?_, fun a => Module.Basis.mk_apply _ _ a⟩
  rw [← LinearMap.range_eq_top.2 (topCech_surjective A hN), LinearMap.range_eq_map,
    ← (b Finset.univ).span_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  by_cases h : T a.1 = Finset.univ
  · exact Submodule.subset_span ⟨⟨a.1, h⟩, rfl⟩
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ T a.1 := by
      simpa [Finset.eq_univ_iff_forall] using h
    have := (topCech_eq_zero_iff A hN _).2 (CubeTop.topTerm_res_mem A hN i
      (b _ ⟨a.1, Finset.subset_erase.2 ⟨Finset.subset_univ _, hi⟩⟩))
    rw [hb] at this
    rw [this]
    exact zero_mem _

end Top

section Count

theorem card_natVec (N : ℕ) (hN : 1 ≤ N) (m : ℤ) :
    Nat.card {a : Fin (N + 1) → ℕ // ∑ i, (a i : ℤ) = m} = (m + N).toNat.choose N := by
  rcases lt_or_ge m 0 with h | h
  · have : IsEmpty {a : Fin (N + 1) → ℕ // ∑ i, (a i : ℤ) = m} := ⟨fun a =>
      absurd (a.2 ▸ Finset.sum_nonneg fun i _ => Int.natCast_nonneg (a.1 i)) h.not_ge⟩
    rw [Nat.card_of_isEmpty, Nat.choose_eq_zero_of_lt (by omega)]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun a => ∑ i, a i = m) fun a => by
      norm_cast), ← Nat.card_congr (Sym.equivNatSumOfFintype _ m), Nat.card_eq_fintype_card,
      Sym.card_sym_eq_choose, Fintype.card_fin, show ((m : ℤ) + N).toNat = m + N by omega,
      show N + 1 + m - 1 = m + N by omega, Nat.choose_symm_add]

abbrev NegExp (N : ℕ) (n : ℤ) : Type := {a : Fin (N + 1) → ℤ // ∑ i, a i = n ∧ ∀ i, a i < 0}

def negExpEquiv (N : ℕ) (n : ℤ) :
    NegExp N n ≃ {a : Fin (N + 1) → ℕ // ∑ i, (a i : ℤ) = -n - (N + 1)} where
  toFun a := ⟨fun i => (-a.1 i - 1).toNat, by
    rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (a := -a.1 i - 1)
      (by have := a.2.2 i; omega)]
    simp [Finset.sum_sub_distrib, a.2.1]⟩
  invFun a := ⟨fun i => -(a.1 i : ℤ) - 1, by simp [Finset.sum_sub_distrib, a.2],
    fun i => show -(a.1 i : ℤ) - 1 < 0 by omega⟩
  left_inv a := Subtype.ext (funext fun i => by have := a.2.2 i; simp only; omega)
  right_inv a := Subtype.ext (funext fun i => by simp)

theorem card_negExp (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    Nat.card (NegExp N n) = (-n - 1).toNat.choose N := by
  rw [Nat.card_congr (negExpEquiv N n), card_natVec N hN]
  congr 2
  ring

instance finite_negExp (N : ℕ) (n : ℤ) : Finite (NegExp N n) := by
  have := (finite_neg_sum_eq (Fin (N + 1)) n).to_subtype
  refine Finite.of_injective (β := {a : {a : Fin (N + 1) → ℤ // ∑ i, a i = n} |
      Finset.univ.filter (fun i => a.1 i < 0) = Finset.univ})
    (fun a => ⟨⟨a.1, a.2.1⟩, Finset.filter_eq_self.2 fun i _ => a.2.2 i⟩) fun a b h => ?_
  exact Subtype.ext (congrArg (·.1.1) h)

theorem isEmpty_negExp (N : ℕ) {n : ℤ} (hn : -(N : ℤ) ≤ n) : IsEmpty (NegExp N n) :=
  ⟨fun a => by
    have h := (negExpEquiv N n a).2
    have : 0 ≤ ∑ i, ((negExpEquiv N n a).1 i : ℤ) :=
      Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
    omega⟩

theorem choose_eq_add (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    Ring.choose (n + N) N = ((n + N).toNat.choose N : ℤ) + (-1) ^ N * (-n - 1).toNat.choose N := by
  rcases lt_or_ge (n + N) 0 with h | h
  · have e := Ring.choose_neg (-(n + N)) N
    rw [neg_neg, show -(n + N) + N - 1 = ((-n - 1).toNat : ℤ) by omega, Ring.choose_natCast] at e
    rw [e, Nat.choose_eq_zero_of_lt (n := (n + N).toNat) (by omega), Units.smul_def,
      Int.coe_negOnePow_natCast]
    simp
  · rw [Nat.choose_eq_zero_of_lt (n := (-n - 1).toNat) (by omega), ← Ring.choose_natCast,
      Int.toNat_of_nonneg h]
    simp

end Count

section Poly

variable (R : Type) [CommRing R] (N : ℕ) (n : ℤ)

theorem nonempty_basis_polyGrading :
    Nonempty (Module.Basis {a : Fin (N + 1) → ℕ // ∑ i, (a i : ℤ) = n} R
      (polyGrading (Fin (N + 1)) R n)) := by
  obtain ⟨b, -⟩ := exists_basis_grCube_polyGrading (Fin (N + 1)) R n
  have h : ∀ a : Fin (N + 1) → ℤ, Finset.univ.filter (fun i => a i < 0) ⊆ ∅ ↔ ∀ i, 0 ≤ a i :=
    fun a => by simp [Finset.filter_eq_empty_iff]
  exact ⟨((b ∅).map (homLocEmptyEquiv (Fin (N + 1)) _ n).symm).reindex
    { toFun := fun a => ⟨fun i => (a.1.1 i).toNat, by
        rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg ((h _).1 a.2 i), a.1.2]⟩
      invFun := fun a => ⟨⟨fun i => a.1 i, a.2⟩, (h _).2 fun i => Int.natCast_nonneg _⟩
      left_inv := fun a => Subtype.ext (Subtype.ext
        (funext fun i => Int.toNat_of_nonneg ((h _).1 a.2 i)))
      right_inv := fun a => rfl }⟩

instance finite_natVec : Finite {a : Fin (N + 1) → ℕ // ∑ i, (a i : ℤ) = n} :=
  Finite.of_equiv _ ((negExpEquiv N (-n - (N + 1))).trans
    (Equiv.subtypeEquivRight fun a => by rw [show -(-n - (N + 1)) - ((N : ℤ) + 1) = n by ring]))

theorem cube_exactAt {p : ℕ} (hp : p ≠ N + 1) :
    (cubeComplex (grCube (Fin (N + 1)) (polyGrading (Fin (N + 1)) R) n)).ExactAt p := by
  obtain ⟨b, hb⟩ := exists_basis_grCube_polyGrading (Fin (N + 1)) R n
  exact cubeComplex_exactAt_of_monomialBasis _ R _ _ _ b hb p (by simpa using hp)

theorem grAug_bijective (hN : 1 ≤ N) :
    Function.Bijective (grAug (Fin (N + 1)) (polyGrading (Fin (N + 1)) R) n) :=
  (grAug_bijective_iff _ n).2 ⟨cube_exactAt R N n (by omega), cube_exactAt R N n (by omega)⟩

theorem isZero_grH_poly {p : ℕ} (h0 : p ≠ 0) (hp : p ≠ N) :
    IsZero (grH (Fin (N + 1)) (polyGrading (Fin (N + 1)) R) n p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((cechComplex_exactAt_succ_iff_cube _ q).2 (cube_exactAt R N n (by omega)))

theorem nonempty_basis_grH_top (hN : 1 ≤ N) :
    Nonempty (Module.Basis (NegExp N n) R (grH (Fin (N + 1)) (polyGrading (Fin (N + 1)) R) n N)) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := N) (by omega)
  obtain ⟨b, hb⟩ := exists_basis_grCube_polyGrading (Fin (N + 1 + 1)) R n
  obtain ⟨c, -⟩ := exists_basis_top _ _ b hb (N := N) (Fintype.card_fin _)
  exact ⟨c.reindex
    { toFun := fun a => ⟨a.1.1, a.1.2, fun i => Finset.filter_eq_self.1 a.2 i (Finset.mem_univ i)⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, Finset.filter_eq_self.2 fun i _ => a.2.2 i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }⟩

theorem nonempty_grH_zero_equiv :
    Nonempty (grH (Fin (0 + 1)) (polyGrading (Fin (0 + 1)) R) n 0 ≃ₗ[R] R) := by
  obtain ⟨b, -⟩ := exists_basis_grCube_polyGrading (Fin (0 + 1)) R n
  let u : Unique {a : {a : Fin (0 + 1) → ℤ // ∑ i, a i = n} //
      Finset.univ.filter (fun i => a.1 i < 0) ⊆ Finset.univ} :=
    { default := ⟨⟨fun _ => n, by simp⟩, Finset.subset_univ _⟩
      uniq := fun a => Subtype.ext (Subtype.ext (funext fun i => by
        obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
        simpa using a.1.2)) }
  exact ⟨(LinearEquiv.ofBijective _ (topCech_zero_bijective _ (Fintype.card_fin _))).symm.trans
    ((b Finset.univ).repr.trans (Finsupp.uniqueLinearEquiv R R default))⟩

end Poly

end GlobalTheory.ProjCoh
