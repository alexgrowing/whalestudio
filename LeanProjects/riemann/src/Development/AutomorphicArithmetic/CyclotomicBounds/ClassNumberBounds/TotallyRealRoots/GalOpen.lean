import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDegree

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

private theorem go_finiteDimensional_adjoinRoots {m : ℕ} (hm : 0 < m) :
    FiniteDimensional E (adjoinRoots E m) := by
  classical
  have hfin : {ζ : AlgebraicClosure E | ζ ^ m = 1}.Finite := by
    refine (Polynomial.nthRoots m (1 : AlgebraicClosure E)).toFinset.finite_toSet.subset ?_
    intro ζ hζ
    simpa [Polynomial.mem_nthRoots hm] using hζ
  have : Finite {ζ : AlgebraicClosure E | ζ ^ m = 1} := hfin.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem totient_le_finrank_mul [NumberField E] (n : ℕ) :
    (l ^ n).totient ≤ Module.finrank ℚ E * Module.finrank E (adjoinRoots E (l ^ n)) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have : NeZero ((l ^ n : ℕ) : AlgebraicClosure E) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  have := go_finiteDimensional_adjoinRoots (E := E) hpos
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure E) (l ^ n)
  have hmem : ζ ∈ adjoinRoots E (l ^ n) := IntermediateField.subset_adjoin E _ hζ.pow_eq_one
  have hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : adjoinRoots E (l ^ n)) (l ^ n) :=
    IsPrimitiveRoot.of_map_of_injective (f := (adjoinRoots E (l ^ n)).val) hζ Subtype.val_injective
  have : FiniteDimensional ℚ (adjoinRoots E (l ^ n)) := Module.Finite.trans E _
  rw [Module.finrank_mul_finrank, ← Polynomial.natDegree_cyclotomic (l ^ n) ℚ,
    Polynomial.cyclotomic_eq_minpoly_rat hζ' hpos]
  exact minpoly.natDegree_le _

theorem finiteIndex_of_index_map_le {U : Subgroup ℤ_[l]ˣ} (hU : IsClosed (U : Set ℤ_[l]ˣ)) {B : ℕ}
    (h : ∀ n, (U.map (redPow l n)).index ≤ B) : U.FiniteIndex := by
  have hl : l.Prime := Fact.out
  have hidx : ∀ n, (U ⊔ princ l n).index = (U.map (redPow l n)).index := by
    intro n
    show (U ⊔ (redPow l n).ker).index = _
    rw [Subgroup.index_map, MonoidHom.range_eq_top.mpr (redPow_surjective n), Subgroup.index_top,
      mul_one]
  have hne : ∀ n, (U ⊔ princ l n).index ≠ 0 := by
    intro n
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
    rw [hidx]
    exact Subgroup.index_ne_zero_of_finite
  have hbdd : BddAbove (Set.range fun n => (U ⊔ princ l n).index) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨n, rfl⟩
    show (U ⊔ princ l n).index ≤ B
    rw [hidx]
    exact h n
  obtain ⟨n₀, hn₀⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  have hmax : ∀ n, (U ⊔ princ l n).index ≤ (U ⊔ princ l n₀).index := by
    intro n
    have hc := le_csSup hbdd ⟨n, rfl⟩
    rw [← hn₀] at hc
    exact hc
  have hstab : ∀ n, n₀ ≤ n → U ⊔ princ l n₀ ≤ U ⊔ princ l n := by
    intro n hn
    have hle : U ⊔ princ l n ≤ U ⊔ princ l n₀ := sup_le_sup_left (princ_anti hn) U
    have hmul := Subgroup.relIndex_mul_index hle
    have h1 : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) = 1 := by
      have hpos : 0 < (U ⊔ princ l n₀).index := Nat.pos_of_ne_zero (hne n₀)
      have hm : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) * (U ⊔ princ l n₀).index
          ≤ 1 * (U ⊔ princ l n₀).index := by
        rw [hmul, one_mul]
        exact hmax n
      have h' := Nat.le_of_mul_le_mul_right hm hpos
      have h0 : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hmul
        exact hne n hmul.symm
      omega
    exact Subgroup.relIndex_eq_one.mp h1
  have hsub : U ⊔ princ l n₀ ≤ U := by
    intro x hx
    apply mem_of_isClosed hU
    intro b
    have hxm : x ∈ U ⊔ princ l (max b n₀) := hstab _ (le_max_right _ _) hx
    obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.mp hxm
    refine ⟨u, hu, ?_⟩
    have hz' : z ∈ princ l b := princ_anti (le_max_left b n₀) hz
    have hz1 : redPow l b z = 1 := MonoidHom.mem_ker.mp hz'
    rw [map_mul, hz1, mul_one]
  have hEq : U ⊔ princ l n₀ = U := le_antisymm hsub le_sup_left
  rw [← hEq]
  exact ⟨hne n₀⟩

theorem isOpen_galImage [NumberField E] : IsOpen (galImage l E : Set ℤ_[l]ˣ) := by
  rw [isOpen_iff_isClosed_finiteIndex]
  refine ⟨isClosed_galImage,
    finiteIndex_of_index_map_le isClosed_galImage (B := Module.finrank ℚ E) fun n => ?_⟩
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hN : 0 < l ^ n := pow_pos hl.pos n
  haveI : FiniteDimensional E (adjoinRoots E (l ^ n)) := go_finiteDimensional_adjoinRoots hN
  have hcard := Subgroup.index_mul_card ((galImage l E).map (redPow l n))
  rw [card_map_redPow_galImage, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at hcard
  have htot := totient_le_finrank_mul (l := l) (E := E) n
  have hpos : 0 < Module.finrank E (adjoinRoots E (l ^ n)) := Module.finrank_pos
  rw [← hcard] at htot
  exact Nat.le_of_mul_le_mul_right htot hpos

end KStar.TotallyRealRoots
