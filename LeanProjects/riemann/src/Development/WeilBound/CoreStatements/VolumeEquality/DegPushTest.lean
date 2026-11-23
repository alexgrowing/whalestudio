import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTestA
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTestB
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree

noncomputable section

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal intNum mixedDiff diffStep)

theorem intNum_perm {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F] (I : Ideal (MvPolynomial (Σ k, ι k) F))
    {n m : ℕ} (a : Fin n → K → ℤ) (b : Fin m → K → ℤ) (h : (List.ofFn a).Perm (List.ofFn b)) : intNum F I a = intNum F I b := by
  have : LeftCommutative (diffStep (K := K)) := ⟨fun x y g => by
    funext z
    simp only [diffStep, sub_right_comm z x y]
    ring⟩
  unfold intNum mixedDiff
  rw [h.foldr_eq]

theorem monoLines_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (l : J → HermLine ι) {d : ℕ}
    (w : Fin d → J) :
    (List.ofFn fun k => (monoLines l (∑ j, Finsupp.single (w j) 1) d k).a).Perm (List.ofFn fun j => (l (w j)).a) := by
  have h1 : Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ) = (List.ofFn w : Multiset J) := by
    rw [map_sum, ← Fin.univ_val_map, Finset.sum_eq_multiset_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    conv_rhs => rw [← Multiset.sum_map_singleton (Multiset.map w Finset.univ.val), Multiset.map_map]
    rfl
  have h2 : (Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList.Perm (List.ofFn w) := by
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, h1]
  have h4 : (List.ofFn fun k => (monoLines l (∑ j, Finsupp.single (w j) 1) d k).a) =
      ((Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList).map fun x => (l x).a := by
    refine List.ext_getElem (by simp) fun i h h' => ?_
    have hi : i < (Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList.length := by simpa using h'
    simp only [List.getElem_ofFn, List.getElem_map, monoLines, dif_pos hi, List.get_eq_getElem]
  rw [h4]
  have h5 := h2.map fun x => (l x).a
  rwa [List.map_ofFn] at h5

theorem monoLines_smooth {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (l : J → HermLine ι)
    (hl : ∀ j, IsSmoothHerm (l j)) (m : J →₀ ℕ) (d : ℕ) (k : Fin d) : IsSmoothHerm (monoLines l m d k) := by
  unfold monoLines
  split_ifs
  · exact hl _
  · exact contDiffOn_const

variable {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)

open Classical in
theorem geoFun_word (hI : PB.Inputs) (w : Fin (dimFl Ψ N) → Ψ × Fin N) :
    M.geoFun (toA (∏ j, X (w j))) * M.δ =
      (intNum ℚ (M.P.map (MvPolynomial.map (Int.castRingHom ℚ))) fun j => M.xdeg (w j) : ℤ) := by
  have h1 : toA (∏ j, X (w j) : RP Ψ N) = basisMonomials (Option (Ψ × Fin N)) ℝ (∑ j, Finsupp.single (some (w j)) 1) := by
    simp only [toA, map_prod, rename_X, coe_basisMonomials]
    rw [monomial_sum_one]
    rfl
  have h2 : (∑ j, Finsupp.single (some (w j)) 1 : Option (Ψ × Fin N) →₀ ℕ).degree = dimFl Ψ N := by
    simp [map_sum]
  have h3 : (∑ j, Finsupp.single (some (w j)) 1 : Option (Ψ × Fin N) →₀ ℕ) none = 0 := by
    simp [Finsupp.finsetSum_apply]
  have hs : ∀ j, IsSmoothHerm (M.line 1 j) := fun j => by
    cases j
    · exact M.A_smooth
    · exact M.x_smooth _ _
  have h4 := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hI.degree M.K M.ι M.P (dimFl Ψ N)
    (monoLines (M.line 1) (∑ j, Finsupp.single (some (w j)) 1) (dimFl Ψ N)) M.arith (monoLines_smooth _ hs _ _)
  have hδ : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.δ_pos.ne'
  rw [h1, RootModel.geoFun, Module.Basis.constr_basis, RootModel.geoMono, if_pos h2, h3, pow_zero, mul_one, div_mul_cancel₀ _ hδ]
  refine h4.trans (congrArg _ ?_)
  refine (intNum_perm _ _ _ (monoLines_perm (M.line 1) fun j => some (w j))).trans ?_
  simp only [RootModel.line, M.x_deg]

open Classical in
theorem geoFun_prod (hI : PB.Inputs) (c : Fin (dimFl Ψ N) → Ψ × Fin N → ℤ) :
    M.geoFun (toA (∏ j, ∑ x, c j x • X x)) * M.δ =
      (intNum ℚ (M.P.map (MvPolynomial.map (Int.castRingHom ℚ))) fun j => ∑ x, c j x • M.xdeg x : ℤ) := by
  obtain ⟨F, hF⟩ := exists_multilinear_gen (P := M.P) M.arith
  rw [← hF, F.map_sum, Fintype.prod_sum]
  have h1 : ∀ w : Fin (dimFl Ψ N) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ((∏ j, c j (w j) : ℤ) : ℝ) • toA (∏ j, X (w j)) := fun w => by
    rw [Finset.prod_smul, Int.cast_smul_eq_zsmul, toA, toA, map_zsmul]
  have h2 : toA (∑ w : Fin (dimFl Ψ N) → Ψ × Fin N, ∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ∑ w : Fin (dimFl Ψ N) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j)) := map_sum (rename some) _ _
  rw [h2, map_sum, Finset.sum_mul, Int.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [h1, map_smul, F.map_smul_univ, smul_eq_mul, smul_eq_mul, mul_assoc, geoFun_word M hI, hF, Int.cast_mul]

theorem test_pointIdeal_rat {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [h : Algebra ℚ Ω]
    (y : (Σ k, ι k) → Ω) : pointIdeal ℚ y = (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) := by
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : h = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalNef.genIdeal_eq y).symm

theorem geoTest : GeoTest := by
  intro hI Ψ _ _ p q M _ n r e hq hn
  have hc : n + r = dimFl Ψ (p + q) := by
    rw [hn, ← count_pairs, ← Fintype.card_congr e, Fintype.card_fin]
  refine ⟨hc, ?_⟩
  have key : ∀ (d : ℕ) (_ : d = dimFl Ψ (p + q)) (c : Fin d → Ψ × Fin (p + q) → ℤ),
      M.geoFun (toA (∏ j, ∑ x, c j x • X x)) * M.δ = inum ℚ M.y fun j => ∑ x, c j x • M.xdeg x := by
    rintro _ rfl c
    rw [inum, test_pointIdeal_rat]
    convert geoFun_prod M hI c
    rfl
  rw [test_factor e hq hn, key _ hc]
  congr 2
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.append_left, sum_muCoef, muDeg]
  · simp only [Fin.append_right, sum_fibCoef, fibDeg]

end SheetDecomposition
