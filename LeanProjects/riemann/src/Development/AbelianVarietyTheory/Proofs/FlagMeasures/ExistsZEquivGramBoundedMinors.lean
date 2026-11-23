import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringOHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentStabilizerOfTerm
open NumberField Module Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.ReducedGram

open NumberField Module Matrix in
open scoped Classical in
private lemma upperUnitriangular_mul_apply_of_le {R : Type} [CommRing R] {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) R) (hA0 : ∀ i j, j < i → A i j = 0) (hA1 : ∀ i, A i i = 1)
    (hB0 : ∀ i j, j < i → B i j = 0) (hB1 : ∀ i, B i i = 1) {i j : Fin N} (h : j ≤ i) :
    (A * B) i j = if i = j then 1 else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · split_ifs with hij
    · subst hij
      rw [hA1, hB1, one_mul]
    · rw [hA1, one_mul]
      exact hB0 i j (lt_of_le_of_ne h (fun e => hij e.symm))
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hki | hik
    · rw [hA0 i k hki, zero_mul]
    · rw [hB0 k j (lt_of_le_of_lt h hik), mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

open NumberField Module Matrix in
open scoped Classical in
private lemma exists_integral_unitriangular_reduction {K : Type} [Field K] [NumberField K]
    (hK : ∀ w : InfinitePlace K, w.IsComplex) {N : ℕ} (V : Matrix (Fin N) (Fin N) K)
    (hV0 : ∀ i j, j < i → V i j = 0) (hV1 : ∀ i, V i i = 1) :
    ∃ m : Matrix (Fin N) (Fin N) (𝓞 K), (∀ i j, j < i → m i j = 0) ∧ (∀ i, m i i = 1) ∧
      ∀ (τ : K →+* ℂ) (i j : Fin N), ‖τ ((V * m.map (fun x : 𝓞 K => (x : K))) i j)‖ ≤
        max 1 (Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ))) := by
  set c := Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) with hc_def
  let φ : K →+* (InfinitePlace K → ℂ) := Pi.ringHom fun w => w.embedding
  let O : Subring (InfinitePlace K → ℂ) := (φ.comp (algebraMap (𝓞 K) K)).range
  let FF : Set (InfinitePlace K → ℂ) := {x | ∀ w, ‖x w‖ ≤ c}
  have hφ : ∀ (x : K) (w : InfinitePlace K), φ x w = w.embedding x := fun _ _ => rfl
  have hcov : ∀ x : InfinitePlace K → ℂ, ∃ a ∈ O, x + a ∈ FF := by
    intro x
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.coveringO_holds K hK (fun w => -x w)
    refine ⟨φ (a : K), ⟨a, rfl⟩, fun w => ?_⟩
    have e : (x + φ (a : K)) w = -(-x w - w.embedding (a : K)) := by
      rw [Pi.add_apply, hφ]
      ring
    rw [e, norm_neg]
    exact ha w
  obtain ⟨n, hn1, hn0, hnO, hnF⟩ := _root_.Formalism.HermitianLatticeCounting.P.unitriangularReduction (InfinitePlace K → ℂ) O FF N (V.map φ) hcov
    (fun i => by simp [hV1]) (fun i j h => by simp [hV0 i j h])
  have hlift : ∀ i j, ∃ a : 𝓞 K, φ (a : K) = n i j := by
    intro i j
    obtain ⟨a, ha⟩ := hnO i j
    exact ⟨a, ha⟩
  choose m₀ hm₀ using hlift
  let m : Matrix (Fin N) (Fin N) (𝓞 K) := Matrix.of m₀
  have hm : ∀ i j, φ (m i j : K) = n i j := hm₀
  have hinj : ∀ a b : 𝓞 K, φ (a : K) = φ (b : K) → a = b := fun a b h =>
    RingOfIntegers.coe_injective (φ.injective h)
  have hm0 : ∀ i j, j < i → m i j = 0 := fun i j h =>
    hinj _ _ (by rw [hm, hn0 i j h]; simp)
  have hm1 : ∀ i, m i i = 1 := fun i => hinj _ _ (by rw [hm, hn1]; simp)
  refine ⟨m, hm0, hm1, ?_⟩
  have hn : n = (m.map (fun x : 𝓞 K => (x : K))).map φ := by
    exact Matrix.ext fun i j => (hm i j).symm
  have hprod : V.map φ * n = (V * m.map (fun x : 𝓞 K => (x : K))).map φ := by
    rw [hn, Matrix.map_mul]
  have key : ∀ (i j : Fin N) (w : InfinitePlace K),
      ‖w.embedding ((V * m.map (fun x : 𝓞 K => (x : K))) i j)‖ ≤ max 1 c := by
    intro i j w
    rcases lt_or_ge i j with hij | hji
    · have h := hnF i j hij w
      rw [hprod, Matrix.map_apply, hφ] at h
      exact le_max_of_le_right h
    · rw [upperUnitriangular_mul_apply_of_le V _ hV0 hV1
        (fun a b h => by simp [hm0 a b h]) (fun a => by simp [hm1 a]) hji]
      split_ifs <;> simp
  intro τ i j
  rw [← InfinitePlace.apply, ← InfinitePlace.norm_embedding_eq]
  exact key i j _

open NumberField Module Matrix in
open scoped Classical in
private lemma det_submatrix_mul_diagonal {R : Type} [CommRing R] {N t : ℕ}
    (X : Matrix (Fin N) (Fin N) R) (s : Fin N → R) (I J : Fin t → Fin N) :
    ((X * diagonal s).submatrix I J).det = (X.submatrix I J).det * ∏ k, s (J k) := by
  have hsub : (X * diagonal s).submatrix I J = X.submatrix I J * diagonal (fun k => s (J k)) := by
    ext a b
    simp [Matrix.mul_diagonal]
  rw [hsub, det_mul, det_diagonal]

open NumberField Module Matrix in
open scoped Classical in

theorem _root_.GlobalTheory.ReducedGram.exists_reduced : ∀ (K : Type) [Field K] [NumberField K],
    (∀ w : InfinitePlace K, w.IsComplex) → ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (p : _root_.Formalism.MainNotions.S.Point K (r + 1)), _root_.Formalism.MainNotions.S.IsInCell (_root_.Formalism.MainNotions.S.ZhatOM Z) p →
    ∃ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) K, _root_.Formalism.MainNotions.S.Lat.ZEquiv Z Z₂ ∧
      ∀ (τ : K →+* ℂ) (t : ℕ) (I J : Fin t → Fin (r + 1)),
        ‖τ (Z₂.submatrix I J).det‖ ≤ 4 ^ (r + 1) * (((r + 1).factorial : ℕ) : ℝ) ^ 2 *
          (Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ))) ^ (2 * (r + 1)) *
          ∏ l ∈ Finset.Icc 1 (r + 1),
            (max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖ * max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖⁻¹) := by
  intro K _ _ hK r Z p hcell
  set c := Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) with hc_def
  have hc : 1 ≤ c := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (finrank ℚ K) := by
      rw [Real.one_le_sqrt]
      exact_mod_cast Module.finrank_pos
    have h2 : (1 : ℝ) ≤ |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) := by
      apply Real.one_le_rpow
      · have hd : discr K ≠ 0 := discr_ne_zero K
        have : (1 : ℤ) ≤ |discr K| := Int.one_le_abs hd
        exact_mod_cast this
      · positivity
    nlinarith
  have hmax : max 1 c = c := max_eq_right hc
  unfold _root_.Formalism.MainNotions.S.IsInCell at hcell
  obtain ⟨L, U, hL, hU, hZ⟩ := hcell
  unfold _root_.Formalism.MainNotions.S.IsLoUni at hL
  unfold _root_.Formalism.MainNotions.S.IsUpUni at hU
  set P := _root_.Formalism.MainNotions.S.ptMat p with hP
  let s : Fin (r + 1) → K := fun b => (-1) ^ (r - (b : ℕ))
  have hss : ∀ b, s b * s b = 1 := by
    intro b
    simp only [s, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hDD : diagonal s * diagonal s = 1 := by
    rw [diagonal_mul_diagonal]
    simp only [hss]
    exact diagonal_one
  have hZD : Z = _root_.Formalism.MainNotions.S.ZhatOM Z * diagonal s := by
    ext a b
    simp only [_root_.Formalism.MainNotions.S.ZhatOM, mul_diagonal, s]
    linear_combination (-Z a b) * hss b
  have hZD' : Z = L * P * U * diagonal s := by
    rw [← hZ]
    exact hZD
  let V := diagonal s * U * diagonal s
  have hVapp : ∀ i j, V i j = s i * U i j * s j := by
    intro i j
    simp [V, mul_diagonal, diagonal_mul]
  have hV0 : ∀ i j, j < i → V i j = 0 := fun i j h => by rw [hVapp, (hU i j).1 h]; ring
  have hV1 : ∀ i, V i i = 1 := fun i => by
    rw [hVapp, (hU i i).2 rfl, mul_one, hss]
  have hZeq : Z = L * (P * diagonal s) * V := by
    rw [hZD']
    calc L * P * U * diagonal s = L * P * (diagonal s * diagonal s) * U * diagonal s := by
          rw [hDD, Matrix.mul_one]
      _ = L * (P * diagonal s) * V := by simp only [V, Matrix.mul_assoc]
  obtain ⟨m, hm0, hm1, hmb⟩ := exists_integral_unitriangular_reduction hK V hV0 hV1
  obtain ⟨m', hm'0, hm'1, hm'b⟩ := exists_integral_unitriangular_reduction hK Lᵀ
    (fun i j h => by rw [transpose_apply]; exact (hL j i).1 h)
    (fun i => by rw [transpose_apply]; exact (hL i i).2 rfl)
  rw [hmax] at hmb hm'b
  let A := m'ᵀ.map (fun x : 𝓞 K => (x : K)) * L
  let B := V * m.map (fun x : 𝓞 K => (x : K))
  let W := P * diagonal s
  refine ⟨A * W * B, ⟨m'ᵀ, m, fun a b h => hm'0 b a h, fun a => hm'1 a, hm0, hm1, ?_⟩, ?_⟩
  · simp only [A, B, W]
    rw [hZeq]
    simp only [Matrix.mul_assoc, transpose_map]
  intro τ t I J
  have hmin : ∀ (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (t : ℕ) (I J : Fin t → Fin (r + 1)),
      ((X.map τ).submatrix I J).det = τ ((X.submatrix I J).det) := by
    intro X t I J
    rw [RingHom.map_det]
    rfl
  have hsign : ∀ (t : ℕ) (J : Fin t → Fin (r + 1)), ‖τ (∏ k, s (J k))‖ = 1 := by
    intro t J
    rw [map_prod, norm_prod]
    simp [s]
  have hA : ∀ i j, ‖(A.map τ) i j‖ ≤ c := by
    intro i j
    have hAt : A = (Lᵀ * m'.map (fun x : 𝓞 K => (x : K)))ᵀ := by
      simp only [A, transpose_mul, transpose_transpose, transpose_map]
    rw [Matrix.map_apply, hAt, transpose_apply]
    exact hm'b τ j i
  have hB : ∀ i j, ‖(B.map τ) i j‖ ≤ c := fun i j => hmb τ i j
  set Pb := ∏ l ∈ Finset.range (r + 1), _root_.GlobalTheory.LoopC.CovTerm.gg2 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE P (l + 1))‖ with hPb
  have hW : ∀ (t : ℕ) (I J : Fin t → Fin (r + 1)), ‖((W.map τ).submatrix I J).det‖ ≤ Pb := by
    intro t I J
    rw [hmin, det_submatrix_mul_diagonal, map_mul, norm_mul, hsign, mul_one, ← hmin]
    exact _root_.GlobalTheory.LoopC.CovTerm.minor_pt_le τ p t I J
  have hbound := _root_.Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.minorBound (r + 1) (A.map τ) (W.map τ) (B.map τ) c Pb hc hA hB hW t I J
  have hlead : ∀ l, ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖ = ‖τ (_root_.Formalism.MainNotions.S.leadMinorE P l)‖ := by
    intro l
    unfold _root_.Formalism.MainNotions.S.leadMinorE
    split_ifs with hl
    · rw [hZD', det_submatrix_mul_diagonal, map_mul, norm_mul, hsign, mul_one,
        _root_.Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant K (r + 1) l hl L P U (fun i => (hL i i).2 rfl) (fun i j h => (hL i j).1 h)
          (fun i => (hU i i).2 rfl) (fun i j h => (hU i j).1 h)]
    · rfl
  have hPbeq : Pb = ∏ l ∈ Finset.Icc 1 (r + 1),
      (max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖ * max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖⁻¹) := by
    rw [hPb, Finset.range_eq_Ico,
      Finset.prod_Ico_add' (fun l => _root_.GlobalTheory.LoopC.CovTerm.gg2 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE P l)‖) 0 (r + 1) 1,
      zero_add, Finset.Ico_add_one_right_eq_Icc]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    rw [hlead]
    rfl
  rw [← hmin, Matrix.map_mul, Matrix.map_mul, ← hPbeq]
  exact hbound

end GlobalTheory.ReducedGram
