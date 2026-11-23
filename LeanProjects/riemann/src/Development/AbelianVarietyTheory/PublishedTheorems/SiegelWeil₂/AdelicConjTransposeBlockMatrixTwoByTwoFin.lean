import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AllHypothesesInhabited

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem submatrix_fromBlocks_mul {R : Type} [CommRing R] (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' = blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrixTwoByTwoFin_injective {R : Type} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R} (h : blk4 a b c d = blk4 a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have := congrArg (fun M => Matrix.submatrix M finSumFinEquiv finSumFinEquiv) h
  simpa [blk4, Matrix.fromBlocks_inj] using this

theorem adelicConjTranspose_blockMatrixTwoByTwoFin (a b c d : Mx D n n) :
    adj (blk4 a b c d : Mx D (n + n) (n + n)) = blk4 (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem JR_Jst : (JR (AF D.host.F) (Jst D n) : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := by
  ext i j
  simp only [JR, Jst, blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;>
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem exists_mat (M N : Mx D (n + n) (n + n)) (h1 : M * N = 1) (h2 : N * M = 1)
    (h : adj M * blk4 0 1 (-1) 0 * M = blk4 0 1 (-1) 0) : ∃ g : G D n, mat g = M :=
  ⟨⟨⟨M, N, h1, h2⟩, by
    change adj M * JR (AF D.host.F) (Jst D n) * M = JR (AF D.host.F) (Jst D n)
    rw [JR_Jst]; exact h⟩, rfl⟩

theorem exists_levi (a : GL (Fin n) (AE D)) : ∃ g : G D n, mat g = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  have h1 : (adj a.1 : Mx D n n) * adj (a⁻¹).1 = 1 := by rw [← adj_mul]; simp [adj_one]
  have h2 : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by rw [← adj_mul]; simp [adj_one]
  refine exists_mat _ (blk4 (a⁻¹).1 0 0 (adj a.1)) ?_ ?_ ?_
  · simp [submatrix_fromBlocks_mul, h2, block_matrix_one, -Matrix.coe_units_inv]
  · simp [submatrix_fromBlocks_mul, h1, block_matrix_one, -Matrix.coe_units_inv]
  · simp [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, h1, adj_zero, adj_adj, -Matrix.coe_units_inv]

theorem exists_unip (b : Mx D n n) : (∃ g : G D n, mat g = blk4 1 b 0 1) ↔ adj b = b := by
  constructor
  · rintro ⟨g, hg⟩
    have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
    rw [JR_Jst, hg] at h
    simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_one, adj_zero, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, mul_neg,
      neg_mul] at h
    exact (neg_add_eq_zero.1 (blockMatrixTwoByTwoFin_injective h).2.2.2).symm
  · intro hb
    refine exists_mat _ (blk4 1 (-b) 0 1) ?_ ?_ ?_
    · simp [submatrix_fromBlocks_mul, block_matrix_one]
    · simp [submatrix_fromBlocks_mul, block_matrix_one]
    · simp [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_zero, adj_one, hb]

theorem exists_weyl : ∃ g : G D n, mat g = blk4 0 1 (-1) 0 := by
  refine exists_mat _ (blk4 0 (-1) 1 0) ?_ ?_ ?_
  · simp [submatrix_fromBlocks_mul, block_matrix_one]
  · simp [submatrix_fromBlocks_mul, block_matrix_one]
  · simp [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_zero, adj_one, adj_neg]

theorem weyl_unip_cube {R : Type} [CommRing R] :
    (blk4 0 1 (-1) 0 * blk4 1 1 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) R) ^ 3 = 1 := by
  simp [pow_succ, submatrix_fromBlocks_mul, block_matrix_one]

theorem isWeilSch_rank_zero (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V : HSp D) (hV : V.rank = 0)
    (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) :
    IsWeilSch ψ 1 θ V μ 1 := by
  have hs : Subsingleton (Mx D V.rank n) := ⟨fun x y => by ext i; exact absurd i.2 (by omega)⟩
  have hi : ∀ x y : Mx D V.rank n, inner V x y = 0 := fun x y => by
    rw [Subsingleton.elim x 0, StdUnn.inner, adj_zero, Matrix.zero_mul]
  have hu : μ Set.univ = 1 := by
    rcases 𝓕.eq_empty_or_nonempty with h | h
    · have := hμ.2.2; simp [h] at this
    · rw [← hμ.2.2, Subsingleton.eq_univ_of_nonempty h]
  refine ⟨fun g a _ Φ x => ?_, fun g b _ Φ x => ?_, fun g _ Φ x => ?_⟩
  · simpa [npow, hV] using congrArg Φ.1 (Subsingleton.elim _ _)
  · simp [hi, halfTr]
  · simp only [hi, Matrix.trace_zero, map_zero, AddChar.map_zero_eq_one, mul_one]
    rw [integral_congr_ae (g := fun _ => Φ.1 x) (.of_forall fun y => by rw [Subsingleton.elim y x])]
    simp [Measure.real, hu]

theorem lower_eq_zero {p : G D n} (hp : p ∈ P D n) (i j : Fin n) :
    mat p (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := by
  have h := (hp (Pi.single (finSumFinEquiv (.inl j)) 1)).1 (by
    ext k
    have : (finSumFinEquiv (Sum.inr k : Fin n ⊕ Fin n)) ≠ finSumFinEquiv (.inl j) := by
      rw [Ne, finSumFinEquiv.apply_eq_iff_eq]; simp
    simp only [LinearMap.funLeft_apply, Pi.single_eq_of_ne this, Pi.zero_apply])
  have h2 := congrFun h i
  simp only [LinearMap.funLeft_apply, Matrix.mulVec_single_one, Pi.zero_apply] at h2
  exact h2

theorem blkA_mul {p q : G D n} (hq : q ∈ P D n) : blkA (mat (p * q)) = blkA (mat p) * blkA (mat q) := by
  ext i j
  have e : mat (p * q) = mat p * mat q := rfl
  simp only [e, blkA, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [lower_eq_zero hq, mul_zero, Finset.sum_const_zero, add_zero]

theorem blkA_one : blkA (mat (1 : G D n)) = 1 := by
  have e : mat (1 : G D n) = 1 := rfl
  rw [e, blkA, Matrix.submatrix_one_equiv, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

def levi : P D n →* GL (Fin n) (AE D) :=
  MonoidHom.toHomUnits ⟨⟨fun p => blkA (mat p.1), blkA_one⟩, fun p q => blkA_mul q.2⟩

theorem continuous_mat : Continuous (mat : G D n → Mx D (n + n) (n + n)) :=
  Units.continuous_val.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous

theorem continuous_levi : Continuous (levi (D := D) (n := n)) := by
  have hA : Continuous fun g : G D n => blkA (mat g) :=
    continuous_matrix fun i j => continuous_mat.matrix_elem _ _
  rw [Units.continuous_iff]
  refine ⟨hA.comp continuous_subtype_val, ?_⟩
  refine (hA.comp (continuous_subtype_val.comp continuous_inv)).congr fun p => ?_
  rw [← map_inv]; rfl

theorem continuous_det : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (AE D) → (AE D)ˣ) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  rw [Units.continuous_iff]
  refine ⟨Units.continuous_val.matrix_det, (Units.continuous_coe_inv.matrix_det).congr fun g => ?_⟩
  rw [← map_inv]; rfl

theorem isCompact_K : IsCompact (K D n : Set (G D n)) :=
  haveI : Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  isCompact_levelAll (isCMExt_host D) _ _ _

theorem isClosed_P : IsClosed (P D n : Set (G D n)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : (P D n : Set (G D n)) = ⋂ x ∈ upperHalf D n, ({g | (mat g).mulVec x ∈ upperHalf D n} ∩
      {g | (mat g⁻¹).mulVec x ∈ upperHalf D n}) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, SetLike.mem_coe]
    refine ⟨fun h x hx => ⟨(h x).1 hx, ((P D n).inv_mem h x).1 hx⟩, fun h x => ⟨fun hx => (h x hx).1, fun hx => ?_⟩⟩
    have := (h _ hx).2
    change (mat g⁻¹).mulVec ((mat g).mulVec x) ∈ _ at this
    rwa [Matrix.mulVec_mulVec, show mat g⁻¹ * mat g = mat (g⁻¹ * g) from rfl, inv_mul_cancel,
      show mat (1 : G D n) = 1 from rfl, Matrix.one_mulVec] at this
  have hU : IsClosed (upperHalf D n : Set (Fin (n + n) → AE D)) :=
    isClosed_eq (f := fun (x : Fin (n + n) → AE D) (i : Fin n) => x (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)))
      (g := fun _ => 0) (continuous_pi fun i => continuous_apply _) continuous_const
  rw [this]
  exact isClosed_biInter fun x _ => (hU.preimage (continuous_mat.matrix_mulVec continuous_const)).inter
    (hU.preimage ((continuous_mat.comp continuous_inv).matrix_mulVec continuous_const))

theorem exists_isHeight : ∃ H : G D n → ℝ≥0, IsHeight H := by
  let δ : P D n →* ℝ≥0 := (absA D).comp (Matrix.GeneralLinearGroup.det.comp levi)
  have hc : Continuous δ := continuous_absE.comp (continuous_det.comp continuous_levi)
  haveI := t2Space_adeleRing' (F := D.host.F)
  have ht := triv_of_isCompact (δ := δ) isClosed_P hc isCompact_K
  refine ⟨iwAbs δ (K D n), fun p hp a ha k hk => ?_⟩
  rw [show a = levi (D := D) (n := n) ⟨p, hp⟩ from Units.ext ha.symm]
  exact iwAbs_mul_of_triv ht ⟨p, hp⟩ hk

theorem data_inhabited (D : D7) : ∃ (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)) (H : G D n → ℝ≥0) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (ν : Measure (GA D V)),
    0 < Formalism.MainNotions.SchurIrreducible.wittIdx V ∧ n < V.rank ∧ V.rank ≤ 2 * n ∧ n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank ∧ IsCharAF D.host.F ψ ∧
      IsHeckeChar D χ ∧ ResEta D χ V.rank ∧ IsInfFam θ ∧ IsCovolOne (ratMx D V.rank n) μ 𝓕 ∧ IsHeight H ∧
      HasRealPar ψ θ l ∧ (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) ∧ ν.IsHaarMeasure := by
  obtain ⟨A, B, h0, h1, h2, h3⟩ := (GlobalTheory.SiegelWeilMiddle.Model.range_inhabited D).1
  obtain ⟨ψ, χ, ω, a, -, -, s, -, -, ν, -, hω, -, -, -, -, hs, -, -, hν, -⟩ :=
    GlobalTheory.SiegelWeilMiddle.Model.all_hypotheses_inhabited D A B
  obtain ⟨θ, hθ⟩ := hω.std.2.1
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.MixModel.exists_isCovolOne D B.rank A.rank
  obtain ⟨H, hH⟩ := exists_isHeight (D := D) (n := A.rank)
  refine ⟨A.rank, B, ψ, χ, θ, μ, 𝓕, H, fun _ => -1, s, ν, h0, h1, h2, h3, hω.std.1, hω.hecT, hω.resT, hθ, hμ, hH,
    fun x => ?_, hs, hν⟩
  rw [hω.std.2.2 θ hθ x]
  congr 1
  simp [Finset.sum_neg_distrib]

end GlobalTheory.StdUnn.Model

end
