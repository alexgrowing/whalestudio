import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

variable {K : Type} [CommRing K] {M : ℕ}

def blk (a b : K) (r : Fin M → K) (c d : K) (r' u w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K :=
  Matrix.of (Fin.cons (Fin.cons a (Fin.cons b r))
    (Fin.cons (Fin.cons c (Fin.cons d r')) fun i => Fin.cons (u i) (Fin.cons (w i) (U i))))

def pm (a b : K) (r : Fin M → K) (d : K) (w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K := blk a b r 0 d 0 0 w U

theorem blk_eta (g : Matrix (Fin (M + 2)) (Fin (M + 2)) K) :
    g = blk (g 0 0) (g 0 1) (fun j => g 0 j.succ.succ) (g 1 0) (g 1 1) (fun j => g 1 j.succ.succ)
      (fun i => g i.succ.succ 0) (fun i => g i.succ.succ 1) (Matrix.of fun i j => g i.succ.succ j.succ.succ) := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;> rfl

theorem blk_inj {a b c d a' b' c' d' : K} {r s u w r' s' u' w' : Fin M → K} {U U' : Matrix (Fin M) (Fin M) K}
    (h : blk a b r c d s u w U = blk a' b' r' c' d' s' u' w' U') :
    a = a' ∧ b = b' ∧ r = r' ∧ c = c' ∧ d = d' ∧ s = s' ∧ u = u' ∧ w = w' ∧ U = U' :=
  ⟨congrFun (congrFun h 0) 0, congrFun (congrFun h 0) 1, funext fun j => congrFun (congrFun h 0) j.succ.succ,
    congrFun (congrFun h 1) 0, congrFun (congrFun h 1) 1, funext fun j => congrFun (congrFun h 1) j.succ.succ,
    funext fun i => congrFun (congrFun h i.succ.succ) 0, funext fun i => congrFun (congrFun h i.succ.succ) 1,
    Matrix.ext fun i j => congrFun (congrFun h i.succ.succ) j.succ.succ⟩

theorem blk_mul (a b c d a' b' c' d' : K) (r s u w r' s' u' w' : Fin M → K) (U U' : Matrix (Fin M) (Fin M) K) :
    blk a b r c d s u w U * blk a' b' r' c' d' s' u' w' U' =
      blk (a * a' + b * c' + r ⬝ᵥ u') (a * b' + b * d' + r ⬝ᵥ w') (a • r' + b • s' + r ᵥ* U')
        (c * a' + d * c' + s ⬝ᵥ u') (c * b' + d * d' + s ⬝ᵥ w') (c • r' + d • s' + s ᵥ* U')
        (a' • u + c' • w + U *ᵥ u') (b' • u + d' • w + U *ᵥ w') (vecMulVec u r' + vecMulVec w s' + U * U') := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_succ, dotProduct, vecMul, mulVec, vecMulVec_apply, add_assoc, mul_comm]

theorem pm_mul (a b d a' b' d' : K) (r w r' w' : Fin M → K) (U U' : Matrix (Fin M) (Fin M) K) :
    pm a b r d w U * pm a' b' r' d' w' U' =
      pm (a * a') (a * b' + b * d' + r ⬝ᵥ w') (a • r' + r ᵥ* U') (d * d') (d' • w + U *ᵥ w') (U * U') := by
  simp [pm, blk_mul]

theorem pm_one : pm (1 : K) 0 (0 : Fin M → K) 1 0 1 = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
    simp [pm, blk, Matrix.one_apply, Fin.ext_iff]

theorem blk_map {L : Type} [CommRing L] (φ : K → L) (a b c d : K) (r s u w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    (blk a b r c d s u w U).map φ = blk (φ a) (φ b) (φ ∘ r) (φ c) (φ d) (φ ∘ s) (φ ∘ u) (φ ∘ w) (U.map φ) := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;> rfl

theorem pm_map {L : Type} [CommRing L] (φ : K →+* L) (a b d : K) (r w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    (pm a b r d w U).map φ = pm (φ a) (φ b) (φ ∘ r) (φ d) (φ ∘ w) (U.map φ) := by
  simp only [pm, blk_map, map_zero]
  congr 1 <;> exact funext fun _ => map_zero φ

theorem block_matrix_transpose (a b c d : K) (r s u w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    (blk a b r c d s u w U)ᵀ = blk a c u b d w r s Uᵀ := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;> rfl

theorem hypJ_eq (J : Matrix (Fin M) (Fin M) K) : hypJ J = blk 0 1 0 1 0 0 0 0 J := rfl

theorem hypJ_map {L : Type} [CommRing L] (φ : K →+* L) (J : Matrix (Fin M) (Fin M) K) :
    (hypJ J).map φ = hypJ (J.map φ) := by
  simp only [hypJ_eq, blk_map, map_zero, map_one]
  congr 1 <;> exact funext fun _ => map_zero φ

theorem hform_eq (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (x y : Fin M → K) :
    hform s J x y = ((s ∘ x) ᵥ* J) ⬝ᵥ y := by
  simp only [hform, vecMul, dotProduct, Finset.sum_mul, Function.comp]
  exact Finset.sum_comm

theorem gram_blk (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (a b d : K) (r t w : Fin M → K)
    (U : Matrix (Fin M) (Fin M) K) :
    cT s (blk a b r 0 d t 0 w U) * hypJ J * blk a b r 0 d t 0 w U =
      blk 0 (s a * d) (s a • t) (s d * a) (s d * b + s b * d + ((s ∘ w) ᵥ* J) ⬝ᵥ w)
        (s d • r + s b • t + ((s ∘ w) ᵥ* J) ᵥ* U) (a • (s ∘ t)) (b • (s ∘ t) + d • (s ∘ r) + (cT s U * J) *ᵥ w)
        (vecMulVec (s ∘ t) r + vecMulVec (s ∘ r) t + cT s U * J * U) := by
  have z : (s : K → K) ∘ (0 : Fin M → K) = 0 := funext fun _ => map_zero s
  simp [cT, blk_map, block_matrix_transpose, hypJ_eq, blk_mul, z]

variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)

def nM (w : Fin M → K) (z : K) : Matrix (Fin (M + 2)) (Fin (M + 2)) K := pm 1 z (-((s ∘ w) ᵥ* J)) 1 w 1

variable {s J}

theorem nM_unit (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) {w : Fin M → K} {z : K} (hz : z + s z + hform s J w w = 0) :
    cT s (nM s J w z) * hypJ J * nM s J w z = hypJ J := by
  have e : (s : K → K) ∘ (-((s ∘ w) ᵥ* J)) = -(J *ᵥ w) := by
    funext i
    have : ∀ j, s (J j i) = J i j := fun j => congrFun (congrFun hJ i) j
    simp [vecMul, mulVec, dotProduct, hs, this, mul_comm]
  have z0 : (s : K → K) ∘ (0 : Fin M → K) = 0 := funext fun _ => map_zero s
  rw [hform_eq] at hz
  rw [nM, pm, gram_blk, hypJ_eq, e, z0]
  simp [cT_one, hz]

theorem iM_unit {U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J) :
    cT s (pm 1 0 0 1 0 U) * hypJ J * pm 1 0 0 1 0 U = hypJ J := by
  have z0 : (s : K → K) ∘ (0 : Fin M → K) = 0 := funext fun _ => map_zero s
  rw [pm, gram_blk, hypJ_eq, z0]
  simp [hU]

theorem mM_unit (hs : ∀ x, s (s x) = x) (a : Kˣ) :
    cT s (pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1) * hypJ J * pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 = hypJ J := by
  have z0 : (s : K → K) ∘ (0 : Fin M → K) = 0 := funext fun _ => map_zero s
  rw [pm, gram_blk, hypJ_eq, z0]
  simp [cT_one, hs, ← map_mul]

theorem nM_mul (w w' : Fin M → K) (z z' : K) :
    nM s J w z * nM s J w' z' = nM s J (w + w') (z + z' - hform s J w w') := by
  have e : (s : K → K) ∘ (w + w') = s ∘ w + s ∘ w' := funext fun _ => map_add s _ _
  simp only [nM, pm_mul, hform_eq, e, add_vecMul]
  congr 1 <;> simp <;> ring

theorem iM_nM {U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J) (w : Fin M → K) (z : K) :
    pm 1 0 0 1 0 U * nM s J w z = nM s J (U *ᵥ w) z * pm 1 0 0 1 0 U := by
  have e : (s : K → K) ∘ (U *ᵥ w) = (s ∘ w) ᵥ* cT s U := by
    funext i; simp [vecMul, mulVec, dotProduct, cT, mul_comm]
  simp [nM, pm_mul, e, neg_vecMul, hU]

theorem mM_nM (hs : ∀ x, s (s x) = x) (a : Kˣ) (w : Fin M → K) (z : K) :
    pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 * nM s J w z =
      nM s J (s a • w) (a * s a * z) * pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 := by
  have e : (s : K → K) ∘ (s a • w) = (a : K) • (s ∘ w) := by funext i; simp [hs]
  have h : s a * s (a⁻¹ : Kˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  simp only [nM, pm_mul, e, smul_vecMul]
  congr 1
  · simp
  · simp only [mul_zero, zero_dotProduct, dotProduct_zero, add_zero, zero_add, zero_mul]
    linear_combination (-(a * z)) * h
  · simp
  · simp
  · simp [smul_smul, mul_comm (s (a⁻¹ : Kˣ)), h]

theorem nim (w : Fin M → K) (z a d : K) (U : Matrix (Fin M) (Fin M) K) :
    nM s J w z * pm 1 0 0 1 0 U * pm a 0 0 d 0 1 = pm a (z * d) (-(((s ∘ w) ᵥ* J) ᵥ* U)) d (d • w) U := by
  simp [nM, pm_mul, neg_vecMul]

theorem par_dec (hs : ∀ x, s (s x) = x) {g : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hg : cT s g * hypJ J * g = hypJ J)
    (h0 : ∀ i : Fin (M + 1), g i.succ 0 = 0) :
    ∃ (w : Fin M → K) (z : K) (U : Matrix (Fin M) (Fin M) K) (a : Kˣ), z + s z + hform s J w w = 0 ∧
      cT s U * J * U = J ∧ g = nM s J w z * pm 1 0 0 1 0 U * pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 := by
  have e := blk_eta g
  rw [show g 1 0 = 0 from h0 0, show (fun i : Fin M => g i.succ.succ 0) = 0 from funext fun i => h0 i.succ] at e
  generalize g 0 0 = a, g 0 1 = b, (fun j : Fin M => g 0 j.succ.succ) = r, g 1 1 = d,
    (fun j : Fin M => g 1 j.succ.succ) = t, (fun i : Fin M => g i.succ.succ 1) = w,
    (Matrix.of fun i j : Fin M => g i.succ.succ j.succ.succ) = U at e
  subst e
  rw [gram_blk, hypJ_eq] at hg
  obtain ⟨-, h1, h2, h3, h4, h5, -, -, h6⟩ := blk_inj hg
  have ht : t = 0 := by rw [← one_smul K t, ← h1, mul_comm, mul_smul, h2, smul_zero]
  subst ht
  have z0 : (s : K → K) ∘ (0 : Fin M → K) = 0 := funext fun _ => map_zero s
  have e : (s : K → K) ∘ (s a • w) = a • (s ∘ w) := by funext i; simp [hs]
  refine ⟨s a • w, b * s a, U, ⟨a, s d, by rw [mul_comm, h3], h3⟩, ?_, by simpa [z0] using h6, ?_⟩
  · rw [hform_eq, e, smul_vecMul, smul_dotProduct, dotProduct_smul, map_mul, hs, smul_eq_mul, smul_eq_mul]
    linear_combination (a * s a) * h4 - (b * s a) * h3 - (a * s b) * h1
  · rw [nim, e, smul_vecMul, smul_vecMul]
    simp only [Units.inv_mk, hs, pm]
    congr 1
    · linear_combination (-b) * h1
    · rw [smul_zero, add_zero, add_eq_zero_iff_eq_neg] at h5
      rw [← smul_neg, ← h5, smul_smul, mul_comm, h3, one_smul]
    · rw [smul_smul, mul_comm, h1, one_smul]

def mkU {n : ℕ} (s : K →+* K) {J Ji : Matrix (Fin n) (Fin n) K} (hJ : Ji * J = 1) (g : Matrix (Fin n) (Fin n) K)
    (hg : cT s g * J * g = J) : UJ s J :=
  have h : Ji * cT s g * J * g = 1 := by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s g), hg, hJ]
  ⟨⟨g, Ji * cT s g * J, mul_eq_one_comm.1 h, h⟩, hg⟩

theorem continuous_UJ {n : ℕ} [TopologicalSpace K] [IsTopologicalRing K] {s : K →+* K} (hs : Continuous s)
    {J Ji : Matrix (Fin n) (Fin n) K} (hJ : Ji * J = 1) :
    Topology.IsInducing fun g : UJ s J => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 : Continuous fun g : UJ s J => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_val.comp continuous_subtype_val
  have h2 : Continuous fun g : Matrix (Fin n) (Fin n) K => (g, MulOpposite.op (Ji * cT s g * J)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul (continuous_id.matrix_map hs).matrix_transpose).matrix_mul continuous_const))
  refine Topology.IsInducing.of_comp h1 h2 ?_
  have h3 := (Units.isInducing_embedProduct (M := Matrix (Fin n) (Fin n) K)).comp
    (Topology.IsInducing.subtypeVal (t := (UJ s J : Set (GL (Fin n) K))))
  have e : ((fun g : Matrix (Fin n) (Fin n) K => (g, MulOpposite.op (Ji * cT s g * J))) ∘
      fun g : UJ s J => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      fun g : UJ s J => Units.embedProduct _ (g : GL (Fin n) K) := by
    funext g
    have : g = mkU s hJ _ g.2 := Subtype.ext (Units.ext rfl)
    conv_rhs => rw [this]
    rfl
  rw [e]
  exact h3

end CompanionTheory.PlacePermOperatorBicommutantSpan
