import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker.Smooth

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

set_option linter.unusedSectionVars false

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem stepCoeff_mul_right (k : ℕ) (F : AdelicGLn.AdelicGL K n → ℂ) (g h : AdelicGLn.AdelicGL K n) :
    stepCoeff k F (g * h) = stepCoeff k (fun y => F (y * h)) g := by
  simp only [stepCoeff, mul_assoc]

theorem partialCoeff_mul_right (ϕ : AdelicGLn.AdelicGL K n → ℂ) (k : ℕ) (g h : AdelicGLn.AdelicGL K n) :
    partialCoeff ϕ k (g * h) = partialCoeff (fun y => ϕ (y * h)) k g := by
  unfold partialCoeff
  induction n - k generalizing g with
  | zero => rfl
  | succ m ih =>
    simp only [partialWhittakerCoeff]
    rw [stepCoeff_mul_right]
    congr 1
    funext y
    exact ih y

theorem partialCoeff_mul_finEmb {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    {V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hV : ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g) (k : ℕ) (g : AdelicGLn.AdelicGL K n)
    {v : AdelicGLn.FiniteAdelicGL K n} (hv : v ∈ V) :
    partialCoeff ϕ k (g * finEmb K n v) = partialCoeff ϕ k g := by
  rw [partialCoeff_mul_right]
  congr 2
  funext y
  exact hV y v hv

def iterDeriv (k : ℕ) (g : AdelicGLn.AdelicGL K n) (ϕ : AdelicGLn.AdelicGL K n → ℂ) :
    List (Fin k × BIdx K) → AdelicGLn.AdelicGL K n → ℂ
  | [] => ϕ
  | p :: l => rDeriv (dirY k g p) (iterDeriv k g ϕ l)

theorem IsUSmooth.iterDeriv {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ) (k : ℕ)
    (g : AdelicGLn.AdelicGL K n) : ∀ l, IsUSmooth (FourierWhittaker.iterDeriv k g ϕ l)
  | [] => hϕ
  | p :: l => (IsUSmooth.iterDeriv hϕ k g l).rDeriv_smooth _

theorem hasSum_vecCoeff_partialCoeff {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ) {k : ℕ}
    (hk : k < n) (g : AdelicGLn.AdelicGL K n)
    (hfin : ∀ (x : Fin k → 𝔸[K]) (z : Fin k → FiniteAdeleRing (𝓞 K) K),
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        partialCoeff ϕ (k + 1) (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) * g) =
          partialCoeff ϕ (k + 1) (colGL k x * g)) :
    HasSum (vecCoeff fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) (partialCoeff ϕ (k + 1) g) := by
  classical
  set F : List (Fin k × BIdx K) → (Fin k → 𝔸[K]) → ℂ :=
    fun l x => partialCoeff (iterDeriv k g ϕ l) (k + 1) (colGL k x * g)
  have hsm := hϕ.iterDeriv k g
  have hc : ∀ l, Continuous (F l) := fun l =>
    (continuous_partialCoeff (hsm l).continuous _).comp ((continuous_colGL k).mul continuous_const)
  have hper : ∀ l, ∀ ξ ∈ vecLattice K (Fin k), ∀ x, F l (ξ + x) = F l x := by
    intro l ξ hξ x
    obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
    simp only [F]
    rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL (hsm l).left hk]
  have hd : ∀ l p x, HasDerivAt (fun s : ℝ => F l (x + torusPt (Pi.single p s))) (F (p :: l) x) 0 := by
    intro l p x
    have h := hasDerivAt_partialCoeff (hsm l) (dirY k g p) (k + 1) (colGL k x * g)
    have e : (fun s : ℝ => F l (x + torusPt (Pi.single p s))) =
        fun s => partialCoeff (iterDeriv k g ϕ l) (k + 1) (colGL k x * g * oneParam (dirY k g p) s) := by
      funext s
      simp only [F]
      rw [colGL_add, mul_assoc, colGL_torusPt_single_mul k hk, mul_assoc]
    rw [e]
    exact h
  have hsum := summable_vecCoeff_of_deriv F hc hper (fun x z hz => hfin x z hz) hd
  have hip : IsIntegralPeriodic (F []) := ⟨hc [], hper [], fun x z hz => hfin x z hz⟩
  have := hip.hasSum_vecCoeff hsum 0
  simp only [pair_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at this
  convert this using 1
  · rfl
  · show partialCoeff ϕ (k + 1) g = partialCoeff ϕ (k + 1) (colGL k 0 * g)
    rw [colGL_zero, one_mul]

theorem exists_lastRow_eq {k : ℕ} {ξ : Fin k → K} (hξ : ξ ≠ 0) :
    ∃ γ : GL (Fin k) K, Matrix.vecMul (lastVec k) (γ : Matrix (Fin k) (Fin k) K) = ξ := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i, ξ i ≠ 0 := by
    by_contra h; push Not at h; exact hξ (funext h)
  have hk : 0 < k := Fin.pos i0
  set last : Fin k := ⟨k - 1, by omega⟩
  set σ := Equiv.swap i0 last
  set M : Matrix (Fin k) (Fin k) K :=
    Matrix.of fun r c => if r = last then ξ (σ c) else if r = c then 1 else 0
  have hM : M.IsLowerTriangular := by
    intro r c hrc
    have hrc' : r < c := hrc
    have hr : r ≠ last := by
      intro h; subst h; have := c.2; rw [Fin.lt_def] at hrc'; simp [last] at hrc'; omega
    simp only [M, Matrix.of_apply, if_neg hr, if_neg (ne_of_lt hrc')]
  have hdetM : M.det = ξ i0 := by
    rw [Matrix.det_of_isLowerTriangular _ hM, Finset.prod_eq_single last]
    · simp [M, σ]
    · intro r _ hr
      simp [M, hr]
    · simp
  set γM := M.submatrix id σ
  have hdet : γM.det ≠ 0 := by
    rw [Matrix.det_permute', hdetM]
    exact mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]) hi0
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γM hdet, funext fun c => ?_⟩
  rw [vecMul_lastVec _ _ hk]
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, γM, M, last, σ]

def rowCompletion {k : ℕ} (ξ : Fin k → K) : GL (Fin k) K :=
  haveI := Classical.propDecidable (ξ ≠ 0)
  if h : ξ ≠ 0 then (exists_lastRow_eq h).choose else 1

theorem vecMul_rowCompletion {k : ℕ} {ξ : Fin k → K} (hξ : ξ ≠ 0) :
    Matrix.vecMul (lastVec k) ((rowCompletion ξ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = ξ := by
  unfold rowCompletion
  rw [dif_pos hξ]
  exact (exists_lastRow_eq hξ).choose_spec

theorem partialCoeff_blockGL_eq_of_vecMul_eq {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    (hϕ : IsLeftInvariant ϕ) {k : ℕ} (hk : k ≤ n) {γ γ' : GL (Fin k) K}
    (h : Matrix.vecMul (lastVec k) (γ : Matrix (Fin k) (Fin k) K) =
      Matrix.vecMul (lastVec k) (γ' : Matrix (Fin k) (Fin k) K)) (g : AdelicGLn.AdelicGL K n) :
    partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk γ') * g) =
      partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk γ) * g) := by
  have hl : IsLastRowUnit (((γ' * γ⁻¹ : GL (Fin k) K)) : Matrix (Fin k) (Fin k) K) := by
    unfold IsLastRowUnit
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ← h, Matrix.vecMul_vecMul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  have : γ' = (γ' * γ⁻¹) * γ := by group
  rw [this, map_mul, map_mul, mul_assoc]
  exact partialCoeff_diagonal_blockGL hϕ _ k rfl hk _ (Or.inl hl) _

def scalarGL (k : ℕ) : Kˣ →* GL (Fin k) K := Units.map (Matrix.scalar (Fin k) : K →+* _).toMonoidHom

theorem coe_scalarGL (k : ℕ) (u : Kˣ) :
    ((scalarGL k u : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = Matrix.scalar (Fin k) (u : K) := rfl

theorem matVec_scalar {k : ℕ} (u : K) (x : Fin k → 𝔸[K]) :
    matVec (Matrix.scalar (Fin k) u) x = fun i => algebraMap K 𝔸[K] u * x i := by
  funext i
  rw [matVec_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (Ne.symm hj)]
  · simp

theorem vecMul_scalar {k : ℕ} (ξ : Fin k → K) (u : K) :
    Matrix.vecMul ξ (Matrix.scalar (Fin k) u) = u • ξ := by
  funext c
  simp [Matrix.vecMul, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]

theorem colGL_finiteAdeleInr (k : ℕ) (w : Fin k → FiniteAdeleRing (𝓞 K) K) :
    colGL (n := n) k (fun i => GroundTheory.Global.finiteAdeleInr (w i)) = finEmb K n (colGL k w) := by
  apply (AdelicGLn.prodEquiv K n).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ ?_
  · apply Units.ext
    refine Matrix.ext fun a b => ?_
    rw [AdelicGLn.prodEquiv_apply_fst]
    simp only [colGL, coe_uGL, uMat_apply, colX_apply, Units.val_one, Matrix.one_apply]
    split_ifs <;> rfl
  · apply Units.ext
    refine Matrix.ext fun a b => ?_
    rw [AdelicGLn.prodEquiv_apply_snd]
    simp only [colGL, coe_uGL, uMat_apply, colX_apply]
    split_ifs <;> rfl

theorem finEmb_mul_eq (g : AdelicGLn.AdelicGL K n) (c : AdelicGLn.FiniteAdelicGL K n) :
    finEmb K n c * g = g * finEmb K n ((AdelicGLn.prodEquiv K n g).2⁻¹ * c *
      (AdelicGLn.prodEquiv K n g).2) := by
  have hg : infEmb K n (archPt g) * finEmb K n (AdelicGLn.prodEquiv K n g).2 = g :=
    infEmb_mul_finEmb g
  set a := archPt g
  set f := (AdelicGLn.prodEquiv K n g).2
  rw [← hg, ← mul_assoc, ← infEmb_mul_finEmb_comm, mul_assoc, mul_assoc, ← map_mul, ← map_mul,
    show c * f = f * (f⁻¹ * c * f) by group]

theorem continuous_colGL_fin (k : ℕ) :
    Continuous fun w : Fin k → FiniteAdeleRing (𝓞 K) K => (colGL (n := n) k w : GL (Fin n) _) := by
  have hc : ∀ (a b : Fin n), Continuous fun x : Fin k → FiniteAdeleRing (𝓞 K) K =>
      uMat (colX (n := n) k x) a b := by
    intro a b
    simp only [uMat_apply, colX_apply]
    by_cases h1 : a = b
    · simp only [h1, if_true]; exact continuous_const
    · simp only [h1, if_false]
      by_cases h2 : a < b
      · simp only [h2, dite_true]
        by_cases h3 : b.val = k
        · simp only [h3, dite_true]; exact continuous_apply _
        · simp only [h3, dite_false]; exact continuous_const
      · simp only [h2, dite_false]; exact continuous_const
  refine Units.continuous_iff.2 ⟨continuous_pi fun a => continuous_pi fun b => hc a b, ?_⟩
  have : (fun x : Fin k → FiniteAdeleRing (𝓞 K) K => (((colGL (n := n) k x)⁻¹ : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _)) = fun x => uMat (colX (n := n) k (-x)) := by
    funext x; rw [← colGL_neg]; rfl
  rw [this]
  exact continuous_pi fun a => continuous_pi fun b => (hc a b).comp continuous_neg

theorem exists_integer_colGL_mem (k : ℕ) (V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n))
    (f : AdelicGLn.FiniteAdelicGL K n) :
    ∃ δ : 𝓞 K, δ ≠ 0 ∧ ∀ z : Fin k → FiniteAdeleRing (𝓞 K) K,
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        f⁻¹ * colGL k (fun i => algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K δ) *
          z i) * f ∈ V := by
  set Θ : (Fin k → FiniteAdeleRing (𝓞 K) K) → AdelicGLn.FiniteAdelicGL K n :=
    fun w => f⁻¹ * colGL k w * f
  have hΘ : Continuous Θ := (continuous_const.mul (continuous_colGL_fin k)).mul continuous_const
  have h0 : Θ 0 = 1 := by simp [Θ, colGL_zero]
  have hW : Θ ⁻¹' (V : Set _) ∈ 𝓝 (0 : Fin k → FiniteAdeleRing (𝓞 K) K) :=
    hΘ.continuousAt.preimage_mem_nhds (by rw [h0]; exact V.isOpen.mem_nhds (one_mem V))
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hIt⟩ := hW
  have hU : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := Filter.iInter_mem.2 ht
  obtain ⟨δ, hδ, hδU⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hU
  refine ⟨δ, hδ, fun z hz => hIt fun i _ => ?_⟩
  exact Set.mem_iInter.1 (hδU (z i) (hz i)) i

theorem hasSum_partialCoeff_of_vecCoeff_zero {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ)
    {k : ℕ} (hk : k < n)
    (hcusp : ∀ g, vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 = 0)
    (g : AdelicGLn.AdelicGL K n) :
    HasSum (fun ξ : {ξ : Fin k → K // ξ ≠ 0} =>
        partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le (rowCompletion ξ.1)) * g))
      (partialCoeff ϕ (k + 1) g) := by
  classical
  obtain ⟨V, hV⟩ := hϕ.fin
  obtain ⟨δ, hδ, hδV⟩ := exists_integer_colGL_mem (n := n) k V (AdelicGLn.prodEquiv K n g).2
  have hδK : (algebraMap (𝓞 K) K δ) ≠ 0 := by
    simpa using (RingOfIntegers.coe_ne_zero_iff).2 hδ
  set u : Kˣ := Units.mk0 _ hδK
  have hconj : ∀ w : Fin k → 𝔸[K], colGL k w * AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) =
      AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) *
        colGL k (fun i => algebraMap K 𝔸[K] u * w i) := by
    intro w
    rw [diagonal_blockGL, colGL_mul_blockGL hk, mulVec_map_inv, ← map_inv, inv_inv, coe_scalarGL,
      matVec_scalar]
  have hfin : ∀ (x : Fin k → 𝔸[K]) (z : Fin k → FiniteAdeleRing (𝓞 K) K),
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        partialCoeff ϕ (k + 1) (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) *
          (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g)) =
          partialCoeff ϕ (k + 1) (colGL k x *
            (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g)) := by
    intro x z hz
    have e1 : (fun i => algebraMap K 𝔸[K] (u : K) * GroundTheory.Global.finiteAdeleInr (z i)) =
        fun i => GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K)
          (algebraMap (𝓞 K) K δ) * z i) := by
      funext i; rw [GroundTheory.Global.algebraMap_mul_finiteAdeleInr]; rfl
    rw [colGL_add, mul_assoc (colGL k x),
      ← mul_assoc (colGL k fun i => GroundTheory.Global.finiteAdeleInr (z i)), hconj, e1,
      colGL_finiteAdeleInr, mul_assoc (AdelicGLn.diagonal K n _), finEmb_mul_eq, ← mul_assoc,
      ← mul_assoc, partialCoeff_mul_finEmb hV _ _ (hδV z hz), mul_assoc]
  have H := hasSum_vecCoeff_partialCoeff hϕ hk _ hfin
  rw [partialCoeff_succ_diagonal_blockGL hϕ.left hk] at H
  have hsupp : Function.support (vecCoeff fun x => partialCoeff ϕ (k + 1) (colGL k x *
      (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g))) ⊆ {ξ | ξ ≠ 0} := by
    intro ξ hξ
    by_contra h0
    apply hξ
    have : ξ = 0 := by simpa using h0
    rw [this]
    exact hcusp _
  rw [← hasSum_subtype_iff_of_support_subset hsupp] at H
  set e : {ξ : Fin k → K // ξ ≠ 0} ≃ {ξ : Fin k → K // ξ ≠ 0} :=
    { toFun := fun ξ => ⟨(u⁻¹ : Kˣ) • ξ.1, fun h => ξ.2 (by simpa using congrArg ((u : Kˣ) • ·) h)⟩
      invFun := fun ξ => ⟨(u : Kˣ) • ξ.1, fun h => ξ.2 (by simpa using congrArg ((u⁻¹ : Kˣ) • ·) h)⟩
      left_inv := fun ξ => Subtype.ext (by simp)
      right_inv := fun ξ => Subtype.ext (by simp) }
  rw [← e.hasSum_iff]
  refine H.congr_fun fun ξ => ?_
  show partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le (rowCompletion (e ξ).1)) * g) = _
  have h1 := partialCoeff_diagonal_blockGL_eq_vecCoeff hϕ.left hk (rowCompletion ξ.1)
    (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g)
  rw [vecMul_rowCompletion ξ.2] at h1
  rw [Function.comp_apply, ← h1, ← mul_assoc, ← map_mul, ← map_mul]
  refine partialCoeff_blockGL_eq_of_vecMul_eq hϕ.left hk.le ?_ g
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, vecMul_rowCompletion ξ.2, coe_scalarGL, vecMul_scalar,
    vecMul_rowCompletion (e ξ).2]
  rfl

end FourierWhittaker

end

end GroundTheory.Automorphic
