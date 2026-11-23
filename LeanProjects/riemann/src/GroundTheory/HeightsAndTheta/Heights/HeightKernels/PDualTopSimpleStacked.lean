import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSimpleStacked
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedGraph
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassFibreDegree
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineSemipositive
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace TopDualSimpleStacked

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem linForm_stackedDiag (a : T → ℤ) (t : T) :
    linForm (ι := dualBlocks T) (ι₂ := dualBlocks T) (stackedDiag a) ⟨(), t⟩ = C (a t) * X ⟨(), t⟩ := by
  simp [linForm, stackedDiag, apply_ite C, ite_mul, Finset.sum_ite_eq]

theorem graphMap_second (P : Ideal (MRing (dualBlocks T))) (g : (Σ _ : Unit, T) → MRing (dualBlocks T))
    (t : T) : graphMap P g (graphSecond t) = C (Ideal.Quotient.mk P (g ⟨(), t⟩)) * X () := by
  simp [graphMap, graphSecond]

theorem graphMap_first (P : Ideal (MRing (dualBlocks T))) (g : (Σ _ : Unit, T) → MRing (dualBlocks T))
    (c : ℤ) (t : T) : graphMap P g (C c * graphFirst t) = C (Ideal.Quotient.mk P (C c * X ⟨(), t⟩)) := by
  simp [graphMap, graphFirst, map_mul]

theorem C_mul_X_not_mem {P : Ideal (MRing (dualBlocks T))} (hP : P.IsPrime) (hhor : IsHorizontal P)
    {c : ℤ} (hc : c ≠ 0) {t : T} (ht : (X ⟨(), t⟩ : MRing (dualBlocks T)) ∉ P) :
    (C c * X ⟨(), t⟩ : MRing (dualBlocks T)) ∉ P := by
  intro h
  rcases hP.mem_or_mem h with h1 | h1
  · have : c ∈ P.comap (C : ℤ →+* MRing (dualBlocks T)) := h1
    rw [hhor] at this
    exact hc this
  · exact ht h1

theorem second_not_mem {P : Ideal (MRing (dualBlocks T))} (hP : P.IsPrime) (a : T → ℤ) {t : T}
    (h : (C (a t) * X ⟨(), t⟩ : MRing (dualBlocks T)) ∉ P) :
    graphSecond t ∉ graphIdeal P (linForm (stackedDiag a)) := by
  have := hP
  intro hm
  have h0 := RingHom.mem_ker.mp hm
  rw [graphMap_second, linForm_stackedDiag] at h0
  have hne : Ideal.Quotient.mk P (C (a t) * X ⟨(), t⟩) ≠ 0 := fun e => h (Ideal.Quotient.eq_zero_iff_mem.mp e)
  exact mul_ne_zero (fun e => hne (C_eq_zero.mp e)) (X_ne_zero _) h0

theorem first_not_mem {P : Ideal (MRing (dualBlocks T))} (hP : P.IsPrime) (a : T → ℤ) {t : T}
    (h : (C (a t) * X ⟨(), t⟩ : MRing (dualBlocks T)) ∉ P) :
    C (a t) * graphFirst t ∉ graphIdeal P (linForm (stackedDiag a)) := by
  have := hP
  intro hm
  have h0 := RingHom.mem_ker.mp hm
  rw [graphMap_first] at h0
  exact h (Ideal.Quotient.eq_zero_iff_mem.mp (C_eq_zero.mp h0))

theorem minor_mem (P : Ideal (MRing (dualBlocks T))) (a : T → ℤ) (s t : T) :
    graphSecond s * (C (a t) * graphFirst t) - graphSecond t * (C (a s) * graphFirst s) ∈
      graphIdeal P (linForm (stackedDiag a)) := by
  refine RingHom.mem_ker.mpr ?_
  rw [map_sub, map_mul _ (graphSecond s), map_mul _ (graphSecond t), graphMap_second, graphMap_second,
    graphMap_first, graphMap_first, linForm_stackedDiag, linForm_stackedDiag]
  ring

theorem exists_scalar {P : Ideal (MRing (dualBlocks T))} {a : T → ℤ} (ha : ∀ t, a t ≠ 0)
    {z : (Σ k, stackedBlocks T k) → ℂ} (hz : z ∈ mcPts (graphIdeal P (linForm (stackedDiag a)))) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ s, z ⟨Sum.inr (), s⟩ = c * ((a s : ℂ) * z ⟨Sum.inl (), s⟩) := by
  have hmin : ∀ s t, z ⟨Sum.inr (), s⟩ * ((a t : ℂ) * z ⟨Sum.inl (), t⟩) =
      z ⟨Sum.inr (), t⟩ * ((a s : ℂ) * z ⟨Sum.inl (), s⟩) := by
    intro s t
    have h := hz.2 _ (minor_mem P a s t)
    simp only [graphFirst, graphSecond, map_sub, map_mul, map_X, map_C, map_intCast, eval_X, eval_C,
      eq_intCast] at h
    exact sub_eq_zero.mp h
  obtain ⟨t₁, ht₁⟩ := hz.1 (Sum.inl ())
  obtain ⟨t₂, ht₂⟩ := hz.1 (Sum.inr ())
  have hd : (a t₁ : ℂ) * z ⟨Sum.inl (), t₁⟩ ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr (ha t₁)) ht₁
  have hs : ∀ s, z ⟨Sum.inr (), s⟩ =
      z ⟨Sum.inr (), t₁⟩ / ((a t₁ : ℂ) * z ⟨Sum.inl (), t₁⟩) * ((a s : ℂ) * z ⟨Sum.inl (), s⟩) := by
    intro s
    rw [div_mul_eq_mul_div, eq_div_iff hd, hmin s t₁]
  refine ⟨_, fun h0 => ht₂ ?_, hs⟩
  rw [hs t₂, h0, zero_mul]

theorem dualEmbMatrix_mulVec {F F' : HermLattice K i} {b : Module.Basis T ℤ (dualLattice F)}
    {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (v : (K →+* ℂ) × Fin i → ℂ) (t : T) :
    (dualEmbMatrix b).mulVec v t = (a t : ℂ) * (dualEmbMatrix b').mulVec v t := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, dualEmbMatrix, hab t]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [zsmul_eq_mul, map_mul, mul_assoc]

theorem dualLine_h_stacked {F F' : HermLattice K i} {b : Module.Basis T ℤ (dualLattice F)}
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {b' : Module.Basis T ℤ (dualLattice F')} (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b')))
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (w : (Σ _ : Unit, T) → ℂ) :
    (dualLine F.withStdMetric b hb).h (fun p => (a p.2 : ℂ) * w p) = (dualLine F'.withStdMetric b' hb').h w := by
  have hrecF : dualRecover b hb (fun t => (a t : ℂ) * w ⟨(), t⟩) = dualRecover b' hb' (fun t => w ⟨(), t⟩) := by
    unfold dualRecover
    rw [LinearEquiv.symm_apply_eq]
    funext t
    rw [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply, dualEmbMatrix_mulVec hab]
    congr 1
    have := (LinearEquiv.ofBijective (Matrix.mulVecLin (dualEmbMatrix b')) hb').apply_symm_apply
      (fun t => w ⟨(), t⟩)
    rw [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply] at this
    exact (congrFun this t).symm
  have hrec : dualRecover (F := F.withStdMetric) b hb (fun t => (a t : ℂ) * w ⟨(), t⟩) =
      dualRecover (F := F'.withStdMetric) b' hb' (fun t => w ⟨(), t⟩) := hrecF
  show Real.sqrt (dualNormSq (F := F.withStdMetric) b hb fun t => (a t : ℂ) * w ⟨(), t⟩) =
    Real.sqrt (dualNormSq (F := F'.withStdMetric) b' hb' fun t => w ⟨(), t⟩)
  simp only [dualNormSq, hrec]
  rfl

theorem isMultiHomog_X_int {K' : Type} [Fintype K'] [DecidableEq K'] {ι : K' → Type} [∀ k, Fintype (ι k)]
    (k : K') (j : ι k) : IsMultiHomog (X ⟨k, j⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j' : ι k', (⟨k, j⟩ : Σ k, ι k) ≠ ⟨k', j'⟩ := fun j' e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem isMultiHomog_C_mul {K' : Type} [Fintype K'] {ι : K' → Type} [∀ k, Fintype (ι k)] {f : MRing ι}
    {d : K' → ℕ} (hf : IsMultiHomog f d) (c : ℤ) : IsMultiHomog (C c * f) d := by
  intro m hm k
  rw [C_mul'] at hm
  exact hf m (MvPolynomial.support_smul hm) k

theorem degFirst_inl : degFirst (Sum.inl ()) = 1 := by
  rw [degFirst, pullDeg, Sum.inl_injective.extend_apply]

theorem degSecond_inl : degSecond (Sum.inl ()) = 0 := by
  rw [degSecond, pullDeg, Function.extend_apply' _ _ _ (by rintro ⟨u, hu⟩; exact Sum.inr_ne_inl hu)]
  rfl

theorem degFirst_eq (k : Unit ⊕ Unit) : degFirst k = ((Pi.single (Sum.inl ()) 1 : Unit ⊕ Unit → ℕ) k : ℤ) := by
  rcases k with u | u <;> cases u
  · simp [degFirst_inl]
  · simp [degFirst_inr]

theorem degSecond_eq (k : Unit ⊕ Unit) :
    degSecond k = ((Pi.single (Sum.inr ()) 1 : Unit ⊕ Unit → ℕ) k : ℤ) := by
  rcases k with u | u <;> cases u
  · simp [degSecond_inl]
  · simp [degSecond_inr]

open IndefiniteRowSideFullHecke.Inter in

theorem logNorm_eq {F F' : HermLattice K i} {b : Module.Basis T ℤ (dualLattice F)}
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {b' : Module.Basis T ℤ (dualLattice F')} (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b')))
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (ha : ∀ t, a t ≠ 0) (t : T)
    {z : (Σ k, stackedBlocks T k) → ℂ} (hz : z ∈ mcPts (stackedGraph b' a)) :
    logNorm (pullHerm (isBlockMap_inr (ι := dualBlocks T)) (dualLine F.withStdMetric b hb)) (graphSecond t) z =
      logNorm (pullHerm (isBlockMap_inl (ι₂ := dualBlocks T)) (dualLine F'.withStdMetric b' hb'))
        (C (a t) * graphFirst t) z := by
  obtain ⟨c, hc, hcz⟩ := exists_scalar ha hz
  have hN : (pullHerm (isBlockMap_inr (ι := dualBlocks T)) (dualLine F.withStdMetric b hb)).h z =
      ‖c‖ * (pullHerm (isBlockMap_inl (ι₂ := dualBlocks T)) (dualLine F'.withStdMetric b' hb')).h z := by
    show (dualLine F.withStdMetric b hb).h (fun p => z (inrV p)) =
      ‖c‖ * (dualLine F'.withStdMetric b' hb').h (fun p => z (inlV p))
    have hfun : (fun p : Σ _ : Unit, T => z (inrV p)) =
        fun p => (fun _ : Unit => c) p.1 * ((fun q : Σ _ : Unit, T => (a q.2 : ℂ) * z (inlV q)) p) := by
      funext ⟨u, s⟩
      cases u
      exact hcz s
    rw [hfun, (dualLine F.withStdMetric b hb).smul _ _ (fun _ => hc), dualLine_h_stacked hb hb' hab]
    simp [dualLine]
  unfold logNorm
  rw [hN]
  simp only [graphSecond, graphFirst, map_X, map_mul, map_C, map_intCast, eval_X, eval_mul, eval_C, eq_intCast]
  rw [hcz t, norm_mul, mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hc)]

open IndefiniteRowSideFullHecke.Inter in

theorem step (hHor : DualStackedGraphHorizontal.Statement) {F F' : HermLattice K i}
    {b : Module.Basis T ℤ (dualLattice F)} (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {b' : Module.Basis T ℤ (dualLattice F')} (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b')))
    {a : T → ℤ} (hi : 1 ≤ i) (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (ha : ∀ t, a t ≠ 0)
    {II : IntersectionSystem} (hII : IsIntersectionSystem II) {n : ℕ}
    (hΓ : IsArithVar (stackedGraph b' a) (n + 1)) (hprime : (dualIdeal b').IsPrime) {t : T}
    (ht : (C (a t) * X ⟨(), t⟩ : MRing (dualBlocks T)) ∉ dualIdeal b')
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (stackedBlocks T)) (hL : ∀ j, IsSmoothHerm (L j)) :
    II (Unit ⊕ Unit) (stackedBlocks T) (stackedGraph b' a) (n + 1)
        (Fin.snoc L (pullHerm (isBlockMap_inr (ι := dualBlocks T)) (dualLine F.withStdMetric b hb))) -
      II (Unit ⊕ Unit) (stackedBlocks T) (stackedGraph b' a) (n + 1)
        (Fin.snoc L (pullHerm (isBlockMap_inl (ι₂ := dualBlocks T)) (dualLine F'.withStdMetric b' hb'))) =
      vertR (stackedGraph b' a) L (graphSecond t) - vertR (stackedGraph b' a) L (C (a t) * graphFirst t) := by
  classical
  have hR := (hII (Unit ⊕ Unit) (stackedBlocks T)).2.2
  have hv2 : IsBlockMap Sum.inr (inrV (ι := dualBlocks T) (ι₂ := dualBlocks T)) := isBlockMap_inr
  have hv1 : IsBlockMap Sum.inl (inlV (ι := dualBlocks T) (ι₂ := dualBlocks T)) := isBlockMap_inl
  have hNs := Inter.IsPullHerm.isSmoothHerm hv2 (isPullHerm_pullHerm hv2 (dualLine F.withStdMetric b hb))
    (DualLineSemipositive.proof K i F.withStdMetric T b hb).1
  have hMs := Inter.IsPullHerm.isSmoothHerm hv1 (isPullHerm_pullHerm hv1 (dualLine F'.withStdMetric b' hb'))
    (DualLineSemipositive.proof K i F'.withStdMetric T b' hb').1
  have hNa : ∀ k, (pullHerm hv2 (dualLine F.withStdMetric b hb)).a k =
      ((Pi.single (Sum.inr ()) 1 : Unit ⊕ Unit → ℕ) k : ℤ) := degSecond_eq
  have hMa : ∀ k, (pullHerm hv1 (dualLine F'.withStdMetric b' hb')).a k =
      ((Pi.single (Sum.inl ()) 1 : Unit ⊕ Unit → ℕ) k : ℤ) := degFirst_eq
  have hYh : IsMultiHomog (graphSecond t : MRing (stackedBlocks T)) (Pi.single (Sum.inr ()) 1) :=
    isMultiHomog_X_int (ι := stackedBlocks T) (Sum.inr ()) t
  have hXh : IsMultiHomog (C (a t) * graphFirst t : MRing (stackedBlocks T)) (Pi.single (Sum.inl ()) 1) :=
    isMultiHomog_C_mul (isMultiHomog_X_int (ι := stackedBlocks T) (Sum.inl ()) t) _
  have rN := hR (stackedGraph b' a) n L _ (graphSecond t) _ hΓ hL hNs hNa hYh (second_not_mem hprime a ht)
  have rM := hR (stackedGraph b' a) n L _ (C (a t) * graphFirst t) _ hΓ hL hMs hMa hXh
    (first_not_mem hprime a ht)
  rw [recR_eq] at rN rM
  have hint : arInt (stackedGraph b' a) (graphSecond t)
        (pullHerm (isBlockMap_inr (ι := dualBlocks T)) (dualLine F.withStdMetric b hb)) L =
      arInt (stackedGraph b' a) (C (a t) * graphFirst t)
        (pullHerm (isBlockMap_inl (ι₂ := dualBlocks T)) (dualLine F'.withStdMetric b' hb')) L :=
    Inter.ptsIntegral_congr_pts _ _ fun z hz => logNorm_eq hb hb' hab ha t hz
  have hS : (divSupp_finite (stackedGraph b' a) (graphSecond t)).toFinset.filter IsHorizontal =
      (divSupp_finite (stackedGraph b' a) (C (a t) * graphFirst t)).toFinset.filter IsHorizontal := by
    ext W
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h => ⟨((hHor K i F F' T b b' a hi hab t W h.2).1).1 h.1, h.2⟩,
      fun h => ⟨((hHor K i F F' T b b' a hi hab t W h.2).1).2 h.1, h.2⟩⟩
  have hcyc : cycR (II (Unit ⊕ Unit) (stackedBlocks T)) (stackedGraph b' a) L (graphSecond t) -
        vertR (stackedGraph b' a) L (graphSecond t) =
      cycR (II (Unit ⊕ Unit) (stackedBlocks T)) (stackedGraph b' a) L (C (a t) * graphFirst t) -
        vertR (stackedGraph b' a) L (C (a t) * graphFirst t) := by
    rw [Inter.cycR_sub_vertR, Inter.cycR_sub_vertR, hS]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hW
    rw [(hHor K i F F' T b b' a hi hab t W hW.2).2 ((hHor K i F F' T b b' a hi hab t W hW.2).1.2 hW.1)]
  rw [rN, rM, hint]
  linarith

theorem update_comp_swap {α : Type*} {n : ℕ} (L : Fin (n + 1) → α) (j : Fin (n + 1)) (A : α) :
    Function.update L j A ∘ Equiv.swap j (Fin.last n) =
      Fin.snoc (fun m : Fin n => L (Equiv.swap j (Fin.last n) (Fin.castSucc m))) A := by
  funext x
  refine Fin.lastCases ?_ (fun m => ?_) x
  · simp
  · simp only [Function.comp_apply, Fin.snoc_castSucc]
    by_cases h : Fin.castSucc m = j
    · subst h
      rw [Equiv.swap_apply_left, Function.update_of_ne (Fin.castSucc_ne_last m).symm]
    · rw [Equiv.swap_apply_of_ne_of_ne h (Fin.castSucc_ne_last m), Function.update_of_ne h]

def mix {α : Type*} (M N : α) (n k : ℕ) : Fin (n + 1) → α := fun j => if (j : ℕ) < k then N else M

def rest {α : Type*} (M N : α) {n : ℕ} (k : Fin (n + 1)) : Fin n → α :=
  fun m => mix M N n k (Equiv.swap k (Fin.last n) (Fin.castSucc m))

theorem mix_mem {α : Type*} (M N : α) (n k : ℕ) (j : Fin (n + 1)) : mix M N n k j = M ∨ mix M N n k j = N := by
  unfold mix
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem mix_succ {α : Type*} (M N : α) (n : ℕ) (k : Fin (n + 1)) :
    mix M N n ((k : ℕ) + 1) = Function.update (mix M N n k) k N := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp [mix]
  · have hj' : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
    rw [Function.update_of_ne hj]
    simp only [mix]
    congr 1
    exact propext ⟨fun h => by omega, fun h => by omega⟩

theorem mix_self {α : Type*} (M N : α) (n : ℕ) (k : Fin (n + 1)) :
    mix M N n k = Function.update (mix M N n k) k M := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp [mix]
  · rw [Function.update_of_ne hj]

theorem telescope {K' : Type} [Fintype K'] {ι : K' → Type} [∀ k, Fintype (ι k)]
    {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P (n + 1)) {M N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hM : IsSmoothHerm M) (hN : IsSmoothHerm N) :
    I P (n + 1) (fun _ => N) - I P (n + 1) (fun _ => M) =
      ∑ k : Fin (n + 1), (I P (n + 1) (Fin.snoc (rest M N k) N) - I P (n + 1) (Fin.snoc (rest M N k) M)) := by
  have hsm : ∀ (k : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), IsSmoothHerm A → ∀ (j : Fin (n + 1)) (x : Fin (n + 1)),
      IsSmoothHerm (Function.update (mix M N n k) j A x) := by
    intro k A hA j x
    by_cases hx : x = j
    · subst hx; rw [Function.update_self]; exact hA
    · rw [Function.update_of_ne hx]
      rcases mix_mem M N n k x with h | h <;> rw [h]
      · exact hM
      · exact hN
  have hterm : ∀ k : Fin (n + 1),
      I P (n + 1) (mix M N n ((k : ℕ) + 1)) - I P (n + 1) (mix M N n k) =
        I P (n + 1) (Fin.snoc (rest M N k) N) - I P (n + 1) (Fin.snoc (rest M N k) M) := by
    intro k
    have e1 := hI.1 P (n + 1) (Function.update (mix M N n k) k N) (Equiv.swap k (Fin.last n)) hP
      (hsm k N hN k)
    have e2 := hI.1 P (n + 1) (Function.update (mix M N n k) k M) (Equiv.swap k (Fin.last n)) hP
      (hsm k M hM k)
    rw [update_comp_swap] at e1 e2
    have h1 : I P (n + 1) (mix M N n ((k : ℕ) + 1)) = I P (n + 1) (Fin.snoc (rest M N k) N) := by
      rw [mix_succ]
      exact e1.symm
    have h2 : I P (n + 1) (mix M N n k) = I P (n + 1) (Fin.snoc (rest M N k) M) := by
      have h3 : I P (n + 1) (mix M N n k) = I P (n + 1) (Function.update (mix M N n k) k M) := by
        rw [← mix_self]
      rw [h3]
      exact e2.symm
    rw [h1, h2]
  have hN' : mix M N n (n + 1) = fun _ => N := by
    funext j
    simp [mix, j.isLt]
  have hM' : mix M N n 0 = fun _ => M := by
    funext j
    simp [mix]
  rw [← hN', ← hM', ← Finset.sum_range_sub (fun k => I P (n + 1) (mix M N n k)) (n + 1),
    ← Fin.sum_univ_eq_sum_range (fun k => I P (n + 1) (mix M N n (k + 1)) - I P (n + 1) (mix M N n k))]
  exact Finset.sum_congr rfl fun k _ => hterm k

theorem geomDeg_proj_eq_one (hGF : GrassFibreDegree.Statement) {II : IntersectionSystem}
    (hII : IsIntersectionSystem II) (n : ℕ) :
    geomDeg (grassIdeal 1 1 n) (fsMulti (plBlocks 1 1 n)) n = 1 := by
  have hP : IsArithVar (grassIdeal 1 1 n) (n + 1) := by
    have := GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 n le_rfl
    simpa using this
  obtain ⟨h1, h2⟩ := (Inter.Conservation.proof : ConservationStatement) (Fin 1) (plBlocks 1 1 n)
    (II (Fin 1) (plBlocks 1 1 n)) (hII _ _) (grassIdeal 1 1 n) n (fun _ => fsMulti (plBlocks 1 1 n)) 2 hP
    (fun _ => FsLineSmooth.proof _ _) Nat.prime_two
  rw [h1, hGF n 2 Nat.prime_two] at h2
  have hlog : Real.log ((2 : ℕ) : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have : ptsIntegral (grassIdeal 1 1 n) (pot fun _ : Fin n => fsMulti (plBlocks 1 1 n)) (fun _ => 1) = 1 := by
    have h3 : Real.log ((2 : ℕ) : ℝ) * 1 =
        Real.log ((2 : ℕ) : ℝ) * ptsIntegral (grassIdeal 1 1 n) (pot fun _ : Fin n => fsMulti (plBlocks 1 1 n))
          (fun _ => 1) := by rw [mul_one]; exact h2
    exact (mul_left_cancel₀ hlog h3).symm
  exact this

end TopDualSimpleStacked

open TopDualSimpleStacked IndefiniteRowSideFullHecke.Inter in

theorem DualTopSimpleStacked.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hImg : DualStackedGraphImage.Statement) (hHor : DualStackedGraphHorizontal.Statement)
    (hFib : DualStackedGraphFibre.Statement) (hGF : GrassFibreDegree.Statement) :
    DualTopSimpleStacked.Statement := by
  intro K _ _ i F F' T _ _ b hb b' hb' a II hi hII hlt hcov hab
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hP' : IsArithVar (dualIdeal b') (n + 1) :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K (n + 1) F' T b' hi
  have hP : IsArithVar (dualIdeal b) (n + 1) :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K (n + 1) F T b hi
  have hprime : (dualIdeal b').IsPrime := hP'.2.1.1
  have ha : ∀ t, a t ≠ 0 := by
    intro t h0
    apply b.ne_zero t
    apply Subtype.ext
    rw [hab t, h0, zero_smul]
    rfl
  obtain ⟨t₀, ht₀⟩ := hP'.2.1.2.2 ()
  have hlin : (C (a t₀) * X ⟨(), t₀⟩ : MRing (dualBlocks T)) ∉ dualIdeal b' :=
    C_mul_X_not_mem hprime hP'.2.2.1 (ha t₀) ht₀
  have hv1 : IsBlockMap Sum.inl (inlV (ι := dualBlocks T) (ι₂ := dualBlocks T)) := isBlockMap_inl
  have hv2 : IsBlockMap Sum.inr (inrV (ι := dualBlocks T) (ι₂ := dualBlocks T)) := isBlockMap_inr
  have hsm' := (DualLineSemipositive.proof K (n + 1) F'.withStdMetric T b' hb').1
  have hsm := (DualLineSemipositive.proof K (n + 1) F.withStdMetric T b hb).1
  have hMs := Inter.IsPullHerm.isSmoothHerm hv1 (isPullHerm_pullHerm hv1 (dualLine F'.withStdMetric b' hb')) hsm'
  have hNs := Inter.IsPullHerm.isSmoothHerm hv2 (isPullHerm_pullHerm hv2 (dualLine F.withStdMetric b hb)) hsm

  have hform : ∀ q : Σ _ : Unit, T,
      IsMultiHomog (linForm (stackedDiag a) q) ((fun _ _ => 1 : Unit → Unit → ℕ) q.1) := by
    rintro ⟨u, t⟩
    cases u
    rw [linForm_stackedDiag]
    have h := isMultiHomog_C_mul (isMultiHomog_X_int (ι := dualBlocks T) () t) (a t)
    have he : (Pi.single () 1 : Unit → ℕ) = fun _ => 1 := by
      funext u
      cases u
      simp
    rwa [he] at h
  obtain ⟨hΓ, himg, hdeg⟩ := hGr Unit (dualBlocks T) Unit (dualBlocks T) (dualIdeal b') (n + 1)
    (linForm (stackedDiag a)) (fun _ _ => 1) hP' hform
    (fun _ => ⟨t₀, by rw [linForm_stackedDiag]; exact hlin⟩)
  obtain ⟨G'⟩ := Targets.genFibreExists Unit (dualBlocks T) (Unit ⊕ Unit) (stackedBlocks T) Sum.inl inlV _
    (n + 1) isBlockMap_inl hΓ
  obtain ⟨J', hJ', -⟩ := Targets.existsUniqueAll G'.Φ _ (fibreIdx (stackedBlocks T) (Sum.inl : Unit → Unit ⊕ Unit))
  have e1 := hAI3 II hII Unit (dualBlocks T) (Unit ⊕ Unit) (stackedBlocks T) Sum.inl inlV _ (n + 1) G' J'
    (fun _ => dualLine F'.withStdMetric b' hb') (fun _ => pullHerm hv1 (dualLine F'.withStdMetric b' hb'))
    hv1 hΓ (by rw [himg]; exact hP') hJ' (fun _ => hsm') (fun _ => isPullHerm_pullHerm _ _)
  rw [hdeg G' J' hJ', himg] at e1

  obtain ⟨himg2, hdeg2⟩ := hImg K (n + 1) F F' T b b' a hi hab
  obtain ⟨G⟩ := Targets.genFibreExists Unit (dualBlocks T) (Unit ⊕ Unit) (stackedBlocks T) Sum.inr inrV _
    (n + 1) isBlockMap_inr hΓ
  obtain ⟨J, hJ, -⟩ := Targets.existsUniqueAll G.Φ _ (fibreIdx (stackedBlocks T) (Sum.inr : Unit → Unit ⊕ Unit))
  have e2 := hAI3 II hII Unit (dualBlocks T) (Unit ⊕ Unit) (stackedBlocks T) Sum.inr inrV _ (n + 1) G J
    (fun _ => dualLine F.withStdMetric b hb) (fun _ => pullHerm hv2 (dualLine F.withStdMetric b hb))
    hv2 hΓ (by rw [stackedGraph] at himg2; rw [himg2]; exact hP) hJ (fun _ => hsm) (fun _ => isPullHerm_pullHerm _ _)
  rw [stackedGraph] at hdeg2 himg2
  rw [hdeg2 G J hJ, himg2] at e2

  have htel := telescope (hII (Unit ⊕ Unit) (stackedBlocks T)) hΓ hMs hNs
  have hstep : ∀ k : Fin (n + 1),
      II (Unit ⊕ Unit) (stackedBlocks T) (graphIdeal (dualIdeal b') (linForm (stackedDiag a))) (n + 1)
          (Fin.snoc (rest (pullHerm hv1 (dualLine F'.withStdMetric b' hb'))
            (pullHerm hv2 (dualLine F.withStdMetric b hb)) k) (pullHerm hv2 (dualLine F.withStdMetric b hb))) -
        II (Unit ⊕ Unit) (stackedBlocks T) (graphIdeal (dualIdeal b') (linForm (stackedDiag a))) (n + 1)
          (Fin.snoc (rest (pullHerm hv1 (dualLine F'.withStdMetric b' hb'))
            (pullHerm hv2 (dualLine F.withStdMetric b hb)) k) (pullHerm hv1 (dualLine F'.withStdMetric b' hb'))) =
        if k = Fin.last n then -∑ s, Real.log |(a s : ℝ)| else 0 := by
    intro k
    have hL : ∀ m, (rest (pullHerm hv1 (dualLine F'.withStdMetric b' hb'))
        (pullHerm hv2 (dualLine F.withStdMetric b hb)) k m).a = degFirst ∨
        (rest (pullHerm hv1 (dualLine F'.withStdMetric b' hb'))
          (pullHerm hv2 (dualLine F.withStdMetric b hb)) k m).a = degSecond := by
      intro m
      rcases mix_mem (pullHerm hv1 (dualLine F'.withStdMetric b' hb'))
        (pullHerm hv2 (dualLine F.withStdMetric b hb)) n k
          (Equiv.swap k (Fin.last n) (Fin.castSucc m)) with h | h
      · left; simp only [rest, h]; rfl
      · right; simp only [rest, h]; rfl
    have hLs : ∀ m, IsSmoothHerm (rest (pullHerm hv1 (dualLine F'.withStdMetric b' hb'))
        (pullHerm hv2 (dualLine F.withStdMetric b hb)) k m) := by
      intro m
      rcases mix_mem (pullHerm hv1 (dualLine F'.withStdMetric b' hb'))
        (pullHerm hv2 (dualLine F.withStdMetric b hb)) n k
          (Equiv.swap k (Fin.last n) (Fin.castSucc m)) with h | h
      · simp only [rest, h]; exact hMs
      · simp only [rest, h]; exact hNs
    refine (step hHor hb hb' hi hab ha hII hΓ hprime hlin _ hLs).trans ?_
    obtain ⟨hall, hone⟩ := hFib K (n + 1) F F' T b b' a hi hlt hcov hab t₀ _ hL
    split_ifs with hk
    · apply hall
      intro m
      subst hk
      simp only [rest, Equiv.swap_self, Equiv.refl_apply, mix, Fin.coe_castSucc, Fin.val_last]
      have hm : (m : ℕ) < n := by have := m.isLt; omega
      rw [if_pos hm]
      rfl
    · apply hone
      have hkn : (k : ℕ) < n := Fin.val_lt_last hk
      refine ⟨⟨k, hkn⟩, ?_⟩
      have hcs : Fin.castSucc (⟨k, hkn⟩ : Fin n) = k := Fin.ext rfl
      simp only [rest, hcs, Equiv.swap_apply_left, mix, Fin.val_last, lt_irrefl, if_false]
      have : ¬ (n < (k : ℕ)) := by omega
      rw [if_neg this]
      rfl
  rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_ite_eq' Finset.univ (Fin.last n),
    if_pos (Finset.mem_univ _)] at htel
  have hg : geomDeg (grassIdeal 1 1 (n + 1 - 1)) (fsMulti (plBlocks 1 1 (n + 1 - 1))) (1 * 1 * (n + 1 - 1)) = 1 := by
    have h := geomDeg_proj_eq_one hGF hII (n + 1 - 1)
    rwa [show 1 * 1 * (n + 1 - 1) = n + 1 - 1 by ring]
  rw [hg, mul_one]
  push_cast at e1 e2
  linarith

end

end GroundTheory.Heights₂.Heights
