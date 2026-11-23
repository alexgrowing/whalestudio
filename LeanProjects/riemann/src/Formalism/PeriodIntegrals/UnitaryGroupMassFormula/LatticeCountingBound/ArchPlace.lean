import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SepDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.GramLowOf

noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

section LinAlg

variable {K : Type*} [Field K]

theorem ap_factor {n k : ℕ} (δ : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin k) (Fin n) K)
    (h : ∀ w, M *ᵥ w = 0 → δ *ᵥ w = 0) : ∃ X : Matrix (Fin n) (Fin k) K, δ = X * M := by
  have hrow : ∀ i, ∃ t : Fin k → K, ∀ z, (δ *ᵥ z) i = t ⬝ᵥ (M *ᵥ z) := by
    intro i
    let f : (Fin n → K) →ₗ[K] (Fin k → K) := M.mulVecLin
    let g : Module.Dual K (Fin n → K) :=
      { toFun := fun z => (δ *ᵥ z) i
        map_add' := fun x y => by simp [Matrix.mulVec_add]
        map_smul' := fun c x => by simp [Matrix.mulVec_smul] }
    have hg : g ∈ (LinearMap.ker f).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro z hz
      show (δ *ᵥ z) i = 0
      rw [h z (LinearMap.mem_ker.mp hz)]
      rfl
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hg
    obtain ⟨hd, hh⟩ := hg
    refine ⟨fun c => hd (fun j => if c = j then 1 else 0), fun z => ?_⟩
    have h1 : hd (f z) = g z := by
      rw [← hh]
      rfl
    have h2 : hd (M *ᵥ z) = (fun c => hd (fun j => if c = j then 1 else 0)) ⬝ᵥ (M *ᵥ z) := by
      rw [LinearMap.pi_apply_eq_sum_univ hd (M *ᵥ z)]
      simp only [dotProduct, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    exact h1.symm.trans h2
  choose X hX using hrow
  refine ⟨Matrix.of X, ?_⟩
  ext i j
  have := hX i (Pi.single j 1)
  rw [Matrix.dotProduct_mulVec] at this
  simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Pi.single_apply] using this

end LinAlg

section Place

theorem ap_uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  first
    | simp [Formalism.MainNotions.S.uMat]
    | (show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
          (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
       rw [Subgroup.coe_inv, Units.mul_inv])

theorem ap_inUJ {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat g = Formalism.REAL.Jm ε := by
  first
    | exact g.2
    | (have h := g.2
       simpa [Formalism.REAL.UJ, Formalism.REAL.inUJ] using h)

theorem ap_Jm_herm {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

theorem ap_Jm_sq {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

variable (I : Formalism.MainNotions.S.AutInst)

def qM (z : I.GA) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  Formalism.MainNotions.S.uMat (z.1 v)⁻¹ * (I.P v)⁻¹

def phv (v : InfinitePlace I.F) (w : Fin I.n → I.E) : Fin I.n → ℂ := fun i => I.φ v (w i)

def colM (z : I.GA) (v : InfinitePlace I.F) {k : ℕ} (b : Fin k → Fin I.n → I.E) : Matrix (Fin I.n) (Fin k) ℂ :=
  Matrix.of fun i c => PI.LatCountG.coordV I z v (b c) i

theorem ap_coordV (z : I.GA) (v : InfinitePlace I.F) (w : Fin I.n → I.E) :
    PI.LatCountG.coordV I z v w = qM I z v *ᵥ phv I v w := rfl

theorem ap_hP (v : InfinitePlace I.F) : I.P v * (I.P v)⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv (I.P v) ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))

theorem ap_hP' (v : InfinitePlace I.F) : (I.P v)⁻¹ * I.P v = 1 := by
  exact Matrix.nonsing_inv_mul (I.P v) ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))

theorem ap_phv_mulVec (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E) (w : Fin I.n → I.E) :
    phv I v (δ *ᵥ w) = δ.map (I.φ v) *ᵥ phv I v w := by
  funext i
  simp [phv, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem ap_AQ (x y : I.GA) (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E) :
    amat I x y v δ * qM I y v = qM I x v * δ.map (I.φ v) := by
  unfold amat qM
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.MainNotions.S.uMat (y.1 v)), ap_uMat_mul_inv, Matrix.one_mul, ap_hP, Matrix.mul_one]

theorem ap_amat_coord (x y : I.GA) (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E)
    (w : Fin I.n → I.E) :
    amat I x y v δ *ᵥ PI.LatCountG.coordV I y v w = PI.LatCountG.coordV I x v (δ *ᵥ w) := by
  rw [ap_coordV, ap_coordV, Matrix.mulVec_mulVec, ap_AQ, ← Matrix.mulVec_mulVec, ap_phv_mulVec]

theorem ap_gram (z : I.GA) (v : InfinitePlace I.F) {k : ℕ} (b : Fin k → Fin I.n → I.E) :
    PI.LatCountG.gramV I z v b = (colM I z v b)ᴴ * colM I z v b := by
  ext a c
  simp [PI.LatCountG.gramV, colM, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem ap_AC (x y : I.GA) (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E) {k : ℕ}
    (u : Fin k → Fin I.n → I.E) :
    amat I x y v δ * colM I y v u = colM I x v (fun c => δ *ᵥ u c) := by
  ext i c
  simp only [colM, Matrix.of_apply]
  rw [← ap_amat_coord I x y v δ (u c)]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem ap_QJQ (y : I.GA) (v : InfinitePlace I.F) :
    (qM I y v)ᴴ * Formalism.REAL.Jm (I.ε v) * qM I y v = I.J.map (I.φ v) := by
  unfold qM
  rw [Matrix.conjTranspose_mul]
  have hU := ap_inUJ (y.1 v)⁻¹
  have hS := I.P_spec v
  calc ((I.P v)⁻¹)ᴴ * (Formalism.MainNotions.S.uMat (y.1 v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (Formalism.MainNotions.S.uMat (y.1 v)⁻¹ * (I.P v)⁻¹)
      = ((I.P v)⁻¹)ᴴ * ((Formalism.MainNotions.S.uMat (y.1 v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * Formalism.MainNotions.S.uMat (y.1 v)⁻¹) * (I.P v)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ := by rw [hU]
    _ = ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹ := by rw [hS]
    _ = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = I.J.map (I.φ v) := by
        rw [ap_hP]
        simp

theorem ap_pair (y : I.GA) (v : InfinitePlace I.F) (p q : Fin I.n → ℂ) :
    star (qM I y v *ᵥ p) ⬝ᵥ (Formalism.REAL.Jm (I.ε v) *ᵥ (qM I y v *ᵥ q)) =
      star p ⬝ᵥ (I.J.map (I.φ v) *ᵥ q) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ap_QJQ]

theorem ap_star (v : InfinitePlace I.F) (a : I.E) : I.φ v (star a) = star (I.φ v a) := by
  have h := I.cm.cmUnram.2.1 (I.φ v) a
  rw [starRingEnd_apply] at h
  exact h

theorem ap_form (v : InfinitePlace I.F) (w z : Fin I.n → I.E) :
    I.φ v (hf I w z) = star (phv I v w) ⬝ᵥ (I.J.map (I.φ v) *ᵥ phv I v z) := by
  simp only [hf, Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, phv, Pi.star_apply,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, ap_star]
  ring

theorem ap_entry {n k : ℕ} (Y C : Matrix (Fin n) (Fin k) ℂ) (Jm : Matrix (Fin n) (Fin n) ℂ) (a c : Fin k) :
    (Yᴴ * Jm * C) a c = star (fun i => Y i a) ⬝ᵥ (Jm *ᵥ fun i => C i c) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ap_DC (y : I.GA) (v : InfinitePlace I.F) {k : ℕ} (b' u : Fin k → Fin I.n → I.E) :
    (Formalism.REAL.Jm (I.ε v) * colM I y v b')ᴴ * colM I y v u = (pairM I b' u).map (I.φ v) := by
  rw [Matrix.conjTranspose_mul, ap_Jm_herm]
  ext a c
  rw [ap_entry, Matrix.map_apply]
  have e1 : (fun i => colM I y v b' i a) = PI.LatCountG.coordV I y v (b' a) := rfl
  have e2 : (fun i => colM I y v u i c) = PI.LatCountG.coordV I y v (u c) := rfl
  rw [e1, e2, ap_coordV, ap_coordV, ap_pair]
  simp only [pairM, Matrix.of_apply]
  rw [ap_form]

theorem ap_DD (y : I.GA) (v : InfinitePlace I.F) {k : ℕ} (b' : Fin k → Fin I.n → I.E) :
    (Formalism.REAL.Jm (I.ε v) * colM I y v b')ᴴ * (Formalism.REAL.Jm (I.ε v) * colM I y v b') =
      (colM I y v b')ᴴ * colM I y v b' := by
  rw [Matrix.conjTranspose_mul, ap_Jm_herm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.REAL.Jm (I.ε v)), ap_Jm_sq, Matrix.one_mul]

def hM {k : ℕ} (b' : Fin k → Fin I.n → I.E) : Matrix (Fin k) (Fin I.n) I.E :=
  Matrix.of (fun a i => star (b' a i)) * I.J

theorem ap_hM (k : ℕ) (b' : Fin k → Fin I.n → I.E) (w : Fin I.n → I.E) (a : Fin k) :
    (hM I b' *ᵥ w) a = hf I (b' a) w := by
  simp only [hM, hf, Formalism.UG.hform, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.of_apply,
    Finset.sum_mul, starRingEnd_apply]
  first
    | exact Finset.sum_comm
    | rw [Finset.sum_comm]

theorem ap_ker (δ : Matrix (Fin I.n) (Fin I.n) I.E) (k : ℕ) (u b' : Fin k → Fin I.n → I.E)
    (hu : LinearIndependent I.E (fun c => δ *ᵥ u c))
    (hsp : ∀ z, δ *ᵥ z ∈ Submodule.span I.E (Set.range fun c => δ *ᵥ u c))
    (hb : LinearIndependent I.E b') (hperp : ∀ a, PerpKer I δ (b' a)) :
    ∀ w, hM I b' *ᵥ w = 0 → δ *ᵥ w = 0 := by
  intro w hw
  have hle : LinearMap.ker δ.mulVecLin ≤ LinearMap.ker (hM I b').mulVecLin := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    funext a
    rw [Matrix.mulVecLin_apply, ap_hM]
    exact hperp a z hz
  have hrδ : Module.finrank I.E (LinearMap.range δ.mulVecLin) = k := by
    have hr : LinearMap.range δ.mulVecLin = Submodule.span I.E (Set.range fun c => δ *ᵥ u c) := by
      apply le_antisymm
      · rintro _ ⟨z, rfl⟩
        exact hsp z
      · rw [Submodule.span_le]
        rintro _ ⟨c, rfl⟩
        exact ⟨u c, rfl⟩
    rw [hr, finrank_span_eq_card hu, Fintype.card_fin]
  have hrows : LinearIndependent I.E (fun a => hM I b' a) := by
    rw [linearIndependent_iff'] at hb ⊢
    intro s g hg a ha
    have h1 : (∑ j ∈ s, g j • (fun i => star (b' j i))) ᵥ* I.J = 0 := by
      rw [← hg]
      funext i
      simp only [hM, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    have hJ : IsUnit I.J.det := isUnit_iff_ne_zero.mpr I.J_det
    have h2 : (∑ j ∈ s, g j • (fun i => star (b' j i))) = 0 := by
      have := congrArg (fun x => x ᵥ* I.J⁻¹) h1
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJ] using this
    have h3 : ∑ j ∈ s, star (g j) • b' j = 0 := by
      funext i
      have := congrArg star (congrFun h2 i)
      simpa [Finset.sum_apply, star_sum, star_mul'] using this
    have := hb s (fun j => star (g j)) h3 a ha
    simpa using this
  have hrM : Module.finrank I.E (LinearMap.range (hM I b').mulVecLin) = k := by
    have := Matrix.rank_eq_finrank_span_row (hM I b')
    have hrows' : LinearIndependent I.E (hM I b').row := by
      first
        | exact hrows
        | simpa [Matrix.row] using hrows
    rw [finrank_span_eq_card hrows', Fintype.card_fin] at this
    exact this
  have hn1 := LinearMap.finrank_range_add_finrank_ker δ.mulVecLin
  have hn2 := LinearMap.finrank_range_add_finrank_ker (hM I b').mulVecLin
  have heq : LinearMap.ker δ.mulVecLin = LinearMap.ker (hM I b').mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hw' : w ∈ LinearMap.ker (hM I b').mulVecLin := LinearMap.mem_ker.mpr hw
  rw [← heq] at hw'
  exact LinearMap.mem_ker.mp hw'

theorem ap_kernel (x y : I.GA) (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E) (k : ℕ)
    (u b' : Fin k → Fin I.n → I.E)
    (hu : LinearIndependent I.E (fun c => δ *ᵥ u c))
    (hsp : ∀ z, δ *ᵥ z ∈ Submodule.span I.E (Set.range fun c => δ *ᵥ u c))
    (hb : LinearIndependent I.E b') (hperp : ∀ a, PerpKer I δ (b' a)) :
    ∀ z : Fin I.n → ℂ, (Formalism.REAL.Jm (I.ε v) * colM I y v b')ᴴ *ᵥ z = 0 → amat I x y v δ *ᵥ z = 0 := by
  intro z hz
  obtain ⟨X, hX⟩ := ap_factor δ (hM I b') (ap_ker I δ k u b' hu hsp hb hperp)
  set Φ : Matrix (Fin I.n) (Fin k) ℂ := Matrix.of fun j a => I.φ v (b' a j) with hΦ
  have hC : colM I y v b' = qM I y v * Φ := by
    ext j a
    simp only [colM, Matrix.of_apply]
    rw [ap_coordV]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hΦ, phv]
  have hH : (Formalism.REAL.Jm (I.ε v) * colM I y v b')ᴴ * qM I y v = (hM I b').map (I.φ v) := by
    rw [hC, Matrix.conjTranspose_mul, ap_Jm_herm, Matrix.conjTranspose_mul]
    calc Φᴴ * (qM I y v)ᴴ * Formalism.REAL.Jm (I.ε v) * qM I y v
        = Φᴴ * ((qM I y v)ᴴ * Formalism.REAL.Jm (I.ε v) * qM I y v) := by simp only [Matrix.mul_assoc]
      _ = Φᴴ * I.J.map (I.φ v) := by rw [ap_QJQ]
      _ = (hM I b').map (I.φ v) := by
          rw [hM, Matrix.map_mul]
          congr 1
          ext a j
          simp [hΦ, ap_star]
  have hinv : qM I y v * (I.P v * Formalism.MainNotions.S.uMat (y.1 v)) = 1 := by
    unfold qM
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (I.P v)⁻¹, ap_hP', Matrix.one_mul]
    have := ap_uMat_mul_inv (y.1 v)⁻¹
    rwa [inv_inv] at this
  set z' := (I.P v * Formalism.MainNotions.S.uMat (y.1 v)) *ᵥ z with hz'
  have hzz : z = qM I y v *ᵥ z' := by
    rw [hz', Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hM0 : (hM I b').map (I.φ v) *ᵥ z' = 0 := by
    rw [← hH, ← Matrix.mulVec_mulVec, ← hzz]
    exact hz
  have hd0 : δ.map (I.φ v) *ᵥ z' = 0 := by
    rw [hX, Matrix.map_mul, ← Matrix.mulVec_mulVec, hM0, Matrix.mulVec_zero]
  rw [hzz, Matrix.mulVec_mulVec, ap_AQ, ← Matrix.mulVec_mulVec, hd0, Matrix.mulVec_zero]

theorem ap_hs_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : hsN A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold hsN Formalism.REAL.hs
  rw [Real.sq_sqrt (by positivity)]

theorem archimedean_place_exists : ArchPlaceOf := by
  unfold ArchPlaceOf ArchIneq ArchPlace
  intro hA I x y δ k u b' v hu hsp hb hperp
  have hCS : ∀ w : Fin I.n → ℂ, PI.UnitaryGroupMassFormula.LSC.nsq (amat I x y v δ *ᵥ w) ≤
      hsN (amat I x y v δ) ^ 2 * PI.UnitaryGroupMassFormula.LSC.nsq w := by
    intro w
    unfold PI.UnitaryGroupMassFormula.LSC.nsq
    rw [ap_hs_sq, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : ‖(amat I x y v δ *ᵥ w) i‖ ≤ ∑ j, ‖amat I x y v δ i j‖ * ‖w j‖ := by
      simp only [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp [norm_mul]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖amat I x y v δ i j‖) (fun j => ‖w j‖)
    calc ‖(amat I x y v δ *ᵥ w) i‖ ^ 2 ≤ (∑ j, ‖amat I x y v δ i j‖ * ‖w j‖) ^ 2 := by
          nlinarith [h1, norm_nonneg ((amat I x y v δ *ᵥ w) i)]
      _ ≤ (∑ j, ‖amat I x y v δ i j‖ ^ 2) * ∑ j, ‖w j‖ ^ 2 := h2
  have key := hA I.n k (amat I x y v δ) (colM I y v u) (Formalism.REAL.Jm (I.ε v) * colM I y v b')
    (hsN (amat I x y v δ) ^ 2) (sq_nonneg _) hCS (ap_kernel I x y v δ k u b' hu hsp hb hperp)
  rw [ap_AC, ap_DD, ap_DC, ← ap_gram, ← ap_gram, ← pow_mul] at key
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  exact key

end Place

end PI.UnitaryGroupMassFormula.LCG

end
