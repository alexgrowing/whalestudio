import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealPlacesIdempotentExtensionAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleTraceZeroNormAdjustRealComponents
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CartanPt

variable {R : Type} [CommRing R] {n : ℕ}

theorem block_matrix_map {S : Type} [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4; rw [← Matrix.fromBlocks_map]; rfl

theorem blkJ_mul : (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
  have h : Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) R) 0 0 (-1) = (-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]
  rw [h]
  change -((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = _
  rw [Matrix.submatrix_one_equiv]

theorem blkJ_transpose : (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0)ᵀ = -blk4 0 1 (-1) 0 := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_one, Matrix.transpose_neg]
  change _ = (-(Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)).submatrix _ _
  rw [Matrix.fromBlocks_neg, neg_zero, neg_neg]

theorem blkJ_map {S : Type} [CommRing S] (f : R →+* S) :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).map f = blk4 0 1 (-1) 0 := by
  rw [block_matrix_map, Matrix.map_zero _ (map_zero f), Matrix.map_one _ (map_zero f) (map_one f),
    Matrix.map_neg _ (map_neg f), Matrix.map_one _ (map_zero f) (map_one f)]

def mixJ (n : ℕ) (a j : R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  a • (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) + j • blk4 0 1 (-1) 0

theorem mixJ_mul (a j a' j' : R) :
    mixJ n a j * mixJ n a' j' = mixJ n (a * a' - j * j') (a * j' + j * a') := by
  simp only [mixJ, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, blkJ_mul]
  module

theorem mixJ_one : mixJ n (1 : R) 0 = 1 := by simp [mixJ]

theorem mixJ_J : mixJ n (0 : R) 1 = blk4 0 1 (-1) 0 := by simp [mixJ]

theorem mixJ_map {S : Type} [CommRing S] (f : R →+* S) (a j : R) :
    (mixJ n a j).map f = mixJ n (f a) (f j) := by
  unfold mixJ
  rw [← blkJ_map f, ← Matrix.map_one f (map_zero f) (map_one f)]
  ext p q
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]

theorem mixJ_transpose (a j : R) : (mixJ n a j)ᵀ = mixJ n a (-j) := by
  simp [mixJ, Matrix.transpose_add, Matrix.transpose_smul, blkJ_transpose]

theorem cT_mixJ (σ : R →+* R) (a j : R) : Formalism.UG.cT σ (mixJ n a j) = mixJ n (σ a) (-σ j) := by
  rw [Formalism.UG.cT, mixJ_map, mixJ_transpose]

theorem phase (A B t : ℂ) (hB : B ≠ 0) (h1 : A * B * conj B = t) (h2 : A * conj A = 4) :
    A * (1 / 2) = t / (‖t‖ : ℂ) := by
  have hA : ‖A‖ = 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖A‖ ^ 2 = 2 ^ 2 := by
      have : ‖A‖ ^ 2 = 4 := by exact_mod_cast h2
      linarith
    exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 h3
  have hn : (‖B‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hB
  have ht : ‖t‖ = 2 * ‖B‖ ^ 2 := by
    rw [← h1, norm_mul, norm_mul, Complex.norm_conj, hA]; ring
  rw [ht, ← h1, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp

theorem four_iff {S : Type} [CommRing S] (f : R →+* S) (z : R) : f (z - 4) = 0 ↔ f z = 4 := by
  rw [map_sub, map_ofNat, sub_eq_zero]

theorem four_left {S : Type} [CommRing S] (f : R →+* S) {e : R} (z : R) (h : f e = 0) : f (e * (z - 4)) = 0 := by
  rw [map_mul, h, zero_mul]

theorem four_right {S : Type} [CommRing S] (f : R →+* S) (e : R) {z : R} (h : f z = 4) : f (e * (z - 4)) = 0 := by
  rw [map_mul, (four_iff f z).2 h, mul_zero]

theorem alg_phase (c : R →+* R) (hc : ∀ z, c (c z) = z) {e h m : R} {u ε : Rˣ} (he : e * e = e) (hce : c e = e)
    (hε : (ε : R) * u * c u = m) (hm : c m = -m) (hh : 2 * h = 1) (h4 : e * (ε * c ε - 4) = 0) :
    e * (e * ε * h) = e * ε * h ∧ (e * ε * h) * (e * ε * h) = -e ∧ c (e * ε * h) = -(e * ε * h) := by
  have hcε : c ε = -(ε : R) := by
    rw [← hε, map_mul, map_mul, hc] at hm
    have hu : IsUnit ((u : R) * c u) := u.isUnit.mul (u.isUnit.map c)
    refine hu.mul_right_cancel ?_
    linear_combination hm
  have hch : c h = h := by
    have := congrArg c hh
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination h * this - c h * hh
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ((ε : R) * h) * he
  · linear_combination ((ε : R) ^ 2 * h ^ 2) * he + (e * ε * h ^ 2) * hcε - h ^ 2 * h4 - e * (2 * h + 1) * hh
  · rw [map_mul, map_mul, hce, hcε, hch]; ring

theorem cx_phase (c : R →+* R) (φ : R →+* ℂ) (hφ : ∀ z, φ (c z) = conj (φ z)) {e h m : R} {u ε : Rˣ} (he : φ e = 1)
    (hε : (ε : R) * u * c u = m) (hh : 2 * h = 1) (h4 : φ (ε * c ε) = 4) :
    φ (e * ε * h) = φ m / (‖φ m‖ : ℂ) := by
  have e1 : φ h = 1 / 2 := by
    have := congrArg φ hh
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination (1 / 2) * this
  rw [map_mul, map_mul, he, one_mul, e1]
  refine phase _ (φ u) _ (u.isUnit.map φ).ne_zero ?_ ?_
  · rw [← hφ, ← map_mul, ← map_mul, hε]
  · rw [← hφ, ← map_mul, h4]

theorem mixJ_real (φ : R →+* ℂ) {e j : R} (he : φ e = 1) :
    (mixJ n (1 - e) j).map φ = φ j • blk4 0 1 (-1) 0 := by
  rw [mixJ_map, map_sub, map_one, he, sub_self, mixJ, zero_smul, zero_add]

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

omit [NumberField F] [NumberField E] in
theorem sigR_sigR (A : Type) [CommRing A] [Algebra F A] (hσ : ∀ x, σ (σ x) = x) (z : A ⊗[F] E) :
    sigR A σ (sigR A σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x =>
    change a ⊗ₜ[F] σ (σ x) = _
    rw [hσ]

omit [NumberField E] in
theorem sigR_compInf (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    sigR w.Completion σ (compInf F E w z) = compInf F E w (sigR (AF F) σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a x => rfl

omit [NumberField F] [NumberField E] in
theorem incl_half [CharZero E] (A : Type) [CommRing A] [Algebra F A] : 2 * inclR (F := F) (E := E) A (1 / 2) = 1 := by
  rw [← map_ofNat (inclR (F := F) (E := E) A) 2, ← map_mul]
  norm_num

theorem exists_point (n : ℕ) {e j : AF F ⊗[F] E} (hee : e * e = e) (hej : e * j = j) (hjj : j * j = -e)
    (hce : sigR (AF F) σ e = e) (hcj : sigR (AF F) σ j = -j) (hef : ∀ v, compFin F E v e = 0) :
    ∃ k ∈ levelAll σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) (stdLattice E (n + n)) 1,
      (AdelicU.matHom _ σ _ k).1 = mixJ n (1 - e) j := by
  have hkk : mixJ n (1 - e) j * mixJ n (1 - e) j = 1 := by
    rw [mixJ_mul, ← mixJ_one]
    congr 1
    · linear_combination hee - hjj
    · linear_combination (-2) * hej
  have hcT : Formalism.UG.cT (sigR (AF F) σ) (mixJ n (1 - e) j) = mixJ n (1 - e) j := by
    rw [cT_mixJ, map_sub, map_one, hce, hcj, neg_neg]
  let kU : GL (Fin (n + n)) (AF F ⊗[F] E) := ⟨mixJ n (1 - e) j, mixJ n (1 - e) j, hkk, hkk⟩
  have hmem : kU ∈ HR (AF F) σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) := by
    change Formalism.UG.cT (sigR (AF F) σ) (mixJ n (1 - e) j) * (blk4 0 1 (-1) 0).map (inclR (AF F)) * mixJ n (1 - e) j =
      (blk4 0 1 (-1) 0).map (inclR (AF F))
    rw [hcT, blkJ_map, ← mixJ_J, mixJ_mul, mixJ_mul]
    congr 1
    · linear_combination 2 * hej
    · linear_combination hee - hjj
  let k : GAd σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) := (⟨kU, hmem⟩ : HR (AF F) σ _)
  refine ⟨k, mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩, rfl⟩
  · have h : (AdelicU.matHom _ σ _ (proj σ _ v k)).1 = 1 := by
      change (mixJ n (1 - e) j).map (compFin F E v) = 1
      rw [mixJ_map, map_sub, map_one, hef, sub_zero, ← hej, map_mul, hef, zero_mul, mixJ_one]
    refine mem_stabLoc.2 fun y => ?_
    rw [h, Matrix.one_mulVec]
  · rw [mem_stabArch, map_one, inv_one, one_mul, mul_one]
    change Formalism.UG.cT (sigR w.Completion σ) ((mixJ n (1 - e) j).map (compInf F E w)) * 1 *
      (mixJ n (1 - e) j).map (compInf F E w) = 1
    rw [Matrix.mul_one]
    nth_rewrite 1 [mixJ_map]
    rw [cT_mixJ, sigR_compInf, sigR_compInf, hcj, map_neg, neg_neg, map_sub (sigR (AF F) σ), map_one, hce,
      ← mixJ_map, ← Matrix.map_mul, hkk, Matrix.map_one _ (map_zero _) (map_one _)]

end Adelic

theorem real_four (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (z : AE D)
    (hz : ∀ w, compInf D.host.F D.host.E w z = 4) (τ : D.what₂.Tau) : ((θ τ).comp (infPart D)) z = 4 :=
  (four_iff ((θ τ).comp (infPart D)) z).1
    (((GlobalTheory.StdUnn.RealComp.real_components D θ hθ).1 (z - 4)).1
      (fun w => (four_iff (compInf D.host.F D.host.E w) z).2 (hz w)) τ)

theorem idem_four (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) {e z : AE D} (he : finPart D e = 0)
    (hz : ∀ τ, ((θ τ).comp (infPart D)) z = 4) : e * (z - 4) = 0 :=
  (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _
    (fun τ => four_right ((θ τ).comp (infPart D)) e (hz τ)) (four_left (finPart D) z he)

theorem cA_skew (D : D7) (μ : D.host.E) (hμ : IsSkew μ) : cA D (incA D μ) = -incA D μ :=
  (show cA D (incA D μ) = incA D (star μ) from rfl).trans ((congrArg (incA D) hμ.2).trans ((incA D).map_neg μ))

theorem cA_cA (D : D7) (z : AE D) : cA D (cA D z) = z := sigR_sigR D.sp.cm.sig _ (fun x => star_star x) z

theorem exists_phase_adele (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (μ : D.host.E) (hμ : IsSkew μ) :
    ∃ e j : AE D, e * e = e ∧ e * j = j ∧ j * j = -e ∧ cA D e = e ∧ cA D j = -j ∧
      (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ τ, ((θ τ).comp (infPart D)) e = 1) ∧
      ∀ τ, ((θ τ).comp (infPart D)) j = tauE D τ μ / (‖tauE D τ μ‖ : ℂ) := by
  obtain ⟨e, hee, hce, hef, -, hfp, hip⟩ := GlobalTheory.StdUnn.realIdem_exists D
  obtain ⟨-, L2, L3, -⟩ := GlobalTheory.StdUnn.RealComp.real_components D θ hθ
  obtain ⟨u, ε, hεu, -, hε4⟩ := GlobalTheory.StdUnn.exists_scal_real D μ hμ 1
  have h4 := real_four D θ hθ _ hε4
  have hh : 2 * incA D (1 / 2) = 1 := incl_half _
  have h := alg_phase (cA D) (cA_cA D) hee hce hεu (cA_skew D μ hμ) hh (idem_four D θ hθ hfp h4)
  have he1 : ∀ τ, ((θ τ).comp (infPart D)) e = 1 := fun τ => (congrArg (θ τ) hip).trans (θ τ).map_one
  refine ⟨e, _, hee, h.1, h.2.1, hce, h.2.2, hef, he1, fun τ => ?_⟩
  have h2 : ((θ τ).comp (infPart D)) (incA D μ) = tauE D τ μ := L3 μ τ
  exact (cx_phase (cA D) ((θ τ).comp (infPart D)) (fun z => L2 z τ) (he1 τ) hεu hh (h4 τ)).trans
    (congrArg (fun t : ℂ => t / (‖t‖ : ℂ)) h2)

theorem exists_mem_K_compAt_eq_stdInv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (n : ℕ) (μ : D.host.E), IsSkew μ →
    ∃ k ∈ K D n, ∀ τ, compAt θ τ (mat k) = stdInv n μ τ := by
  intro D θ hθ n μ hμ
  obtain ⟨e, j, hee, hej, hjj, hce, hcj, hef, he1, hj⟩ := exists_phase_adele D θ hθ μ hμ
  obtain ⟨k, hk, hmat⟩ := exists_point D.sp.cm.sig n hee hej hjj hce hcj hef
  refine ⟨k, hk, fun τ => ?_⟩
  have h0 : mat (D := D) (n := n) k = mixJ n (1 - e) j := hmat
  have h1 : compAt θ τ (mixJ n (1 - e) j) = (mixJ n (1 - e) j).map ((θ τ).comp (infPart D)) := rfl
  rw [h0, h1, mixJ_real _ (he1 τ), hj]
  rfl

end GlobalTheory.CartanPt
