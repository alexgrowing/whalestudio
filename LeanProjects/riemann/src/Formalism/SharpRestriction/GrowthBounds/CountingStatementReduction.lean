import Formalism.SharpRestriction.GrowthBounds.FlipOneThree
import Formalism.MahlerMeasure.CoarseLevelSlackInequalities
import Formalism.PolynomialDimension.FinalM
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DischargeHeightBound
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.LatticeTheoremEps28Valid
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
import Lemmata.GeneralBFactLeftBisForm.Imports

noncomputable section

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.GM Formalism.GM.M Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.L4 Finset

theorem eps_eq (X : InstM) (i : Fin X.T.t) :
    X.eps i = Formalism.CountingSumsFrames.epsSeg (X.T.S (X.LL.setTies X.T X.top) i : ℝ) (X.Yl i) (Formalism.CountingSumsFrames.kapSeg X.p X.a X.r X.s)
      (Formalism.CountingSumsFrames.lgSeg X.p X.a X.r) X.E := rfl

theorem alternative_mean_value_theorem (D : Formalism.BasicNotions.D7) (X : InstM) : ModelLatticeRank D X := fun hX =>
  Formalism.InvariantFactorPaths.MC.Top.theoremMV7 X.p X.s X.r X.LL X.T X.a X.E X.Yl X.n₀ X.dd X.ρ hX.1 hX.2.1 hX.2.2.1 hX.2.2.2.1
    hX.2.2.2.2.1 hX.2.2.2.2.2.1 hX.2.2.2.2.2.2.1 hX.2.2.2.2.2.2.2.1 hX.2.2.2.2.2.2.2.2.1 hX.2.2.2.2.2.2.2.2.2.1
    hX.2.2.2.2.2.2.2.2.2.2

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

section General

variable {R A A' : Type} [CommRing R] [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A'] {n : ℕ}

theorem aeval_genMat_det (M : Matrix (Fin n) (Fin n) A) :
    aeval (fun x : Fin n × Fin n => M x.1 x.2) (genMat R n).det = M.det := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [genMat]

theorem evalG_alg (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit (aeval (fun x : Fin n × Fin n => g x.1 x.2) (genMat R n).det))
    (P : MvPolynomial (Fin n × Fin n) R) :
    evalG (R := R) g hg (algebraMap _ (GLCoord R n) P) = aeval (fun x : Fin n × Fin n => g x.1 x.2) P := by
  unfold evalG
  exact IsLocalization.Away.lift_eq _ hg P

theorem evalG_congr {g g' : Matrix (Fin n) (Fin n) A} (h : g = g')
    (hg : IsUnit (aeval (fun x : Fin n × Fin n => g x.1 x.2) (genMat R n).det))
    (hg' : IsUnit (aeval (fun x : Fin n × Fin n => g' x.1 x.2) (genMat R n).det)) (f : GLCoord R n) :
    evalG (R := R) g hg f = evalG (R := R) g' hg' f := by
  subst h; rfl

theorem evalG_map (φ : A →ₐ[R] A') (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit (aeval (fun x : Fin n × Fin n => g x.1 x.2) (genMat R n).det))
    (hg' : IsUnit (aeval (fun x : Fin n × Fin n => (g.map φ) x.1 x.2) (genMat R n).det)) (f : GLCoord R n) :
    φ (evalG (R := R) g hg f) = evalG (R := R) (g.map φ) hg' f := by
  have h : (φ : A →+* A').comp (evalG (R := R) g hg) = evalG (R := R) (g.map φ) hg' := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (genMat R n).det)
    apply RingHom.ext
    intro P
    simp only [RingHom.comp_apply, evalG_alg, RingHom.coe_coe]
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  exact RingHom.congr_fun h f

end General

theorem evaluation_generic_corner_entry {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {r : ℕ}
    (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
    (hg : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => g x.1 x.2) (genMat R (r + 1)).det)) :
    evalG (R := R) g hg (g0r R r) = g 0 (Fin.last r) := by
  unfold g0r
  rw [evalG_alg, aeval_X]

theorem chiB_map {A A' : Type} [CommRing A] [CommRing A'] {r : ℕ} (φ : A →+* A') (c : ℤ) (ka : Fin r → ℤ)
    (u : Fin (r + 1) → Aˣ) :
    φ (chiB c ka u : A) = (chiB c ka (fun i => Units.map (φ : A →* A') (u i)) : A') := by
  have : Units.map (φ : A →* A') (chiB c ka u) = chiB c ka (fun i => Units.map (φ : A →* A') (u i)) := by
    unfold chiB
    rw [map_mul, map_zpow, map_prod]
    simp only [map_zpow]
  rw [← this]
  rfl

theorem chiB_succ {A : Type} [CommRing A] {r : ℕ} (c : ℤ) (ka : Fin r → ℤ) (u : Fin (r + 1) → Aˣ) :
    (chiB c ka u : A) = (u 0 : A) * (chiB (c - 1) ka u : A) := by
  have : chiB c ka u = u 0 * chiB (c - 1) ka u := by
    unfold chiB
    rw [← mul_assoc, ← zpow_one_add]
    congr 2
    ring
  rw [this, Units.val_mul]

section Universal

variable (O : Type) [CommRing O] [IsDomain O] (n : ℕ)

abbrev UV (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

def uB : Matrix (Fin n) (Fin n) (MvPolynomial (UV n) O) := fun i j => if j ≤ i then X (Sum.inl (i, j)) else 0

def uG : Matrix (Fin n) (Fin n) (MvPolynomial (UV n) O) := fun i j => X (Sum.inr (i, j))

def uS : MvPolynomial (UV n) O := (∏ i : Fin n, X (Sum.inl (i, i))) * (uG O n).det

theorem uS_eq : uS O n = (∏ i : Fin n, X (Sum.inl (i, i))) * (uG O n).det := rfl

attribute [irreducible] uS

theorem uG_det_ne : (uG O n).det ≠ 0 := by
  have h : uG O n = (Matrix.mvPolynomialX (Fin n) (Fin n) O).map (rename (Sum.inr : Fin n × Fin n → UV n)) := by
    ext i j
    simp [uG, Matrix.mvPolynomialX]
  have h2 : ((Matrix.mvPolynomialX (Fin n) (Fin n) O).map (rename (Sum.inr : Fin n × Fin n → UV n))).det =
      rename (Sum.inr : Fin n × Fin n → UV n) (Matrix.mvPolynomialX (Fin n) (Fin n) O).det :=
    (AlgHom.map_det _ _).symm
  rw [h, h2]
  intro h0
  have := (rename_injective (Sum.inr : Fin n × Fin n → UV n) Sum.inr_injective (R := O))
    (h0.trans (map_zero _).symm)
  exact Matrix.det_mvPolynomialX_ne_zero (Fin n) O this

theorem uS_ne : uS O n ≠ 0 := by
  rw [uS_eq]
  refine mul_ne_zero ?_ (uG_det_ne O n)
  exact Finset.prod_ne_zero_iff.mpr fun i _ => X_ne_zero _

theorem uB_det : (uB O n).det = ∏ i : Fin n, X (Sum.inl (i, i)) := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [uB]
  · intro i j hij
    have : i < j := hij
    simp [uB, not_le.mpr this]

abbrev UA := Localization.Away (uS O n)

instance : IsDomain (UA O n) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (uS_ne O n))

theorem UA_inj : Function.Injective (algebraMap (MvPolynomial (UV n) O) (UA O n)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (uS_ne O n))

def B0 : Matrix (Fin n) (Fin n) (UA O n) := (uB O n).map (algebraMap (MvPolynomial (UV n) O) (UA O n))
def G0 : Matrix (Fin n) (Fin n) (UA O n) := (uG O n).map (algebraMap (MvPolynomial (UV n) O) (UA O n))

theorem uS_unit : IsUnit (algebraMap (MvPolynomial (UV n) O) (UA O n) (uS O n)) :=
  IsLocalization.Away.algebraMap_isUnit _

theorem unit_of_dvd (q : MvPolynomial (UV n) O) (h : q ∣ uS O n) :
    IsUnit (algebraMap (MvPolynomial (UV n) O) (UA O n) q) :=
  isUnit_of_dvd_unit (map_dvd _ h) (uS_unit O n)

theorem base_matrix_det_isUnit : IsUnit (G0 O n).det := by
  have h : (G0 O n).det = algebraMap (MvPolynomial (UV n) O) (UA O n) (uG O n).det := (RingHom.map_det _ _).symm
  rw [h]
  exact unit_of_dvd O n _ (Dvd.intro_left _ (uS_eq O n).symm)

theorem lower_triangular_base_det_isUnit : IsUnit (B0 O n).det := by
  have h : (B0 O n).det = algebraMap (MvPolynomial (UV n) O) (UA O n) (uB O n).det := (RingHom.map_det _ _).symm
  rw [h, uB_det]
  exact unit_of_dvd O n _ (Dvd.intro _ (uS_eq O n).symm)

theorem lower_triangular_base_diag_isUnit (i : Fin n) : IsUnit (B0 O n i i) := by
  have : B0 O n i i = algebraMap (MvPolynomial (UV n) O) (UA O n) (X (Sum.inl (i, i))) := by
    simp [B0, uB]
  rw [this]
  exact unit_of_dvd O n _ ((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans (Dvd.intro _ (uS_eq O n).symm))

def pt {A : Type} (b g : Matrix (Fin n) (Fin n) A) : UV n → A :=
  Sum.elim (fun x => b x.1 x.2) (fun x => g x.1 x.2)

theorem pt_unit {A : Type} [CommRing A] [Algebra O A] (b g : Matrix (Fin n) (Fin n) A)
    (hb : ∀ i, IsUnit (b i i)) (hg : IsUnit g.det) : IsUnit (aeval (pt n b g) (uS O n)) := by
  rw [uS_eq, map_mul, map_prod, AlgHom.map_det]
  refine IsUnit.mul ?_ ?_
  · have : ∀ i : Fin n, aeval (pt n b g) (X (Sum.inl (i, i)) : MvPolynomial (UV n) O) = b i i := by
      intro i; rw [aeval_X]; rfl
    simp only [this]
    exact (Finset.univ.prod_induction (fun i => b i i) IsUnit (fun _ _ h1 h2 => h1.mul h2) isUnit_one
      (fun i _ => hb i))
  · convert hg using 2
    ext i j
    simp [uG, pt]

def specR {A : Type} [CommRing A] [Algebra O A] (b g : Matrix (Fin n) (Fin n) A)
    (hb : ∀ i, IsUnit (b i i)) (hg : IsUnit g.det) : UA O n →+* A :=
  IsLocalization.Away.lift (uS O n)
    (g := (aeval (pt n b g) : MvPolynomial (UV n) O →ₐ[O] A).toRingHom) (pt_unit O n b g hb hg)

theorem specR_alg {A : Type} [CommRing A] [Algebra O A] (b g : Matrix (Fin n) (Fin n) A)
    (hb : ∀ i, IsUnit (b i i)) (hg : IsUnit g.det) (q : MvPolynomial (UV n) O) :
    specR O n b g hb hg (algebraMap (MvPolynomial (UV n) O) (UA O n) q) = aeval (pt n b g) q := by
  unfold specR
  exact IsLocalization.Away.lift_eq _ (pt_unit O n b g hb hg) q

def spec {A : Type} [CommRing A] [Algebra O A] (b g : Matrix (Fin n) (Fin n) A)
    (hb : ∀ i, IsUnit (b i i)) (hg : IsUnit g.det) : UA O n →ₐ[O] A :=
  { specR O n b g hb hg with
    commutes' := fun c => by
      show specR O n b g hb hg (algebraMap O (UA O n) c) = algebraMap O A c
      rw [IsScalarTower.algebraMap_apply O (MvPolynomial (UV n) O) (UA O n), specR_alg, AlgHom.commutes] }

theorem spec_alg {A : Type} [CommRing A] [Algebra O A] (b g : Matrix (Fin n) (Fin n) A)
    (hb : ∀ i, IsUnit (b i i)) (hg : IsUnit g.det) (q : MvPolynomial (UV n) O) :
    spec O n b g hb hg (algebraMap (MvPolynomial (UV n) O) (UA O n) q) = aeval (pt n b g) q :=
  specR_alg O n b g hb hg q

end Universal

theorem key_positivity_condition (D : Formalism.BasicNotions.D7) : ArchimedeanSignatureMatching D := by
  intro O _ _ _ r c ka f _ hf hdvd
  obtain ⟨f₁, rfl⟩ := hdvd
  refine ⟨f₁, ?_, rfl⟩

  have hG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => G0 O (r + 1) x.1 x.2) (genMat O (r + 1)).det) := by
    rw [aeval_genMat_det]; exact base_matrix_det_isUnit O (r + 1)
  have hBG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => (B0 O (r + 1) * G0 O (r + 1)) x.1 x.2)
      (genMat O (r + 1)).det) := by
    rw [aeval_genMat_det, Matrix.det_mul]; exact (lower_triangular_base_det_isUnit O (r + 1)).mul (base_matrix_det_isUnit O (r + 1))
  let U0 : Fin (r + 1) → (UA O (r + 1))ˣ := fun i => (lower_triangular_base_diag_isUnit O (r + 1) i).unit
  have hlow0 : ∀ i j, i < j → B0 O (r + 1) i j = 0 := by
    intro i j hij
    simp [B0, uB, not_le.mpr hij]
  have hU0 : ∀ i, B0 O (r + 1) i i = U0 i := fun i => rfl
  have h0 := hf (UA O (r + 1)) (B0 O (r + 1)) (G0 O (r + 1)) U0 hG0 hBG0 hlow0 hU0
  rw [map_mul, map_mul, evaluation_generic_corner_entry, evaluation_generic_corner_entry] at h0
  have hrow : (B0 O (r + 1) * G0 O (r + 1)) 0 (Fin.last r) = (U0 0 : UA O (r + 1)) * G0 O (r + 1) 0 (Fin.last r) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [hU0]
    · intro k _ hk
      rw [hlow0 0 k (Fin.pos_of_ne_zero hk), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hγ : G0 O (r + 1) 0 (Fin.last r) ≠ 0 := by
    have : G0 O (r + 1) 0 (Fin.last r) = algebraMap (MvPolynomial (UV (r + 1)) O) (UA O (r + 1))
        (X (Sum.inr (0, Fin.last r))) := rfl
    rw [this]
    intro h
    exact X_ne_zero (R := O) _ (UA_inj O (r + 1) (h.trans (map_zero _).symm))
  have hE : evalG (R := O) (B0 O (r + 1) * G0 O (r + 1)) hBG0 f₁ =
      (chiB (c - 1) ka U0 : UA O (r + 1)) * evalG (R := O) (G0 O (r + 1)) hG0 f₁ := by
    rw [hrow, chiB_succ] at h0
    have hne : (U0 0 : UA O (r + 1)) * G0 O (r + 1) 0 (Fin.last r) ≠ 0 := mul_ne_zero (U0 0).ne_zero hγ
    apply mul_left_cancel₀ hne
    rw [h0]; ring

  intro A _ _ b g u hg hbg hlow hdiag
  have hdetg : IsUnit g.det := by rwa [aeval_genMat_det] at hg
  have hbu : ∀ i, IsUnit (b i i) := fun i => by rw [hdiag i]; exact Units.isUnit _
  let φ := spec O (r + 1) b g hbu hdetg
  have hφB : (B0 O (r + 1)).map φ = b := by
    ext i j
    simp only [Matrix.map_apply, B0, uB]
    rw [spec_alg]
    split_ifs with h
    · rw [aeval_X]; rfl
    · rw [map_zero, hlow i j (not_le.mp h)]
  have hφG : (G0 O (r + 1)).map φ = g := by
    ext i j
    simp only [Matrix.map_apply, G0, uG]
    rw [spec_alg, aeval_X]; rfl
  have hφBG : (B0 O (r + 1) * G0 O (r + 1)).map φ = b * g := by
    rw [Matrix.map_mul, hφB, hφG]
  have hφU : (fun i => Units.map ((φ : UA O (r + 1) →+* A) : UA O (r + 1) →* A) (U0 i)) = u := by
    funext i
    apply Units.ext
    have : φ (B0 O (r + 1) i i) = b i i := by
      have := congrFun (congrFun hφB i) i
      simpa using this
    rw [← hdiag i, ← this]
    rfl
  have h1 := congrArg φ hE
  rw [map_mul, evalG_map φ _ hBG0 (by rw [hφBG]; exact hbg), evalG_map φ _ hG0 (by rw [hφG]; exact hg),
    evalG_congr hφBG _ hbg, evalG_congr hφG _ hg] at h1
  rw [h1]
  congr 1
  have h2 := chiB_map (φ : UA O (r + 1) →+* A) (c - 1) ka U0
  rw [hφU] at h2
  exact h2

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

section GlobalTheory

variable {A A' : Type} [CommRing A] [CommRing A'] {n : ℕ}

def blk (W : Fin n → A) (Dm : Matrix (Fin n) (Fin n) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  fun i j => Fin.cases (motive := fun _ => A) (Fin.cases (motive := fun _ => A) 1 W j)
    (fun i' => Fin.cases (motive := fun _ => A) 0 (fun j' => Dm i' j') j) i

def lowM (γ : A) (v : Fin n → A) (b' : Matrix (Fin n) (Fin n) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  fun i j => Fin.cases (motive := fun _ => A) (Fin.cases (motive := fun _ => A) γ (fun _ => 0) j)
    (fun i' => Fin.cases (motive := fun _ => A) (v i') (fun j' => b' i' j') j) i

variable (W : Fin n → A) (Dm : Matrix (Fin n) (Fin n) A) (γ : A) (v : Fin n → A) (b' : Matrix (Fin n) (Fin n) A)

@[simp] theorem blk_00 : blk W Dm 0 0 = 1 := rfl
@[simp] theorem blk_0s (j : Fin n) : blk W Dm 0 j.succ = W j := rfl
@[simp] theorem cornerScalarBlockMatrix_apply_succ_zero (i : Fin n) : blk W Dm i.succ 0 = 0 := rfl
@[simp] theorem blk_ss (i j : Fin n) : blk W Dm i.succ j.succ = Dm i j := rfl
@[simp] theorem lowM_00 : lowM γ v b' 0 0 = γ := rfl
@[simp] theorem lowM_0s (j : Fin n) : lowM γ v b' 0 j.succ = 0 := rfl
@[simp] theorem lowerMatrix_succ_zero (i : Fin n) : lowM γ v b' i.succ 0 = v i := rfl
@[simp] theorem lowM_ss (i j : Fin n) : lowM γ v b' i.succ j.succ = b' i j := rfl

theorem blk_det : (blk W Dm).det = Dm.det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h : (blk W Dm).submatrix Fin.succ Fin.succ = Dm := by
    ext i j
    simp [Matrix.submatrix_apply]
  simp [h]

theorem blk_map (φ : A →+* A') : (blk W Dm).map φ = blk (fun j => φ (W j)) (Dm.map φ) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;> simp

theorem lowM_mul_blk_00 : (lowM γ v b' * blk W Dm) 0 0 = γ := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]; simp

theorem lowM_mul_blk_0s (j : Fin n) : (lowM γ v b' * blk W Dm) 0 j.succ = γ * W j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]; simp

theorem lowerMatrix_mul_block_succ_zero (i : Fin n) : (lowM γ v b' * blk W Dm) i.succ 0 = v i := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]; simp

theorem lowM_mul_blk_ss (i j : Fin n) : (lowM γ v b' * blk W Dm) i.succ j.succ = v i * W j + (b' * Dm) i j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mul_apply]; simp

end GlobalTheory

def genD (O : Type) [CommRing O] (r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1))) :=
  (genMat O (r + 1)).map ((C : GLCoord O (r + 1) →+* MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1))).comp
    (algebraMap (MvPolynomial (Fin (r + 1) × Fin (r + 1)) O) (GLCoord O (r + 1))))

theorem resMat_eq (O : Type) [CommRing O] (r : ℕ) :
    resMat O r = blk (fun j => (X j : MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1)))) (genD O r) := rfl

theorem res_unit (O : Type) [CommRing O] (r : ℕ) :
    IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => resMat O r x.1 x.2) (genMat O (r + 1 + 1)).det) := by
  rw [aeval_genMat_det, resMat_eq, blk_det]
  have h : (genD O r).det = ((C : GLCoord O (r + 1) →+* MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1))).comp
      (algebraMap (MvPolynomial (Fin (r + 1) × Fin (r + 1)) O) (GLCoord O (r + 1)))) (genMat O (r + 1)).det :=
    (RingHom.map_det _ _).symm
  rw [h, RingHom.comp_apply]
  exact (IsLocalization.Away.algebraMap_isUnit (genMat O (r + 1)).det).map C

section Eval

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

theorem evalG_algebraMap {n : ℕ} (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit (aeval (fun x : Fin n × Fin n => g x.1 x.2) (genMat O n).det)) (c : O) :
    evalG (R := O) g hg (algebraMap O (GLCoord O n) c) = algebraMap O A c := by
  rw [IsScalarTower.algebraMap_apply O (MvPolynomial (Fin n × Fin n) O) (GLCoord O n), evalG_alg, AlgHom.commutes]

variable {r : ℕ}

def resEv (W : Fin (r + 1) → A) (Dm : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
    (hD : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => Dm x.1 x.2) (genMat O (r + 1)).det)) :
    MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1)) →ₐ[O] A :=
  { eval₂Hom (evalG (R := O) Dm hD) W with
    commutes' := fun c => by
      show eval₂Hom (evalG (R := O) Dm hD) W (algebraMap O _ c) = algebraMap O A c
      rw [MvPolynomial.algebraMap_apply, eval₂Hom_C, evalG_algebraMap] }

theorem resEv_X (W : Fin (r + 1) → A) (Dm : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
    (hD : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => Dm x.1 x.2) (genMat O (r + 1)).det)) (j : Fin (r + 1)) :
    resEv W Dm hD (X j) = W j := by
  show eval₂Hom (evalG (R := O) Dm hD) W (X j) = W j
  rw [eval₂Hom_X']

theorem resEv_C (W : Fin (r + 1) → A) (Dm : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
    (hD : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => Dm x.1 x.2) (genMat O (r + 1)).det))
    (x : GLCoord O (r + 1)) : resEv W Dm hD (C x) = evalG (R := O) Dm hD x := by
  show eval₂Hom (evalG (R := O) Dm hD) W (C x) = _
  rw [eval₂Hom_C]

theorem resEv_resMat (W : Fin (r + 1) → A) (Dm : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
    (hD : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => Dm x.1 x.2) (genMat O (r + 1)).det)) :
    (resMat O r).map (resEv W Dm hD) = blk W Dm := by
  have h := blk_map (fun j => (X j : MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1)))) (genD O r)
    (resEv W Dm hD : MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1)) →+* A)
  rw [resMat_eq]
  refine h.trans ?_
  congr 1
  · funext j; exact resEv_X W Dm hD j
  · ext i j
    simp only [genD, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_coe, resEv_C, evalG_alg, genMat,
      Matrix.of_apply, aeval_X]

theorem RES_eval (W : Fin (r + 1) → A) (Dm : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
    (hD : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => Dm x.1 x.2) (genMat O (r + 1)).det))
    (hM : IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => resMat O r x.1 x.2) (genMat O (r + 1 + 1)).det))
    (h : IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => blk W Dm x.1 x.2) (genMat O (r + 1 + 1)).det))
    (f : GLCoord O (r + 1 + 1)) :
    resEv W Dm hD (evalG (R := O) (resMat O r) hM f) = evalG (R := O) (blk W Dm) h f := by
  rw [evalG_map (resEv W Dm hD) _ hM (by rw [resEv_resMat]; exact h)]
  exact evalG_congr (resEv_resMat W Dm hD) _ _ f

theorem lowM_lower {n : ℕ} (γ : A) (v : Fin n → A) (b' : Matrix (Fin n) (Fin n) A)
    (hlow : ∀ i j, i < j → b' i j = 0) : ∀ i j, i < j → lowM γ v b' i j = 0 := by
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · intro h; exact absurd h (lt_irrefl _)
  · intro _; rfl
  · intro h; exact absurd h (Fin.not_lt_zero _)
  · intro h; exact hlow i' j' (Fin.succ_lt_succ_iff.mp h)

theorem HB_low {n : ℕ} {c : ℤ} {ka : Fin n → ℤ} {f : GLCoord O (n + 1)} (hf : f ∈ HB O n c ka) (γ : Aˣ)
    (v : Fin n → A) (b' : Matrix (Fin n) (Fin n) A) (u' : Fin n → Aˣ) (hlow : ∀ i j, i < j → b' i j = 0)
    (hdiag : ∀ i, b' i i = u' i) (W : Fin n → A) (Dm : Matrix (Fin n) (Fin n) A)
    (h2 : IsUnit (aeval (fun x : Fin (n + 1) × Fin (n + 1) => blk W Dm x.1 x.2) (genMat O (n + 1)).det))
    (h1 : IsUnit (aeval (fun x : Fin (n + 1) × Fin (n + 1) => (lowM (γ : A) v b' * blk W Dm) x.1 x.2)
      (genMat O (n + 1)).det)) :
    evalG (R := O) (lowM (γ : A) v b' * blk W Dm) h1 f =
      ((γ ^ c * ∏ i, u' i ^ ka i : Aˣ) : A) * evalG (R := O) (blk W Dm) h2 f := by
  have h := hf A (lowM (γ : A) v b') (blk W Dm) (Fin.cases γ u') h2 h1 (lowM_lower _ _ _ hlow)
    (by intro i; refine Fin.cases rfl (fun i' => ?_) i; exact hdiag i')
  exact h

def cellW {n : ℕ} (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (γ : Aˣ) : Fin n → A :=
  fun j => ((γ⁻¹ : Aˣ) : A) * g 0 j.succ

def cellD {n : ℕ} (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (γ : Aˣ) : Matrix (Fin n) (Fin n) A :=
  fun i j => g i.succ j.succ - g i.succ 0 * cellW g γ j

theorem cell_mul {n : ℕ} (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (γ : Aˣ) (hγ : g 0 0 = γ) :
    g = lowM (γ : A) (fun i => g i.succ 0) 1 * blk (cellW g γ) (cellD g γ) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · rw [lowM_mul_blk_00, hγ]
  · rw [lowM_mul_blk_0s, cellW, ← mul_assoc, Units.mul_inv, one_mul]
  · rw [lowerMatrix_mul_block_succ_zero]
  · rw [lowM_mul_blk_ss, Matrix.one_mul, cellD]; ring

theorem cell_unit {n : ℕ} (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (γ : Aˣ) (hγ : g 0 0 = γ)
    (hg : IsUnit g.det) : IsUnit (cellD g γ).det := by
  rw [cell_mul g γ hγ, Matrix.det_mul, blk_det] at hg
  exact isUnit_of_mul_isUnit_right hg

theorem bigcell {n : ℕ} {c : ℤ} {ka : Fin n → ℤ} {f : GLCoord O (n + 1)} (hf : f ∈ HB O n c ka)
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (γ : Aˣ) (hγ : g 0 0 = γ)
    (hg : IsUnit (aeval (fun x : Fin (n + 1) × Fin (n + 1) => g x.1 x.2) (genMat O (n + 1)).det))
    (h2 : IsUnit (aeval (fun x : Fin (n + 1) × Fin (n + 1) => blk (cellW g γ) (cellD g γ) x.1 x.2)
      (genMat O (n + 1)).det)) :
    evalG (R := O) g hg f = ((γ ^ c : Aˣ) : A) * evalG (R := O) (blk (cellW g γ) (cellD g γ)) h2 f := by
  have hm := cell_mul g γ hγ
  have h1 : IsUnit (aeval (fun x : Fin (n + 1) × Fin (n + 1) =>
      (lowM (γ : A) (fun i => g i.succ 0) 1 * blk (cellW g γ) (cellD g γ)) x.1 x.2) (genMat O (n + 1)).det) := by
    rw [← hm]; exact hg
  rw [evalG_congr hm hg h1, HB_low hf γ _ 1 (fun _ => 1) (fun i j hij => Matrix.one_apply_ne (ne_of_lt hij))
    (fun i => by simp) _ _ h2 h1]
  simp

end Eval

section Generic

variable (O : Type) [CommRing O] [IsDomain O] (n : ℕ)

theorem genMat_det_ne : (genMat O n).det ≠ 0 := Matrix.det_mvPolynomialX_ne_zero (Fin n) O

instance instDomGL : IsDomain (GLCoord O n) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (genMat_det_ne O n))

theorem GL_inj : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) O) (GLCoord O n)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (genMat_det_ne O n))

def genG : Matrix (Fin n) (Fin n) (GLCoord O n) :=
  (genMat O n).map (algebraMap (MvPolynomial (Fin n × Fin n) O) (GLCoord O n))

theorem genG_det_unit : IsUnit (genG O n).det := by
  have h : (genG O n).det = algebraMap (MvPolynomial (Fin n × Fin n) O) (GLCoord O n) (genMat O n).det :=
    (RingHom.map_det _ _).symm
  rw [h]
  exact IsLocalization.Away.algebraMap_isUnit _

theorem genG_unit : IsUnit (aeval (fun x : Fin n × Fin n => genG O n x.1 x.2) (genMat O n).det) := by
  rw [aeval_genMat_det]; exact genG_det_unit O n

theorem evalG_genG (h : IsUnit (aeval (fun x : Fin n × Fin n => genG O n x.1 x.2) (genMat O n).det))
    (f : GLCoord O n) : evalG (R := O) (genG O n) h f = f := by
  have h1 : evalG (R := O) (genG O n) h = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (genMat O n).det)
    apply RingHom.ext
    intro P
    simp only [RingHom.comp_apply, evalG_alg, RingHom.id_apply]
    have h2 := aeval_unique (IsScalarTower.toAlgHom O (MvPolynomial (Fin n × Fin n) O) (GLCoord O n))
    have h3 := congrArg (fun φ => φ P) h2
    simp only [IsScalarTower.coe_toAlgHom'] at h3
    rw [h3]
    rfl
  rw [h1]; rfl

def g00 : GLCoord O (n + 1) := algebraMap (MvPolynomial (Fin (n + 1) × Fin (n + 1)) O) (GLCoord O (n + 1)) (X (0, 0))

theorem corner_entry_ne_zero : g00 O n ≠ 0 := by
  intro h
  exact X_ne_zero (R := O) _ (GL_inj O (n + 1) (h.trans (map_zero _).symm))

abbrev CA := Localization.Away (g00 O n)

instance instDomCA : IsDomain (CA O n) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (corner_entry_ne_zero O n))

theorem CA_inj : Function.Injective (algebraMap (GLCoord O (n + 1)) (CA O n)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (corner_entry_ne_zero O n))

def iotaA : GLCoord O (n + 1) →ₐ[O] CA O n := IsScalarTower.toAlgHom O (GLCoord O (n + 1)) (CA O n)

def genA : Matrix (Fin (n + 1)) (Fin (n + 1)) (CA O n) := (genG O (n + 1)).map (iotaA O n)

def gam : (CA O n)ˣ := (IsLocalization.Away.algebraMap_isUnit (S := CA O n) (g00 O n)).unit

theorem genA_00 : genA O n 0 0 = gam O n := by
  simp [genA, genG, genMat, gam, g00, iotaA]
  rfl

theorem genA_det_unit : IsUnit (genA O n).det := by
  have h : (genA O n).det = iotaA O n (genG O (n + 1)).det := (AlgHom.map_det _ _).symm
  rw [h]
  exact (genG_det_unit O (n + 1)).map _

theorem genA_unit : IsUnit (aeval (fun x : Fin (n + 1) × Fin (n + 1) => genA O n x.1 x.2) (genMat O (n + 1)).det) := by
  rw [aeval_genMat_det]; exact genA_det_unit O n

theorem evalG_genA (f : GLCoord O (n + 1)) : evalG (R := O) (genA O n) (genA_unit O n) f = iotaA O n f := by
  have h := evalG_map (iotaA O n) (genG O (n + 1)) (genG_unit O (n + 1)) (genA_unit O n) f
  rw [evalG_genG] at h
  exact h.symm

def cW : Fin n → CA O n := cellW (genA O n) (gam O n)
def cD : Matrix (Fin n) (Fin n) (CA O n) := cellD (genA O n) (gam O n)

theorem cD_unit : IsUnit (aeval (fun x : Fin n × Fin n => cD O n x.1 x.2) (genMat O n).det) := by
  rw [aeval_genMat_det]; exact cell_unit _ _ (genA_00 O n) (genA_det_unit O n)

theorem cblk_unit : IsUnit (aeval (fun x : Fin (n + 1) × Fin (n + 1) => blk (cW O n) (cD O n) x.1 x.2)
    (genMat O (n + 1)).det) := by
  rw [aeval_genMat_det, blk_det]; exact cell_unit _ _ (genA_00 O n) (genA_det_unit O n)

end Generic

theorem cellFormula (O : Type) [CommRing O] [IsDomain O] (r : ℕ) {c : ℤ} {ka : Fin (r + 1) → ℤ}
    {f : GLCoord O (r + 1 + 1)} (hf : f ∈ HB O (r + 1) c ka)
    (hM : IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => resMat O r x.1 x.2) (genMat O (r + 1 + 1)).det)) :
    iotaA O (r + 1) f = ((gam O (r + 1) ^ c : (CA O (r + 1))ˣ) : CA O (r + 1)) *
      resEv (cW O (r + 1)) (cD O (r + 1)) (cD_unit O (r + 1)) (evalG (R := O) (resMat O r) hM f) := by
  rw [RES_eval _ _ _ hM (cblk_unit O (r + 1)), ← evalG_genA]
  exact bigcell hf (genA O (r + 1)) (gam O (r + 1)) (genA_00 O (r + 1)) _ _

theorem res_inj (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (c : ℤ) (ka : Fin (r + 1) → ℤ)
    (hM : IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => resMat O r x.1 x.2) (genMat O (r + 1 + 1)).det))
    (f : GLCoord O (r + 1 + 1)) (hf : f ∈ HB O (r + 1) c ka) (f' : GLCoord O (r + 1 + 1))
    (hf' : f' ∈ HB O (r + 1) c ka) (h : evalG (R := O) (resMat O r) hM f = evalG (R := O) (resMat O r) hM f') :
    f = f' := by
  apply CA_inj O (r + 1)
  have h1 := cellFormula O r hf hM
  have h2 := cellFormula O r hf' hM
  rw [h] at h1
  exact h1.trans h2.symm

section Loc

variable {R : Type} [CommRing R] [IsDomain R]

theorem away_pow_dvd (s q : R) (hq : Prime q) (hs : ¬ q ∣ s) (e : ℕ) (x : R)
    (h : algebraMap R (Localization.Away s) q ^ e ∣ algebraMap R (Localization.Away s) x) : q ^ e ∣ x := by
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ dvd_zero q)
  have hinj : Function.Injective (algebraMap R (Localization.Away s)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hs0)
  obtain ⟨y, hy⟩ := h
  obtain ⟨⟨z, ⟨t, k, hk⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers s) y
  have hz' : y * algebraMap R (Localization.Away s) t = algebraMap R (Localization.Away s) z := hz
  have h1 : x * t = q ^ e * z := by
    apply hinj
    rw [map_mul, hy, mul_assoc, hz', map_mul, map_pow]
  have hk' : s ^ k = t := hk
  have ht : ¬ q ∣ t := by
    rw [← hk']
    exact fun hd => hs (hq.dvd_of_dvd_pow hd)
  exact hq.pow_dvd_of_dvd_mul_right e ht ⟨z, h1⟩

theorem away_prime (s q : R) (hq : Prime q) (hs : ¬ q ∣ s) : Prime (algebraMap R (Localization.Away s) q) := by
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ dvd_zero q)
  have hinj : Function.Injective (algebraMap R (Localization.Away s)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hs0)
  have hdvd : ∀ x : R, algebraMap R (Localization.Away s) q ∣ algebraMap R (Localization.Away s) x → q ∣ x := by
    intro x hx
    have := away_pow_dvd s q hq hs 1 x (by rwa [pow_one])
    rwa [pow_one] at this
  refine ⟨fun h0 => hq.ne_zero (hinj (h0.trans (map_zero _).symm)), fun hu => ?_, fun a b hab => ?_⟩
  · have h1 : algebraMap R (Localization.Away s) q ∣ algebraMap R (Localization.Away s) 1 := by
      rw [map_one]; exact hu.dvd
    exact hq.not_isUnit (isUnit_of_dvd_one (hdvd 1 h1))
  · obtain ⟨⟨a0, t1⟩, ha⟩ := IsLocalization.surj (Submonoid.powers s) a
    obtain ⟨⟨b0, t2⟩, hb⟩ := IsLocalization.surj (Submonoid.powers s) b
    have ha' : a * algebraMap R (Localization.Away s) t1 = algebraMap R (Localization.Away s) a0 := ha
    have hb' : b * algebraMap R (Localization.Away s) t2 = algebraMap R (Localization.Away s) b0 := hb
    have hu1 : IsUnit (algebraMap R (Localization.Away s) (t1 : R)) := IsLocalization.map_units _ t1
    have hu2 : IsUnit (algebraMap R (Localization.Away s) (t2 : R)) := IsLocalization.map_units _ t2
    have h1 : algebraMap R (Localization.Away s) q ∣ algebraMap R (Localization.Away s) (a0 * b0) := by
      rw [map_mul, ← ha', ← hb']
      have : a * algebraMap R (Localization.Away s) (t1 : R) * (b * algebraMap R (Localization.Away s) (t2 : R)) =
          a * b * (algebraMap R (Localization.Away s) (t1 : R) * algebraMap R (Localization.Away s) (t2 : R)) := by ring
      rw [this]
      exact Dvd.dvd.mul_right hab _
    rcases hq.dvd_or_dvd (hdvd _ h1) with h | h
    · left
      have h2 : algebraMap R (Localization.Away s) q ∣ a * algebraMap R (Localization.Away s) (t1 : R) := by
        rw [ha']; exact map_dvd _ h
      exact (hu1.dvd_mul_right).1 h2
    · right
      have h2 : algebraMap R (Localization.Away s) q ∣ b * algebraMap R (Localization.Away s) (t2 : R) := by
        rw [hb']; exact map_dvd _ h
      exact (hu2.dvd_mul_right).1 h2

end Loc

section Primes

variable (O : Type) [CommRing O] [IsDomain O] (n : ℕ)

def evOne : MvPolynomial (Fin n × Fin n) O →ₐ[O] O := aeval (fun x : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) O) x.1 x.2)

theorem evOne_det : evOne O n (genMat O n).det = 1 := by
  unfold evOne
  rw [aeval_genMat_det, Matrix.det_one]

theorem evOne_X (i j : Fin n) : evOne O n (X (i, j)) = (1 : Matrix (Fin n) (Fin n) O) i j := by
  unfold evOne
  rw [aeval_X]

theorem not_dvd_det (q : MvPolynomial (Fin n × Fin n) O) (hq : ¬ IsUnit (evOne O n q)) : ¬ q ∣ (genMat O n).det := by
  intro h
  have := map_dvd (evOne O n) h
  rw [evOne_det] at this
  exact hq (isUnit_of_dvd_one this)

theorem not_dvd_corner_variable (q : MvPolynomial (Fin (n + 1) × Fin (n + 1)) O) (hq : ¬ IsUnit (evOne O (n + 1) q)) :
    ¬ q ∣ X (0, 0) := by
  intro h
  have := map_dvd (evOne O (n + 1)) h
  rw [evOne_X, Matrix.one_apply_eq] at this
  exact hq (isUnit_of_dvd_one this)

theorem cell_pow_dvd (q : MvPolynomial (Fin (n + 1) × Fin (n + 1)) O) (hq : Prime q)
    (hq1 : ¬ IsUnit (evOne O (n + 1) q)) (e : ℕ) (f : GLCoord O (n + 1))
    (h : algebraMap (GLCoord O (n + 1)) (CA O n) (algebraMap _ (GLCoord O (n + 1)) q) ^ e ∣
      algebraMap (GLCoord O (n + 1)) (CA O n) f) :
    algebraMap _ (GLCoord O (n + 1)) q ^ e ∣ f := by
  have hp : Prime (algebraMap (MvPolynomial (Fin (n + 1) × Fin (n + 1)) O) (GLCoord O (n + 1)) q) :=
    away_prime _ q hq (not_dvd_det O (n + 1) q hq1)
  refine away_pow_dvd (g00 O n) _ hp ?_ e f h
  intro hd
  have := away_pow_dvd _ q hq (not_dvd_det O (n + 1) q hq1) 1 (X (0, 0)) (by rw [pow_one]; exact hd)
  rw [pow_one] at this
  exact not_dvd_corner_variable O n q hq1 this

end Primes

theorem residue_matrix_generic_corner_entry (O : Type) [CommRing O] (r : ℕ)
    (hM : IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => resMat O r x.1 x.2) (genMat O (r + 1 + 1)).det)) :
    evalG (R := O) (resMat O r) hM (g0r O (r + 1)) = X (Fin.last r) := by
  rw [evaluation_generic_corner_entry, ← Fin.succ_last, resMat_eq, blk_0s]

theorem cW_last (O : Type) [CommRing O] [IsDomain O] (r : ℕ) :
    cW O (r + 1) (Fin.last r) = ((gam O (r + 1))⁻¹ : (CA O (r + 1))ˣ) *
      algebraMap (GLCoord O (r + 1 + 1)) (CA O (r + 1)) (g0r O (r + 1)) := by
  unfold cW cellW
  congr 1

theorem res_div (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (c : ℤ) (ka : Fin (r + 1) → ℤ)
    (hM : IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => resMat O r x.1 x.2) (genMat O (r + 1 + 1)).det))
    (f : GLCoord O (r + 1 + 1)) (hf : f ∈ HB O (r + 1) c ka) (e : ℕ) :
    g0r O (r + 1) ^ e ∣ f ↔ X (Fin.last r) ^ e ∣ evalG (R := O) (resMat O r) hM f := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [map_mul, map_pow, residue_matrix_generic_corner_entry]
    exact Dvd.intro _ rfl
  · rintro ⟨F1, hF1⟩
    have h1 := cellFormula O r hf hM
    rw [hF1, map_mul, map_pow, resEv_X, cW_last, mul_pow] at h1
    refine cell_pow_dvd O (r + 1) (X (0, Fin.last (r + 1))) X_prime ?_ e f ?_
    · rw [evOne_X, Matrix.one_apply_ne (Fin.last_pos).ne]
      exact not_isUnit_zero
    · refine ⟨((gam O (r + 1) ^ c : (CA O (r + 1))ˣ) : CA O (r + 1)) *
        (((gam O (r + 1))⁻¹ : (CA O (r + 1))ˣ) : CA O (r + 1)) ^ e *
        resEv (cW O (r + 1)) (cD O (r + 1)) (cD_unit O (r + 1)) F1, ?_⟩
      have h2 : algebraMap (GLCoord O (r + 1 + 1)) (CA O (r + 1)) f = iotaA O (r + 1) f := rfl
      rw [h2, h1]
      unfold g0r
      ring

section Coeff

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] {r : ℕ}

def cAlg (O : Type) [CommRing O] (A : Type) [CommRing A] [Algebra O A] (σ : Type) : A →ₐ[O] MvPolynomial σ A :=
  IsScalarTower.toAlgHom O A (MvPolynomial σ A)

theorem mapC_unit {n : ℕ} (σ : Type) (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit (aeval (fun x : Fin n × Fin n => g x.1 x.2) (genMat O n).det)) :
    IsUnit (aeval (fun x : Fin n × Fin n => (g.map (cAlg O A σ)) x.1 x.2) (genMat O n).det) := by
  rw [aeval_genMat_det] at hg ⊢
  have h : (g.map (cAlg O A σ)).det = cAlg O A σ g.det := (AlgHom.map_det _ _).symm
  rw [h]
  exact hg.map _

theorem resEv_const (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
    (hg : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => g x.1 x.2) (genMat O (r + 1)).det))
    (F : MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1))) :
    resEv (fun j => (X j : MvPolynomial (Fin (r + 1)) A)) (g.map (cAlg O A (Fin (r + 1)))) (mapC_unit _ g hg) F =
      MvPolynomial.map (evalG (R := O) g hg) F := by
  have h : evalG (R := O) (g.map (cAlg O A (Fin (r + 1)))) (mapC_unit _ g hg) =
      (C : A →+* MvPolynomial (Fin (r + 1)) A).comp (evalG (R := O) g hg) := by
    apply RingHom.ext
    intro x
    exact (evalG_map (cAlg O A (Fin (r + 1))) g hg (mapC_unit _ g hg) x).symm
  show eval₂Hom (evalG (R := O) (g.map (cAlg O A (Fin (r + 1)))) (mapC_unit _ g hg)) _ F = _
  rw [h]
  have h2 : eval₂Hom ((C : A →+* MvPolynomial (Fin (r + 1)) A).comp (evalG (R := O) g hg))
      (fun j => (X j : MvPolynomial (Fin (r + 1)) A)) = MvPolynomial.map (evalG (R := O) g hg) := by
    apply MvPolynomial.ringHom_ext
    · intro x; simp
    · intro i; simp
  rw [h2]

end Coeff

theorem res_coeff (O : Type) [CommRing O] (r : ℕ) (c : ℤ) (ka : Fin (r + 1) → ℤ)
    (hM : IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => resMat O r x.1 x.2) (genMat O (r + 1 + 1)).det))
    (f : GLCoord O (r + 1 + 1)) (hf : f ∈ HB O (r + 1) c ka) (m : Fin (r + 1) →₀ ℕ) :
    (evalG (R := O) (resMat O r) hM f).coeff m ∈ HB O r (ka 0) (fun i => ka i.succ) := by
  intro A _ _ b g u hg hbg hlow hdiag
  set φ := cAlg O A (Fin (r + 1)) with hφ
  set XX : Fin (r + 1) → MvPolynomial (Fin (r + 1)) A := fun j => X j with hXX
  have hmul : blk XX ((b * g).map φ) = lowM (((1 : (MvPolynomial (Fin (r + 1)) A)ˣ)) : MvPolynomial (Fin (r + 1)) A)
      (fun _ => 0) (b.map φ) * blk XX (g.map φ) := by
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · rw [lowM_mul_blk_00]; simp
    · rw [lowM_mul_blk_0s]; simp
    · rw [lowerMatrix_mul_block_succ_zero]; simp
    · rw [lowM_mul_blk_ss, blk_ss, Matrix.map_mul]; simp
  have hu2 : IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => blk XX (g.map φ) x.1 x.2)
      (genMat O (r + 1 + 1)).det) := by
    have := mapC_unit (O := O) (Fin (r + 1)) g hg
    rw [aeval_genMat_det] at this ⊢
    rw [blk_det]; exact this
  have hu1 : IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => blk XX ((b * g).map φ) x.1 x.2)
      (genMat O (r + 1 + 1)).det) := by
    have := mapC_unit (O := O) (Fin (r + 1)) (b * g) hbg
    rw [aeval_genMat_det] at this ⊢
    rw [blk_det]; exact this
  have hu1' : IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) =>
      (lowM (((1 : (MvPolynomial (Fin (r + 1)) A)ˣ)) : MvPolynomial (Fin (r + 1)) A) (fun _ => 0) (b.map φ) *
        blk XX (g.map φ)) x.1 x.2) (genMat O (r + 1 + 1)).det) := by
    rw [← hmul]; exact hu1
  let u' : Fin (r + 1) → (MvPolynomial (Fin (r + 1)) A)ˣ :=
    fun i => Units.map ((φ : A →+* MvPolynomial (Fin (r + 1)) A) : A →* MvPolynomial (Fin (r + 1)) A) (u i)
  have key := HB_low hf (1 : (MvPolynomial (Fin (r + 1)) A)ˣ) (fun _ => 0) (b.map φ) u'
    (fun i j hij => by rw [Matrix.map_apply, hlow i j hij, map_zero])
    (fun i => by rw [Matrix.map_apply, hdiag i]; rfl) XX (g.map φ) hu2 hu1'
  rw [← evalG_congr hmul hu1 hu1', ← RES_eval XX ((b * g).map φ) (mapC_unit _ (b * g) hbg) hM hu1,
    ← RES_eval XX (g.map φ) (mapC_unit _ g hg) hM hu2, resEv_const, resEv_const] at key
  have hchi : (((1 : (MvPolynomial (Fin (r + 1)) A)ˣ) ^ c * ∏ i, u' i ^ ka i : (MvPolynomial (Fin (r + 1)) A)ˣ) :
      MvPolynomial (Fin (r + 1)) A) = C ((chiB (ka 0) (fun i => ka i.succ) u : Aˣ) : A) := by
    have h1 : ((1 : (MvPolynomial (Fin (r + 1)) A)ˣ) ^ c * ∏ i, u' i ^ ka i) =
        Units.map ((φ : A →+* MvPolynomial (Fin (r + 1)) A) : A →* MvPolynomial (Fin (r + 1)) A)
          (chiB (ka 0) (fun i => ka i.succ) u) := by
      unfold chiB
      rw [one_zpow, one_mul, Fin.prod_univ_succ, map_mul, map_zpow, map_prod]
      simp only [map_zpow]
      rfl
    rw [h1]
    rfl
  rw [hchi] at key
  have := congrArg (fun P => coeff m P) key
  simp only [coeff_map, coeff_C_mul] at this
  exact this

theorem HB_of_universal (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ)
    (f₁ : GLCoord O (r + 1))
    (hG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => G0 O (r + 1) x.1 x.2) (genMat O (r + 1)).det))
    (hBG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => (B0 O (r + 1) * G0 O (r + 1)) x.1 x.2)
      (genMat O (r + 1)).det))
    (hE : evalG (R := O) (B0 O (r + 1) * G0 O (r + 1)) hBG0 f₁ =
      (chiB c ka (fun i => (lower_triangular_base_diag_isUnit O (r + 1) i).unit) : UA O (r + 1)) * evalG (R := O) (G0 O (r + 1)) hG0 f₁) :
    f₁ ∈ HB O r c ka := by
  intro A _ _ b g u hg hbg hlow hdiag
  let U0 : Fin (r + 1) → (UA O (r + 1))ˣ := fun i => (lower_triangular_base_diag_isUnit O (r + 1) i).unit
  have hdetg : IsUnit g.det := by rwa [aeval_genMat_det] at hg
  have hbu : ∀ i, IsUnit (b i i) := fun i => by rw [hdiag i]; exact Units.isUnit _
  let φ := spec O (r + 1) b g hbu hdetg
  have hφB : (B0 O (r + 1)).map φ = b := by
    ext i j
    simp only [Matrix.map_apply, B0, uB]
    rw [spec_alg]
    split_ifs with h
    · rw [aeval_X]; rfl
    · rw [map_zero, hlow i j (not_le.mp h)]
  have hφG : (G0 O (r + 1)).map φ = g := by
    ext i j
    simp only [Matrix.map_apply, G0, uG]
    rw [spec_alg, aeval_X]; rfl
  have hφBG : (B0 O (r + 1) * G0 O (r + 1)).map φ = b * g := by
    rw [Matrix.map_mul, hφB, hφG]
  have hφU : (fun i => Units.map ((φ : UA O (r + 1) →+* A) : UA O (r + 1) →* A) (U0 i)) = u := by
    funext i
    apply Units.ext
    have : φ (B0 O (r + 1) i i) = b i i := by
      have := congrFun (congrFun hφB i) i
      simpa using this
    rw [← hdiag i, ← this]
    rfl
  have h1 := congrArg φ hE
  rw [map_mul, evalG_map φ _ hBG0 (by rw [hφBG]; exact hbg), evalG_map φ _ hG0 (by rw [hφG]; exact hg),
    evalG_congr hφBG _ hbg, evalG_congr hφG _ hg] at h1
  rw [h1]
  congr 1
  have h2 := chiB_map (φ : UA O (r + 1) →+* A) c ka U0
  rw [hφU] at h2
  exact h2

theorem HB_of_smul (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ) (a : O) (ha : a ≠ 0)
    (f₁ : GLCoord O (r + 1)) (hf : algebraMap O (GLCoord O (r + 1)) a * f₁ ∈ HB O r c ka) : f₁ ∈ HB O r c ka := by
  have hG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => G0 O (r + 1) x.1 x.2) (genMat O (r + 1)).det) := by
    rw [aeval_genMat_det]; exact base_matrix_det_isUnit O (r + 1)
  have hBG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => (B0 O (r + 1) * G0 O (r + 1)) x.1 x.2)
      (genMat O (r + 1)).det) := by
    rw [aeval_genMat_det, Matrix.det_mul]; exact (lower_triangular_base_det_isUnit O (r + 1)).mul (base_matrix_det_isUnit O (r + 1))
  refine HB_of_universal O r c ka f₁ hG0 hBG0 ?_
  have hlow0 : ∀ i j, i < j → B0 O (r + 1) i j = 0 := by
    intro i j hij
    simp [B0, uB, not_le.mpr hij]
  have h0 := hf (UA O (r + 1)) (B0 O (r + 1)) (G0 O (r + 1)) (fun i => (lower_triangular_base_diag_isUnit O (r + 1) i).unit) hG0 hBG0 hlow0
    (fun i => rfl)
  rw [map_mul, map_mul, evalG_algebraMap, evalG_algebraMap] at h0
  have hne : algebraMap O (UA O (r + 1)) a ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply O (MvPolynomial (UV (r + 1)) O) (UA O (r + 1))]
    intro h
    have h1 := UA_inj O (r + 1) (h.trans (map_zero _).symm)
    rw [MvPolynomial.algebraMap_eq] at h1
    exact ha (C_injective _ _ (h1.trans C_0.symm))
  apply mul_left_cancel₀ hne
  rw [h0]; ring

theorem res_sat (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r : ℕ) (c : ℤ)
    (ka : Fin (r + 1) → ℤ)
    (hM : IsUnit (aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => resMat O r x.1 x.2) (genMat O (r + 1 + 1)).det))
    (f : GLCoord O (r + 1 + 1)) (hf : f ∈ HB O (r + 1) c ka) (a : O)
    (F : MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1))) (ha : a ≠ 0)
    (hF : evalG (R := O) (resMat O r) hM f = algebraMap O _ a * F) :
    ∃ f' ∈ HB O (r + 1) c ka, evalG (R := O) (resMat O r) hM f' = F := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, hau⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have h1 := cellFormula O r hf hM
  rw [hF, map_mul, AlgHom.commutes] at h1
  have hdv : algebraMap _ (GLCoord O (r + 1 + 1)) (C ϖ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1) ) O) ^ k ∣ f := by
    refine cell_pow_dvd O (r + 1) (C ϖ) ((MvPolynomial.prime_C_iff _).2 hϖ.prime) ?_ k f ?_
    · unfold evOne
      rw [aeval_C]
      exact hϖ.not_isUnit
    · refine ⟨algebraMap O (CA O (r + 1)) (u : O) * (((gam O (r + 1) ^ c : (CA O (r + 1))ˣ) : CA O (r + 1)) *
        resEv (cW O (r + 1)) (cD O (r + 1)) (cD_unit O (r + 1)) F), ?_⟩
      have h2 : algebraMap (GLCoord O (r + 1 + 1)) (CA O (r + 1)) f = iotaA O (r + 1) f := rfl
      have h3 : algebraMap (GLCoord O (r + 1 + 1)) (CA O (r + 1)) (algebraMap _ (GLCoord O (r + 1 + 1))
          (C ϖ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) O)) = algebraMap O (CA O (r + 1)) ϖ := by
        rw [IsScalarTower.algebraMap_apply O (GLCoord O (r + 1 + 1)) (CA O (r + 1)),
          IsScalarTower.algebraMap_apply O (MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) O) (GLCoord O (r + 1 + 1)),
          MvPolynomial.algebraMap_eq]
      rw [h2, h1, h3, hau, map_mul, map_pow]
      ring
  obtain ⟨f0, hf0⟩ := hdv
  have hCa : algebraMap O (GLCoord O (r + 1 + 1)) a =
      algebraMap _ (GLCoord O (r + 1 + 1)) (C ϖ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) O) ^ k *
        algebraMap O (GLCoord O (r + 1 + 1)) (u : O) := by
    rw [hau, map_mul, map_pow,
      IsScalarTower.algebraMap_apply O (MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) O) (GLCoord O (r + 1 + 1)) ϖ,
      MvPolynomial.algebraMap_eq]
    ring
  set f' : GLCoord O (r + 1 + 1) := algebraMap O (GLCoord O (r + 1 + 1)) ((u⁻¹ : Oˣ) : O) * f0 with hf'
  have hff : f = algebraMap O (GLCoord O (r + 1 + 1)) a * f' := by
    rw [hf0, hCa, hf']
    have : algebraMap O (GLCoord O (r + 1 + 1)) (u : O) * algebraMap O (GLCoord O (r + 1 + 1)) ((u⁻¹ : Oˣ) : O) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc _ = algebraMap _ (GLCoord O (r + 1 + 1)) (C ϖ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) O) ^ k *
          (algebraMap O (GLCoord O (r + 1 + 1)) (u : O) * algebraMap O (GLCoord O (r + 1 + 1)) ((u⁻¹ : Oˣ) : O)) * f0 := by
            rw [this, mul_one]
      _ = _ := by ring
  refine ⟨f', HB_of_smul O (r + 1) c ka a ha f' (hff ▸ hf), ?_⟩
  have h4 : algebraMap O (MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1))) a * evalG (R := O) (resMat O r) hM f' =
      algebraMap O _ a * F := by
    rw [← hF]
    conv_rhs => rw [hff, map_mul, evalG_algebraMap]
  have hne : algebraMap O (MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1))) a ≠ 0 := by
    rw [MvPolynomial.algebraMap_apply]
    intro h
    have h5 := C_injective _ _ (h.trans C_0.symm)
    rw [IsScalarTower.algebraMap_apply O (MvPolynomial (Fin (r + 1) × Fin (r + 1)) O) (GLCoord O (r + 1))] at h5
    have h6 := GL_inj O (r + 1) (h5.trans (map_zero _).symm)
    rw [MvPolynomial.algebraMap_eq] at h6
    exact ha (C_injective _ _ (h6.trans C_0.symm))
  exact mul_left_cancel₀ hne h4

theorem residue_division_transfer (D : Formalism.BasicNotions.D7) : adm7 D := by
  intro O _ _ _ r c ka
  refine ⟨res_unit O r, fun hM => ⟨fun f hf f' hf' h => res_inj O r c ka hM f hf f' hf' h,
    fun f hf m => res_coeff O r c ka hM f hf m,
    fun f hf a F ha _ hF => res_sat O r c ka hM f hf a F ha hF,
    fun f hf e => res_div O r c ka hM f hf e⟩⟩

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.G

theorem integral_form_exponent_le_ceil (p a r n : ℕ) (hn : n + 1 ≤ r) (l : ℕ) (hl : l ≤ 8 * a) :
    N0 (n + 1) * deF p (n + 1) l ≤ ⌈Formalism.MainNotions.flipOneThree.kappaOneExponent p a r⌉₊ := by
  have hN0 : N0 (n + 1) ≤ r ^ 2 := by
    unfold N0
    calc (n + 1) * (n + 1 - 1) / 2 ≤ (n + 1) * (n + 1 - 1) := Nat.div_le_self _ _
      _ ≤ r * r := Nat.mul_le_mul hn (by omega)
      _ = r ^ 2 := (sq r).symm
  have hde : deF p (n + 1) l ≤ Nat.log p (8 * a + r) := by
    unfold deF
    exact Nat.log_mono_right (by omega)
  have hlog : (Nat.log p (8 * a + r) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + r) := by
    have := Real.natLog_le_logb (8 * a + r) p
    push_cast at this
    exact this
  have h1 : ((N0 (n + 1) * deF p (n + 1) l : ℕ) : ℝ) ≤ Formalism.MainNotions.flipOneThree.kappaOneExponent p a r := by
    unfold Formalism.MainNotions.flipOneThree.kappaOneExponent Formalism.MainNotions.flipOneThree.lgA
    have hA : ((N0 (n + 1) : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast hN0
    have hB : ((deF p (n + 1) l : ℕ) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + r) :=
      (Nat.cast_le.mpr hde).trans hlog
    have hB0 : (0 : ℝ) ≤ ((deF p (n + 1) l : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith [sq_nonneg (r : ℝ)]
  exact_mod_cast h1.trans (Nat.le_ceil _)

theorem mq_top_of_irr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n : ℕ} [NeZero n]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) (hirr : IsIrrHW E lam v)
    (M : Submodule O V) (hM : UZLattice (O := O) E M) (hv : v ∈ M) : MQ (K := KK O) M = ⊤ := by
  have hE : ∀ a b, ∀ y ∈ MQ (K := KK O) M, E a b y ∈ MQ (K := KK O) M := by
    intro a b y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      apply Submodule.subset_span
      by_cases hab : a = b
      · subst hab
        have hg : binomE E a 1 ∈ UZgens E := Or.inr ⟨a, 1, rfl⟩
        have := hM.1 _ hg x hx
        simpa [binomE] using this
      · have hg : divPowE E a b 1 ∈ UZgens E := Or.inl ⟨a, b, 1, hab, rfl⟩
        have := hM.1 _ hg x hx
        simpa [divPowE] using this
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
  have hU : ∀ u ∈ Umon E, ∀ y ∈ MQ (K := KK O) M, u y ∈ MQ (K := KK O) M := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hu
      exact hE a b
    | one => intro y hy; simpa using hy
    | mul u w _ _ hu hw => intro y hy; simpa using hu _ (hw y hy)
  rw [eq_top_iff, ← hirr.2.2.2]
  apply Submodule.span_le.mpr
  rintro x ⟨u, hu, rfl⟩
  exact hU u hu v (Submodule.subset_span hv)

theorem weight_condition_of_integral_form (D : Formalism.BasicNotions.D7) (X : Formalism.MainNotions.flipOneThree.Inst) (h : Formalism.MainNotions.CovariantDegrees.NablaDeltaComparisonField D) :
    Formalism.MainNotions.flipOneThree.adm2 D X := by
  intro n V _ _ _ _ E lam v hn _ hirr hl
  obtain ⟨hA, hB⟩ := h X.p X.L.n' X.O X.setting X.instance_ring_standard (n + 1) lam V E v hirr
  refine ⟨fun x hx => ?_, fun M hM hv hwt => ?_⟩
  · have hx' := hA x hx
    have hle := integral_form_exponent_le_ceil X.p X.L.a X.r n hn (ellWt lam) hl
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    have : ((X.p : KK X.O) ^ ⌈Formalism.MainNotions.flipOneThree.kappaOneExponent X.p X.L.a X.r⌉₊) • x =
        ((X.p : X.O) ^ k) • (((X.p : X.O) ^ (N0 (n + 1) * deF X.p (n + 1) (ellWt lam))) • x) := by
      rw [hk, smul_smul, ← pow_add, add_comm, ← algebraMap_smul (KK X.O) (((X.p : X.O)) ^ _ )]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ hx'
  · apply hB M hM (mq_top_of_irr E lam v hirr M hM hv)
    intro x
    constructor
    · rintro ⟨hxM, hxw⟩
      exact hwt x hxM hxw
    · rintro ⟨c, rfl⟩
      refine ⟨M.smul_mem c hv, ?_⟩
      rw [← algebraMap_smul (KK X.O) c v]
      exact Submodule.smul_mem _ _ hirr.2.2.1.2.1

theorem weight_condition_from_integral_form (D : Formalism.BasicNotions.D7) (X : Formalism.MainNotions.flipOneThree.Inst) : Formalism.MainNotions.flipOneThree.adm2 D X :=
  weight_condition_of_integral_form D X (Formalism.MainNotions.G.GLWeightTheory.nabla_delta_comparison_field D)

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.MainNotions.G MvPolynomial

def subOps (K : Type) [Field K] {N r n : ℕ} (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r) :
    GLOps n K (MvPolynomial (Fin N × Fin r) K) :=
  fun a b => glAct K Lt S (φ a) (φ b)

theorem chOps_eq {K : Type} [Field K] {N r : ℕ} (LL : ChainLetters N) (j : ℕ) :
    chOps (R := K) (r := r) LL j = subOps K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} id := rfl

theorem chOps'_eq {K : Type} [Field K] {N r : ℕ} (LL : ChainLetters N) (j : ℕ) :
    chOps' (R := K) (r := r) LL j =
      subOps K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} (Fin.castLE (Nat.sub_le r 1)) := rfl

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees MvPolynomial Finset

section Rep

variable {K : Type} [Field K] {N r n : ℕ}

theorem subOps_apply (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r) (a b : Fin n) :
    subOps K Lt S φ a b = glOps K r Lt S (φ a) (φ b) := rfl

theorem weightSp_le_sub (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r) (mu : Fin r → ℤ) :
    weightSp (glOps K r Lt S) mu ≤ weightSp (subOps K Lt S φ) (mu ∘ φ) := by
  intro x hx
  rw [mem_weightSpace_iff_diag] at hx ⊢
  intro a
  exact hx (φ a)

theorem subOps_rep (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r) (hφ : Function.Injective φ) :
    IsGLRep (subOps K Lt S φ) := by
  obtain ⟨h1, h2, h3⟩ := polynomial_isGLRep (K := K) (n := r) Lt S
  refine ⟨fun a b c d => ?_, fun x => ?_, ?_⟩
  · have := h1 (φ a) (φ b) (φ c) (φ d)
    simp only [subOps_apply]
    rw [this]
    simp only [hφ.eq_iff]
  · obtain ⟨W, hW, hx, hst⟩ := h2 x
    exact ⟨W, hW, hx, fun a b y hy => hst (φ a) (φ b) y hy⟩
  · rw [eq_top_iff, ← h3]
    exact iSup_le fun mu => (weightSp_le_sub Lt S φ mu).trans (le_iSup (weightSp (subOps K Lt S φ)) (mu ∘ φ))

theorem subOps_wt [CharZero K] (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r) (mu : Fin n → ℤ)
    (F : MvPolynomial (Fin N × Fin r) K) (hF : F ∈ weightSp (subOps K Lt S φ) mu) (m : Fin N × Fin r →₀ ℕ)
    (hm : m ∈ F.support) : (wtS Lt S m) ∘ φ = mu := by
  funext a
  have h1 := (mem_weightSpace_iff_diag _ mu F).1 hF a
  rw [subOps_apply, gl_operator_apply_derivation] at h1
  have h2 := congrArg (coeff m) h1
  rw [diagonal_derivation_coeff, coeff_smul, smul_eq_mul] at h2
  have h3 : coeff m F ≠ 0 := by simpa using hm
  have h4 := mul_right_cancel₀ h3 h2
  show wtS Lt S m (φ a) = mu a
  exact_mod_cast h4

theorem uzgens_sub (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r) (hφ : Function.Injective φ) :
    UZgens (subOps K Lt S φ) ⊆ UZgens (glOps K r Lt S) := by
  rintro u (⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩)
  · exact Or.inl ⟨φ a, φ b, k, fun h => hab (hφ h), rfl⟩
  · exact Or.inr ⟨φ a, k, rfl⟩

end Rep

section Abs

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem isoProj_of_set (E : GLOps n K V) (lam : Fin n → ℤ) (e : Module.End K V) (h : IsIsoProjSet E {lam} e) :
    IsIsoProj E lam e :=
  ⟨fun x hx => h.1 lam rfl x hx, fun mu hmu x hx => h.2 mu (by simpa using hmu) x hx⟩

open Classical in

theorem setProj_eq_sum (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (T : Set (Fin n → ℤ))
    (e : Module.End K V) (he : IsIsoProjSet E T e) (ee : (Fin n → ℤ) → Module.End K V)
    (hee : ∀ lam, IsIsoProj E lam (ee lam)) (x : V) :
    ∃ A : Finset (Fin n → ℤ), ∀ B : Finset (Fin n → ℤ), A ⊆ B → e x = ∑ mu ∈ B.filter (· ∈ T), ee mu x := by
  have hx : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; exact Submodule.mem_top
  induction hx using Submodule.iSup_induction' with
  | mem nu x hx =>
    refine ⟨{nu}, fun B hB => ?_⟩
    have hnu : nu ∈ B := hB (Finset.mem_singleton_self nu)
    by_cases hnT : nu ∈ T
    · rw [he.1 nu hnT x hx, Finset.sum_eq_single nu]
      · exact ((hee nu).1 x hx).symm
      · intro mu _ hmu
        exact (hee mu).2 nu (Ne.symm hmu) x hx
      · intro h
        exact absurd (Finset.mem_filter.2 ⟨hnu, hnT⟩) h
    · rw [he.2 nu hnT x hx]
      refine (Finset.sum_eq_zero fun mu hmu => ?_).symm
      have hne : nu ≠ mu := fun h => hnT (h ▸ (Finset.mem_filter.1 hmu).2)
      exact (hee mu).2 nu hne x hx
  | zero => exact ⟨∅, fun B _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A1, h1⟩ := hx
    obtain ⟨A2, h2⟩ := hy
    refine ⟨A1 ∪ A2, fun B hB => ?_⟩
    rw [map_add, h1 B (Finset.union_subset_left hB), h2 B (Finset.union_subset_right hB), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun mu _ => (map_add _ _ _).symm

end Abs

open Classical in

theorem subOps_int (D : Formalism.BasicNotions.D7) (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S0 : UniformizedDVR p O) (hG : AdmissibleDVR p n' O) (N r n : ℕ) (hn : 0 < n) (Lt : Letters (Fin N)) (S : Set (Fin N))
    (φ : Fin n → Fin r) (hφ : Function.Injective φ)
    (hEx : ∀ lam : Fin n → ℤ, ∃ e, IsIsoProjSet (subOps (KK O) Lt S φ) {lam} e)
    (d : Fin N → ℕ) (T : Set (Fin n → ℤ)) (e : Module.End (KK O) (MvPolynomial (Fin N × Fin r) (KK O)))
    (he : IsIsoProjSet (subOps (KK O) Lt S φ) T e) :
    (∀ F ∈ Pol (KK O) r d, e F ∈ Pol (KK O) r d) ∧
    ∀ L : Submodule O (MvPolynomial (Fin N × Fin r) (KK O)),
      (∀ u ∈ UZgens (glOps (KK O) r Lt S), ∀ F ∈ L, u F ∈ L) → (latticeMultidegreePart L d).FG →
      MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ →
      ∀ F ∈ Pol (KK O) r d, F ∈ L →
        ((p : KK O) ^ (N0 n * Nat.log p (2 * degIn d S + n - 1))) • e F ∈ L := by
  have hchar : CharZero (KK O) := (integral_formula_lattice_holds p n' O S0 hG).1
  have hCR : CompleteReducibilityIsotypic := complete_reducibility_of_semisimple D (Formalism.MainNotions.G.GLWeightTheory.weight_condition_from_integral_form D)
  have hRes : SubrepRestrictionRep := subrep_restriction_of_reducibility hCR
  have hRep : IsGLRep (subOps (KK O) Lt S φ) := subOps_rep Lt S φ hφ
  have hst : ∀ a b, ∀ x ∈ Pol (KK O) r d, subOps (KK O) Lt S φ a b x ∈ Pol (KK O) r d :=
    fun a b x hx => gl_operator_preserves_multidegree Lt S d (φ a) (φ b) x hx
  obtain ⟨hR1, hR2, hR3, hR4, hR5, hR6⟩ := hRes (KK O) _ n (subOps (KK O) Lt S φ) hRep (Pol (KK O) r d) hst
  choose ee hee0 using hEx
  have hee : ∀ lam, IsIsoProj (subOps (KK O) Lt S φ) lam (ee lam) := fun lam => isoProj_of_set _ lam _ (hee0 lam)
  choose ee' hee' hcoe using fun lam => hR5 lam (ee lam) (hee lam)
  have hTop := hCR (KK O) _ n (subOps (KK O) Lt S φ) hRep

  have hsum : ∀ F ∈ Pol (KK O) r d, ∃ Sw : Finset (Fin n → ℤ),
      (∀ lam ∈ Sw, ∃ v : Pol (KK O) r d, IsHWV (restrictStableOperators (subOps (KK O) Lt S φ) (Pol (KK O) r d) hst) lam v) ∧
      e F = ∑ lam ∈ Sw, ee lam F := by
    intro F hF
    obtain ⟨A, hA⟩ := setProj_eq_sum _ hTop T e he ee hee F
    refine ⟨(A.filter (· ∈ T)).filter
      (fun lam => ∃ v : Pol (KK O) r d, IsHWV (restrictStableOperators (subOps (KK O) Lt S φ) (Pol (KK O) r d) hst) lam v),
      fun lam hlam => (Finset.mem_filter.1 hlam).2, ?_⟩
    rw [hA A (Finset.Subset.refl A), Finset.sum_filter
      (p := fun lam => ∃ v : Pol (KK O) r d, IsHWV (restrictStableOperators (subOps (KK O) Lt S φ) (Pol (KK O) r d) hst) lam v)]
    refine Finset.sum_congr rfl fun lam _ => ?_
    split_ifs with hv
    · rfl
    · exact hR6 lam (ee lam) (hee lam) hv F hF
  refine ⟨fun F hF => ?_, ?_⟩
  · obtain ⟨Sw, -, hs⟩ := hsum F hF
    rw [hs]
    refine Submodule.sum_mem _ fun lam _ => ?_
    rw [← hcoe lam ⟨F, hF⟩]
    exact (ee' lam ⟨F, hF⟩).2
  intro L hL hFG hMQ F hF hFL
  obtain ⟨Sw, hSw, hs⟩ := hsum F hF
  have : NeZero n := ⟨hn.ne'⟩
  have := homogeneous_multidegree_findim (K := KK O) (n := r) d
  have hwt : ∀ (mu : Fin n → ℤ) (x : Pol (KK O) r d), x ≠ 0 →
      x ∈ weightSp (restrictStableOperators (subOps (KK O) Lt S φ) (Pol (KK O) r d) hst) mu →
      ∃ m : Fin N × Fin r →₀ ℕ, (∀ i, multideg m i = d i) ∧ (wtS Lt S m) ∘ φ = mu := by
    intro mu x hx0 hx
    have h1 : (x : MvPolynomial (Fin N × Fin r) (KK O)) ≠ 0 := fun h => hx0 (Subtype.ext h)
    obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 h1
    refine ⟨m, ?_, subOps_wt Lt S φ mu _ ((hR2 mu x).1 hx) m hm⟩
    have h2 := (MvPolynomial.mem_restrictSupport_iff (KK O)).1 x.2
    exact h2 (by simpa using hm)
  have hdom : ∀ lam ∈ Sw, Dominant lam := fun lam hlam => by
    obtain ⟨v, hv⟩ := hSw lam hlam
    exact highest_weight_dominant_holds (KK O) _ n _ hR1 lam v hv
  have hUZ : UZLattice (O := O) (restrictStableOperators (subOps (KK O) Lt S φ) (Pol (KK O) r d) hst) (latticeMultidegreePart L d) := by
    refine ⟨?_, hFG⟩
    intro u hu x hx
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · show ((divPowE _ a b k x : Pol (KK O) r d) : MvPolynomial (Fin N × Fin r) (KK O)) ∈ L
      rw [hR3]
      exact hL _ (uzgens_sub Lt S φ hφ (Or.inl ⟨a, b, k, hab, rfl⟩)) _ hx
    · show ((binomE _ a k x : Pol (KK O) r d) : MvPolynomial (Fin N × Fin r) (KK O)) ∈ L
      rw [hR4]
      exact hL _ (uzgens_sub Lt S φ hφ (Or.inr ⟨a, k, rfl⟩)) _ hx
  have key := isotypic_projector_theorem_field D p n' O S0 hG n _ _ hR1 (latticeMultidegreePart L d) hUZ hMQ Sw hdom ee'
    (fun lam _ => hee' lam) ⟨F, hF⟩ hFL
  have key2 : ((p : O) ^ (Sw.sup fun lam => N0 n * deF p n
      (ellOf (restrictStableOperators (subOps (KK O) Lt S φ) (Pol (KK O) r d) hst) (MQ (K := KK O) (latticeMultidegreePart L d)) + ellWt lam))) •
      e F ∈ L := by
    have h1 : ((∑ lam ∈ Sw, ee' lam ⟨F, hF⟩ : Pol (KK O) r d) : MvPolynomial (Fin N × Fin r) (KK O)) = e F := by
      rw [hs, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun lam _ => hcoe lam ⟨F, hF⟩
    rw [← h1]
    exact key
  have hb1 : ellOf (restrictStableOperators (subOps (KK O) Lt S φ) (Pol (KK O) r d) hst) (MQ (K := KK O) (latticeMultidegreePart L d)) ≤
      degIn d S := by
    unfold ellOf
    apply csSup_le'
    rintro k ⟨mu, hmu, nu, hnu, a, b, hab, heq⟩
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hmu
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hnu
    obtain ⟨m, hm, rfl⟩ := hwt mu x hx0 hx.1
    obtain ⟨m', hm', rfl⟩ := hwt nu y hy0 hy.1
    have h1 := polynomial_weight_difference_le Lt S d m m' hm hm' (φ a) (φ a)
    have h2 := congrFun heq a
    simp [rootW, hab] at h2
    omega
  have hb2 : ∀ lam ∈ Sw, ellWt lam ≤ degIn d S := by
    intro lam hlam
    obtain ⟨v, hv⟩ := hSw lam hlam
    obtain ⟨m, hm, rfl⟩ := hwt lam v hv.1 hv.2.1
    have h1 := polynomial_weight_difference_le Lt S d m m hm hm (φ 0) (φ (lastIdx n))
    unfold ellWt
    simp only [Function.comp_apply]
    omega
  have hle : (Sw.sup fun lam => N0 n * deF p n
      (ellOf (restrictStableOperators (subOps (KK O) Lt S φ) (Pol (KK O) r d) hst) (MQ (K := KK O) (latticeMultidegreePart L d)) + ellWt lam)) ≤
      N0 n * Nat.log p (2 * degIn d S + n - 1) := by
    refine Finset.sup_le fun lam hlam => ?_
    apply Nat.mul_le_mul_left
    unfold deF
    apply Nat.log_mono_right
    have := hb2 lam hlam
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
  rw [← prime_pow_smul_cast, hj, add_comm, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ key2

theorem subOps_int_lat (D : Formalism.BasicNotions.D7) (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S0 : UniformizedDVR p O) (hG : AdmissibleDVR p n' O) (N r n : ℕ) (hn : 0 < n) (Lt : Letters (Fin N)) (S : Set (Fin N))
    (φ : Fin n → Fin r) (hφ : Function.Injective φ)
    (hEx : ∀ lam : Fin n → ℤ, ∃ e, IsIsoProjSet (subOps (KK O) Lt S φ) {lam} e)
    (d : Fin N → ℕ) (T : Set (Fin n → ℤ)) (e : Module.End (KK O) (MvPolynomial (Fin N × Fin r) (KK O)))
    (he : IsIsoProjSet (subOps (KK O) Lt S φ) T e) (e1 : ℕ)
    (he1 : N0 n * Nat.log p (2 * degIn d S + n - 1) ≤ e1) :
    ∀ F ∈ Pol (KK O) r d,
      (F ∈ IntPol O (Fin N × Fin r) → ((p : KK O) ^ e1) • e F ∈ IntPol O (Fin N × Fin r)) ∧
      (InBB (O := O) p F → InBB (O := O) p (((p : KK O) ^ e1) • e F)) := by
  obtain ⟨-, hLat⟩ := integral_formula_lattice_holds p n' O S0 hG
  obtain ⟨-, hst, BBs, hBB, hd⟩ := hLat r (Fin N) Lt
  obtain ⟨hFG1, hMQ1, hFG2, hMQ2⟩ := hd d
  obtain ⟨-, hint⟩ := subOps_int D p n' O S0 hG N r n hn Lt S φ hφ hEx d T e he
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le he1
  have hup : ∀ (L : Submodule O (MvPolynomial (Fin N × Fin r) (KK O))) (y : MvPolynomial (Fin N × Fin r) (KK O)),
      ((p : KK O) ^ (N0 n * Nat.log p (2 * degIn d S + n - 1))) • y ∈ L → ((p : KK O) ^ e1) • y ∈ L := by
    intro L y hy
    rw [← prime_pow_smul_cast] at hy ⊢
    rw [hj, add_comm, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ hy
  intro F hF
  refine ⟨fun hFL => hup _ _ (hint _ (fun u hu G hGL => (hst S u hu).1 G hGL) hFG1 hMQ1 F hF hFL), fun hFL => ?_⟩
  rw [← hBB]
  exact hup _ _ (hint BBs (fun u hu G hGL => (hBB _).2 ((hst S u hu).2 G ((hBB _).1 hGL))) hFG2 hMQ2 F hF
    ((hBB _).2 hFL))

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

section abs

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem iso_indep_abs (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ lam mu : Fin n → ℤ, lam ≠ mu → ∀ x ∈ isoSub E lam, ∀ y ∈ isoSub E mu, B x y = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) : iSupIndep (isoSub E) := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply hnd
  intro y
  have hy : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  induction hy using Submodule.iSup_induction' with
  | mem mu y hy =>
    by_cases h : mu = i
    · subst h
      have hle : (⨆ (j : Fin n → ℤ) (_ : j ≠ mu), isoSub E j) ≤ LinearMap.ker (B.flip y) := by
        refine iSup₂_le fun j hj z hz => ?_
        rw [LinearMap.mem_ker, LinearMap.flip_apply]
        exact hB j mu hj z hz y hy
      have := hle hx'
      rwa [LinearMap.mem_ker, LinearMap.flip_apply] at this
    · exact hB i mu (Ne.symm h) x hx y hy
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]

theorem isoProjSet_exists_abs (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤)
    (hI : iSupIndep (isoSub E)) (T : Set (Fin n → ℤ)) : ∃ e, IsIsoProjSet E T e := by
  have hd : Disjoint (⨆ i ∈ T, isoSub E i) (⨆ i ∈ Tᶜ, isoSub E i) := hI.disjoint_biSup_biSup disjoint_compl_right
  have hc : Codisjoint (⨆ i ∈ T, isoSub E i) (⨆ i ∈ Tᶜ, isoSub E i) := by
    rw [codisjoint_iff, eq_top_iff, ← hT]
    refine iSup_le fun mu => ?_
    by_cases h : mu ∈ T
    · exact le_sup_of_le_left (le_iSup₂_of_le mu h le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le mu h le_rfl)
  have hC : IsCompl (⨆ i ∈ T, isoSub E i) (⨆ i ∈ Tᶜ, isoSub E i) := ⟨hd, hc⟩
  refine ⟨Submodule.projection _ _ hC, ?_, ?_⟩
  · intro lam hlam x hx
    have hxA : x ∈ (⨆ i ∈ T, isoSub E i) := (le_iSup₂_of_le lam hlam le_rfl : isoSub E lam ≤ _) hx
    exact Submodule.projection_apply_of_mem_left hC hxA
  · intro mu hmu x hx
    have hxB : x ∈ (⨆ i ∈ Tᶜ, isoSub E i) := (le_iSup₂_of_le mu hmu le_rfl : isoSub E mu ≤ _) hx
    exact Submodule.projection_apply_of_mem_right hC hxB

theorem isoProjSet_comm_abs (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (T : Set (Fin n → ℤ))
    (e : Module.End K V) (he : IsIsoProjSet E T e) (X : Module.End K V)
    (hX : ∀ mu, ∀ x ∈ isoSub E mu, X x ∈ isoSub E mu) : e * X = X * e := by
  ext x
  have hx : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  simp only [Module.End.mul_apply]
  induction hx using Submodule.iSup_induction' with
  | mem mu x hx =>
    by_cases h : mu ∈ T
    · rw [he.1 mu h x hx, he.1 mu h _ (hX _ x hx)]
    · rw [he.2 mu h x hx, he.2 mu h _ (hX _ x hx), map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]

theorem isoProjSet_selfadj_abs (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (T : Set (Fin n → ℤ))
    (e : Module.End K V) (he : IsIsoProjSet E T e) (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ lam mu : Fin n → ℤ, lam ≠ mu → ∀ x ∈ isoSub E lam, ∀ y ∈ isoSub E mu, B x y = 0) (x y : V) :
    B (e x) y = B x (e y) := by
  have hx : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  have hy : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  induction hx using Submodule.iSup_induction' with
  | mem mu x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem nu y hy =>
      by_cases h : mu ∈ T
      · rw [he.1 mu h x hx]
        by_cases h' : nu ∈ T
        · rw [he.1 nu h' y hy]
        · have hne : mu ≠ nu := fun hh => h' (hh ▸ h)
          rw [he.2 nu h' y hy, map_zero, hB mu nu hne x hx y hy]
      · rw [he.2 mu h x hx, map_zero, LinearMap.zero_apply]
        by_cases h' : nu ∈ T
        · have hne : mu ≠ nu := fun hh => h (hh ▸ h')
          rw [he.1 nu h' y hy, hB mu nu hne x hx y hy]
        · rw [he.2 nu h' y hy, map_zero]
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

end abs

section pol

variable {K : Type} [Field K] [CharZero K] {N r n : ℕ}

theorem fock_nondeg' {σ : Type} (F : MvPolynomial σ K) (h : ∀ G, fockBilinear K σ F G = 0) : F = 0 := by
  ext m
  have h1 := h (monomial m 1)
  rw [fockBilinear_apply, fock_form_symm, fock_form_monomial, one_mul] at h1
  have h2 : ((expFact m : ℕ) : K) ≠ 0 := by exact_mod_cast exponent_factorial_ne_zero_of m
  rw [coeff_zero]
  exact (mul_eq_zero.1 h1).resolve_right h2

theorem subOps_contra (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r) (a b : Fin n)
    (F G : MvPolynomial (Fin N × Fin r) K) :
    fockBilinear K (Fin N × Fin r) (subOps K Lt S φ a b F) G = fockBilinear K (Fin N × Fin r) F (subOps K Lt S φ b a G) :=
  fock_form_contravariant Lt S (φ a) (φ b) F G

theorem subOps_top (D : Formalism.BasicNotions.D7) (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r)
    (hRep : IsGLRep (subOps K Lt S φ)) : (⨆ mu : Fin n → ℤ, isoSub (subOps K Lt S φ) mu) = ⊤ :=
  complete_reducibility_of_semisimple D (Formalism.MainNotions.G.GLWeightTheory.weight_condition_from_integral_form D) K _ n _ hRep

theorem subOps_orth (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r)
    (hRep : IsGLRep (subOps K Lt S φ)) (lam mu : Fin n → ℤ) (h : lam ≠ mu)
    (x : MvPolynomial (Fin N × Fin r) K) (hx : x ∈ isoSub (subOps K Lt S φ) lam)
    (y : MvPolynomial (Fin N × Fin r) K) (hy : y ∈ isoSub (subOps K Lt S φ) mu) :
    fockBilinear K (Fin N × Fin r) x y = 0 :=
  contravariant_orthogonality_holds K _ n _ hRep (fockBilinear K (Fin N × Fin r)) (fun a b F G => subOps_contra Lt S φ a b F G) lam mu h x hx y hy

theorem iso_indep (D : Formalism.BasicNotions.D7) (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r)
    (hRep : IsGLRep (subOps K Lt S φ)) : iSupIndep (isoSub (subOps K Lt S φ)) :=
  iso_indep_abs _ (subOps_top D Lt S φ hRep) (fockBilinear K (Fin N × Fin r)) (subOps_orth Lt S φ hRep) fock_nondeg'

theorem subOps_exists (D : Formalism.BasicNotions.D7) (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r)
    (hRep : IsGLRep (subOps K Lt S φ)) (T : Set (Fin n → ℤ)) : ∃ e, IsIsoProjSet (subOps K Lt S φ) T e :=
  isoProjSet_exists_abs _ (subOps_top D Lt S φ hRep) (iso_indep D Lt S φ hRep) T

theorem subOps_selfadj (D : Formalism.BasicNotions.D7) (Lt : Letters (Fin N)) (S : Set (Fin N)) (φ : Fin n → Fin r)
    (hRep : IsGLRep (subOps K Lt S φ)) (T : Set (Fin n → ℤ)) (e : Module.End K (MvPolynomial (Fin N × Fin r) K))
    (he : IsIsoProjSet (subOps K Lt S φ) T e) (F G : MvPolynomial (Fin N × Fin r) K) :
    fock (e F) G = fock F (e G) :=
  isoProjSet_selfadj_abs _ (subOps_top D Lt S φ hRep) T e he (fockBilinear K (Fin N × Fin r)) (subOps_orth Lt S φ hRep) F G

theorem subOps_comm_op (D : Formalism.BasicNotions.D7) {n' : ℕ} (Lt : Letters (Fin N)) (S S' : Set (Fin N)) (hS : S ⊆ S')
    (φ : Fin n → Fin r) (φ' : Fin n' → Fin r) (hφ : ∀ a, ∃ a', φ' a = φ a')
    (hRep : IsGLRep (subOps K Lt S φ)) (T : Set (Fin n → ℤ)) (e : Module.End K (MvPolynomial (Fin N × Fin r) K))
    (he : IsIsoProjSet (subOps K Lt S φ) T e) (a b : Fin n') :
    e * subOps K Lt S' φ' a b = subOps K Lt S' φ' a b * e := by
  refine isoProjSet_comm_abs _ (subOps_top D Lt S φ hRep) T e he _ ?_
  intro mu x hx
  obtain ⟨a', ha⟩ := hφ a
  obtain ⟨b', hb⟩ := hφ b
  have h1 : subOps K Lt S' φ' a b = subOps K Lt S φ a' b' + glOps K r Lt (S' \ S) (φ' a) (φ' b) := by
    have := gl_operator_union_add (K := K) Lt S S' hS (φ' a) (φ' b)
    rw [ha, hb] at this ⊢
    show glOps K r Lt S' (φ' a) (φ' b) = _
    rw [ha, hb]
    exact this
  rw [h1, LinearMap.add_apply]
  refine Submodule.add_mem _ (isotypic_stable_gl_operator _ mu a' b' x hx) ?_
  refine isotypic_stable_commuting _ _ (fun c d => ?_) mu x hx
  exact (disjoint_letters_commute (K := K) Lt S (S' \ S) Set.disjoint_sdiff_right (φ c) (φ d) (φ' a) (φ' b)).symm

theorem subOps_comm (D : Formalism.BasicNotions.D7) {n' : ℕ} (Lt : Letters (Fin N)) (S S' : Set (Fin N)) (hS : S ⊆ S')
    (φ : Fin n → Fin r) (φ' : Fin n' → Fin r) (hφ : ∀ a, ∃ a', φ' a = φ a')
    (hRep : IsGLRep (subOps K Lt S φ)) (hRep' : IsGLRep (subOps K Lt S' φ'))
    (T : Set (Fin n → ℤ)) (T' : Set (Fin n' → ℤ)) (e e' : Module.End K (MvPolynomial (Fin N × Fin r) K))
    (he : IsIsoProjSet (subOps K Lt S φ) T e) (he' : IsIsoProjSet (subOps K Lt S' φ') T' e') :
    e * e' = e' * e := by
  refine (isoProjSet_comm_abs _ (subOps_top D Lt S' φ' hRep') T' e' he' e ?_).symm
  intro mu x hx
  exact isotypic_stable_commuting _ e (fun c d => subOps_comm_op D Lt S S' hS φ φ' hφ hRep T e he c d) mu x hx

theorem chOps_comm3 (D : Formalism.BasicNotions.D7) (LL : ChainLetters N)
    (hRep : ∀ j, IsGLRep (Formalism.MainNotions.flipOneThree.chOps (R := K) (r := r) LL j))
    (hRep' : ∀ j, IsGLRep (Formalism.MainNotions.flipOneThree.chOps' (R := K) (r := r) LL j)) (j j' : ℕ) (hjj : j ≤ j') :
    (∀ T T' e e', IsIsoProjSet (Formalism.MainNotions.flipOneThree.chOps (r := r) (R := K) LL j) T e →
        IsIsoProjSet (Formalism.MainNotions.flipOneThree.chOps (r := r) (R := K) LL j') T' e' → e * e' = e' * e) ∧
      (∀ T T' e e', IsIsoProjSet (Formalism.MainNotions.flipOneThree.chOps (r := r) (R := K) LL j) T e →
        IsIsoProjSet (Formalism.MainNotions.flipOneThree.chOps' (r := r) (R := K) LL j') T' e' → e * e' = e' * e) ∧
      (∀ T T' e e', IsIsoProjSet (Formalism.MainNotions.flipOneThree.chOps' (r := r) (R := K) LL j) T e →
        IsIsoProjSet (Formalism.MainNotions.flipOneThree.chOps' (r := r) (R := K) LL j') T' e' → e * e' = e' * e) := by
  have hS : {i : Fin N | (i : ℕ) < j} ⊆ {i : Fin N | (i : ℕ) < j'} := fun i hi => lt_of_lt_of_le hi hjj
  refine ⟨fun T T' e e' he he' => ?_, fun T T' e e' he he' => ?_, fun T T' e e' he he' => ?_⟩
  · exact subOps_comm D (⟨LL.vec⟩ : Letters (Fin N)) _ _ hS id id (fun a => ⟨a, rfl⟩) (hRep j) (hRep j') T T' e e' he he'
  · exact subOps_comm D (⟨LL.vec⟩ : Letters (Fin N)) _ _ hS id (Fin.castLE (Nat.sub_le r 1))
      (fun a => ⟨Fin.castLE (Nat.sub_le r 1) a, rfl⟩) (hRep j) (hRep' j') T T' e e' he he'
  · exact subOps_comm D (⟨LL.vec⟩ : Letters (Fin N)) _ _ hS (Fin.castLE (Nat.sub_le r 1))
      (Fin.castLE (Nat.sub_le r 1)) (fun a => ⟨a, rfl⟩) (hRep' j) (hRep' j') T T' e e' he he'

end pol

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial Finset

theorem mem_bbSpec_one_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    (hV : ValuationProperties p O) {σ : Type} (F : MvPolynomial σ (KK O)) :
    F ∈ bbSpec O p σ 1 ↔ InBB (O := O) p F := by
  constructor
  · intro h
    unfold bbSpec at h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨μ, c, hc, rfl⟩ := hx
      rw [fock_lattice_monomial_iff hV]
      unfold halfFactorialValuation
      simpa using hc
    | zero => exact fock_lattice_zero_mem hV
    | add x y _ _ hx hy => exact fock_lattice_add_mem hV hx hy
    | smul o x _ hx => exact fock_lattice_smul_mem hV o hx
  · intro h
    rw [F.as_sum]
    refine Submodule.sum_mem _ fun m _ => Submodule.subset_span ⟨m, F.coeff m, ?_, rfl⟩
    have := (fock_lattice_monomial_iff hV m _).1 ((fock_lattice_iff_monomials hV F).1 h m)
    unfold halfFactorialValuation at this
    simpa using this

theorem mem_bbSpec_one_iff' {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    (hp : p.Prime) (S0 : UniformizedDVR p O) {σ : Type} (F : MvPolynomial σ (KK O)) :
    F ∈ bbSpec O p σ 1 ↔ InBB (O := O) p F := mem_bbSpec_one_iff (valuation_properties_hold hp S0) F

theorem exp_le (p a r n d : ℕ) [Fact p.Prime] (hn : n ≤ r) (h : 2 * d + r ≤ p ^ 2 * (8 * a + r) ^ 2) :
    N0 n * Nat.log p (2 * d + n - 1) ≤ ⌈kappaOneExponent p a r⌉₊ := by
  have h1 : (Formalism.InvariantFactorPaths.PW.kapC p r (2 * d) : ℝ) ≤ (r : ℝ) ^ 2 * Formalism.GM.lgV2 p a r :=
    Formalism.InvariantFactorPaths.PW.kapC_le_real p r (2 * d) a h
  have h2 : N0 n * Nat.log p (2 * d + n - 1) ≤ Formalism.InvariantFactorPaths.PW.kapC p r (2 * d) := by
    unfold Formalism.InvariantFactorPaths.PW.kapC N0
    rw [← Nat.choose_two_right]
    exact Nat.mul_le_mul (Nat.choose_le_choose 2 hn) (Nat.log_mono_right (by omega))
  have h3 : ((N0 n * Nat.log p (2 * d + n - 1) : ℕ) : ℝ) ≤ kappaOneExponent p a r :=
    le_trans (by exact_mod_cast h2) h1
  exact_mod_cast h3.trans (Nat.le_ceil _)

theorem posAdd_cdist {n' : ℕ} (x s : Fin n') : posAdd x (cdist x s) = s := by
  apply Fin.ext
  unfold posAdd cdist
  simp only
  rw [Nat.add_mod_mod]
  have h1 : x.val + (s.val + n' - x.val) = s.val + n' := by have := x.2; omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt s.2]

theorem segPos_mem {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ TT := by
  have h : (segDists TT j).get i ∈ segDists TT j := List.get_mem _ _
  unfold segDists at h
  rw [Finset.mem_sort, Finset.mem_image] at h
  obtain ⟨s, hs, heq⟩ := h
  have : segPos TT j i = s := by
    unfold segPos
    rw [show (segDists TT j).get i = cdist (segStart TT j) s from heq.symm]
    exact posAdd_cdist _ _
  rw [this]
  exact (Finset.mem_filter.1 hs).1

theorem segNext_mem {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : segNext TT j ∈ TT := by
  have h : segNext TT j ∈ evenTops TT := List.get_mem _ _
  unfold evenTops at h
  rw [Finset.mem_sort] at h
  exact (Finset.mem_filter.1 h).1

section Deg

variable {s r p : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r)

theorem coarseA_le (i : Fin s) : coarseA p S b i ≤ S.bTop i :=
  (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem coarseC_le (i : Fin s) : coarseC p S aTop b i ≤ aTop i :=
  (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem base_exponent_le_a (hp : 1 ≤ p) (hE0 : 0 ≤ S.E0) : (S.A0 p : ℝ) ≤ S.a := by
  unfold SegData.A0
  refine (Int.floor_le _).trans ?_
  have hQ : (1 : ℝ) ≤ (S.Qj p : ℝ) := by
    unfold SegData.Qj
    exact_mod_cast Nat.one_le_pow _ _ hp
  rw [div_le_iff₀ (by linarith)]
  have ha : (0 : ℝ) ≤ S.a := Nat.cast_nonneg _
  nlinarith

theorem cap_le (hp : 1 ≤ p) (hE0 : 0 ≤ S.E0) (B : ℝ) (hB : ∀ i, (S.bTop i : ℝ) ≤ B) (l : ℕ) :
    (cap p S b l : ℝ) ≤ S.a + s * B := by
  have hB0 : ∀ i : Fin s, (0 : ℝ) ≤ B := fun i => le_trans (Nat.cast_nonneg _) (hB i)
  unfold cap
  push_cast
  have h1 : (∑ i : Fin s, (if (i : ℕ) < l then ((coarseA p S b i : ℝ) - (oEff S b i : ℝ)) else 0)) ≤
      ∑ _i : Fin s, B := by
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs
    · have h2 : ((coarseA p S b i : ℕ) : ℝ) ≤ S.bTop i := by exact_mod_cast coarseA_le S b i
      have h3 : (0 : ℝ) ≤ (oEff S b i : ℝ) := Nat.cast_nonneg _
      linarith [hB i]
    · exact hB0 i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have := base_exponent_le_a (p := p) S hp hE0
  linarith

theorem oPlus_le (hK : Kept p r S aTop b) (hp : 1 ≤ p) (hE0 : 0 ≤ S.E0) (hLa0 : 0 ≤ S.La)
    (hLa : S.La / ((r : ℝ) + 1) + 4 / (p : ℝ) ^ 2 ≤ 1) (B : ℝ) (hB : ∀ i, (S.bTop i : ℝ) ≤ B)
    (hBp : (S.bPlus : ℝ) ≤ B) : (b.oPlus : ℝ) ≤ S.a + s * B + 2 * S.a * s + B := by
  have h := hK.2.2.2
  unfold Oplus at h
  have ha : (0 : ℝ) ≤ S.a := Nat.cast_nonneg _
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have h4 : (0 : ℝ) ≤ 4 / (p : ℝ) ^ 2 := by positivity
  have hc0 : 0 ≤ S.La / ((r : ℝ) + 1) := div_nonneg hLa0 hr.le
  have hsum0 : (0 : ℝ) ≤ ∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hsum : (∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ)) ≤ 2 * S.a * s := by
    have : (∑ i : Fin s, 2 * (S.a : ℝ) / (S.P p i : ℝ)) ≤ ∑ _i : Fin s, 2 * (S.a : ℝ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hP : (1 : ℝ) ≤ (S.P p i : ℝ) := by
        unfold SegData.P
        exact_mod_cast Nat.one_le_pow _ _ hp
      exact div_le_self (by positivity) hP
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have h5 : (S.La / ((r : ℝ) + 1) + 4 / (p : ℝ) ^ 2) * ∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ) ≤ 2 * S.a * s :=
    (mul_le_of_le_one_left hsum0 hLa).trans hsum
  have hb0 : (0 : ℝ) ≤ S.bPlus := Nat.cast_nonneg _
  have h6 : S.La * (S.bPlus : ℝ) / ((r : ℝ) + 1) ≤ B := by
    have : S.La * (S.bPlus : ℝ) / ((r : ℝ) + 1) = S.La / ((r : ℝ) + 1) * S.bPlus := by ring
    rw [this]
    exact (mul_le_of_le_one_left hb0 (by linarith)).trans hBp
  have h7 := cap_le (p := p) S b hp hE0 B hB s
  linarith

theorem segChain_deg_le (hK : Kept p r S aTop b) (hp : 1 ≤ p) (hE0 : 0 ≤ S.E0) (hLa0 : 0 ≤ S.La)
    (hLa : S.La / ((r : ℝ) + 1) + 4 / (p : ℝ) ^ 2 ≤ 1) (A B : ℝ) (hB : ∀ i, (S.bTop i : ℝ) ≤ B)
    (hBp : (S.bPlus : ℝ) ≤ B) (hA : ∀ i, (aTop i : ℝ) ≤ A) (ha : (S.a : ℝ) ≤ A) (x : Fin (2 * s + 1)) :
    ((segChain p S aTop b).deg x : ℝ) ≤ A + s * B + 2 * A * s + B := by
  have hb0 : (0 : ℝ) ≤ B := le_trans (Nat.cast_nonneg _) hBp
  have ha0 : (0 : ℝ) ≤ A := le_trans (Nat.cast_nonneg _) ha
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
  have hsB : 0 ≤ (s : ℝ) * B := mul_nonneg hs0 hb0
  have hsA : 0 ≤ 2 * A * (s : ℝ) := by positivity
  have hbd : ∀ i : Fin s, ((coarseA p S b i : ℕ) : ℝ) ≤ B := fun i =>
    le_trans (by exact_mod_cast coarseA_le S b i) (hB i)
  have hcd : ∀ i : Fin s, ((coarseC p S aTop b i : ℕ) : ℝ) ≤ A := fun i =>
    le_trans (by exact_mod_cast coarseC_le S aTop b i) (hA i)
  unfold segChain
  simp only
  split_ifs with h1 h2 h3 h3
  · have := oPlus_le S aTop b hK hp hE0 hLa0 hLa B hB hBp
    have h8 : 2 * (S.a : ℝ) * s ≤ 2 * A * s := by nlinarith
    linarith
  · have h9 : b.w (topOf x h1) ≤ coarseA p S b (topOf x h1) := (hK.2.2.1 _ h3).2.1
    have : ((b.w (topOf x h1) : ℕ) : ℝ) ≤ B := le_trans (by exact_mod_cast h9) (hbd _)
    linarith
  · have h9 : b.o (topOf x h1) ≤ coarseA p S b (topOf x h1) := (hK.2.1 _ (not_lt.mp h3)).1
    have : ((b.o (topOf x h1) : ℕ) : ℝ) ≤ B := le_trans (by exact_mod_cast h9) (hbd _)
    linarith
  · have h9 : coarseC p S aTop b (topOf x h1) - b.sg (topOf x h1) ≤ coarseC p S aTop b (topOf x h1) := Nat.sub_le _ _
    have : ((coarseC p S aTop b (topOf x h1) - b.sg (topOf x h1) : ℕ) : ℝ) ≤ A :=
      le_trans (by exact_mod_cast h9) (hcd _)
    linarith
  · have := hcd (topOf x h1)
    linarith

end Deg

structure HIFacts (C0 : ℝ) (X : flipOneThree.Inst) : Prop where
  m4 : 4 ≤ X.L.m
  s_le : 2 * X.s + 2 ≤ X.L.m
  p_ge : ((X.L.m : ℝ) + 1) ^ 2 ≤ (X.L.p : ℝ)
  a1 : (1 : ℝ) ≤ X.L.a
  La0 : 0 ≤ X.L.La C0
  La_lt : X.L.La C0 < ((X.L.m : ℝ) + 1) / 2
  b0 : 0 < X.L.b'
  b_lt : (X.L.p : ℝ) * X.L.b' < X.L.a
  bT_le : ∀ s ∈ X.L.TT, (X.L.bT s : ℝ) ≤ 5 / 2 * X.L.b'
  win_le : (X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa ≤ 2 * X.L.a
  win0 : 0 ≤ (X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa

theorem hiFacts (C0 CYb Cde Ck CD Cb Cc : ℝ) (X : flipOneThree.Inst) (hCYb : 1 ≤ CYb)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : HIFacts C0 X := by
  obtain ⟨h0, -, hxa0, hxa, hxb0, hxb, hbT, -, -, -⟩ := hH
  obtain ⟨hY, hpk, ⟨s0, hs0, -⟩, -, hseg, hN1, hm, hLa8, hb0, hbl, hbh, -, hbw, hYb, hk2, -, -, hpa, -⟩ := h0
  have hk : X.L.k = (X.L.m : ℝ) + 1 := rfl
  have hm4 : 4 ≤ X.L.m := by omega
  have hmR : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hm4
  have hk5 : (5 : ℝ) ≤ X.L.k := by rw [hk]; linarith
  have hN : (1 : ℝ) ≤ X.L.N := by
    have : 1 ≤ X.L.TT.card := Finset.card_pos.2 ⟨s0, hs0⟩
    show (1 : ℝ) ≤ (X.L.TT.card : ℝ)
    exact_mod_cast this
  have hLa0 : 0 ≤ X.L.La C0 := by
    have h1 : (1 : ℝ) ≤ X.L.N * X.L.Y := by nlinarith
    have := Real.log_nonneg h1
    linarith
  have hYb1 : (1 : ℝ) ≤ X.L.Yb := hCYb.trans hYb
  have hLa_lt : X.L.La C0 < X.L.k / 2 := by
    have h1 : (1 : ℝ) ≤ X.L.Yb * X.L.N := by nlinarith
    have h2 : X.L.La C0 ≤ X.L.Yb * X.L.N * X.L.La C0 := le_mul_of_one_le_left hLa0 h1
    linarith
  have hp : X.L.k ^ 2 ≤ (X.L.p : ℝ) := by
    have h1 : (1 : ℝ) ≤ X.L.Y ^ 2 := by nlinarith
    have h2 : X.L.k ^ 2 ≤ X.L.k ^ 2 * X.L.Y ^ 2 := le_mul_of_one_le_right (by positivity) h1
    linarith
  have hp25 : (25 : ℝ) ≤ (X.L.p : ℝ) := by nlinarith
  have hpb : (X.L.p : ℝ) * X.L.b' < X.L.a := by rwa [lt_div_iff₀ hb0] at hpa
  have ha0 : (0 : ℝ) < X.L.a := by
    have : 0 < (X.L.p : ℝ) * X.L.b' := by positivity
    linarith
  have ha1 : (1 : ℝ) ≤ X.L.a := by
    have : 0 < X.L.a := by exact_mod_cast ha0
    exact_mod_cast this
  have hJ0 : X.L.J0 C0 ≤ X.L.b' / 2 := by
    unfold Formalism.MainNotions.ColumnSystems.Loc.J0
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hb25 : 25 * X.L.b' < X.L.a := by nlinarith
  refine ⟨hm4, ?_, by rw [← hk]; exact hp, ha1, hLa0, by rw [← hk]; exact hLa_lt, hb0, hpb, ?_, ?_, ?_⟩
  · have := (hseg X.j).2
    show 2 * segS X.L.TT X.j + 2 ≤ X.L.m
    omega
  · intro s hs
    have := (hbT s hs).2
    linarith
  · have h1 : (X.L.a : ℝ) / (X.L.k * X.L.Y) ≤ X.L.a / 5 := by
      apply div_le_div_of_nonneg_left ha0.le (by norm_num)
      nlinarith
    linarith
  · have h1 : 0 ≤ (X.L.a : ℝ) / (X.L.k * X.L.Y) := by positivity
    linarith

theorem final_num (a m s p : ℝ) (ha : 1 ≤ a) (hm : 4 ≤ m) (hs0 : 0 ≤ s) (hs : 2 * s + 2 ≤ m) (hp : (m + 1) ^ 2 ≤ p) :
    2 * ((2 * s + 1) * (2 * a + s * (a / 10) + 2 * (2 * a) * s + a / 10)) + m ≤ p ^ 2 * (8 * a + m) ^ 2 := by
  have h1 : 2 * a + s * (a / 10) + 2 * (2 * a) * s + a / 10 ≤ a * (3 * m) := by nlinarith
  have h2 : (2 * s + 1) * (2 * a + s * (a / 10) + 2 * (2 * a) * s + a / 10) ≤ m * (a * (3 * m)) := by
    apply mul_le_mul (by linarith) h1 (by positivity) (by linarith)
  have h3 : m ≤ m ^ 2 * a := by nlinarith
  have h4 : m ^ 2 ≤ p := by nlinarith
  have h5 : (1 : ℝ) ≤ p := by nlinarith
  have h6 : m ^ 2 ≤ p ^ 2 := by nlinarith
  have h7 : 64 * a ≤ (8 * a + m) ^ 2 := by nlinarith
  have h8 : m ^ 2 * (64 * a) ≤ p ^ 2 * (8 * a + m) ^ 2 := mul_le_mul h6 h7 (by positivity) (by positivity)
  nlinarith

theorem degIn_le_sum {ι : Type} [Fintype ι] (d : ι → ℕ) (S : Set ι) : degIn d S ≤ ∑ l, d l := by
  unfold degIn
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem block_size (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (X : flipOneThree.Inst) (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1)
    (hCE2 : 0 ≤ CE2) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (LL : ChainLetters (2 * X.s + 1))
    (hLL : X.BlockLetters C0 CE1 CE2 LL) (S : Set (Fin (2 * X.s + 1))) :
    2 * degIn LL.deg S + X.r ≤ X.p ^ 2 * (8 * X.L.a + X.r) ^ 2 := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  obtain ⟨aTop, haTop, aPlus, -, b, hK, j, jp, -, rfl⟩ := hLL
  have hmR : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
  have hp25 : (25 : ℝ) ≤ (X.L.p : ℝ) := by nlinarith [hF.p_ge]
  have hp1 : 1 ≤ X.p := by
    have : (1 : ℝ) ≤ (X.L.p : ℝ) := by linarith
    exact_mod_cast this
  have ha0 : (0 : ℝ) ≤ (X.L.a : ℝ) := Nat.cast_nonneg _
  have hb10 : 5 / 2 * X.L.b' ≤ (X.L.a : ℝ) / 10 := by nlinarith [hF.b_lt, hF.b0]
  have hE0 : 0 ≤ (X.S C0 CE1 CE2).E0 := by
    show 0 ≤ errorTermBound CE1 CE2 X.L.p X.L.k X.L.N1 X.L.Q X.L.c X.L.a X.L.b' (X.L.La C0)
    unfold errorTermBound
    have h1 := hF.La0
    have h2 := hF.b0.le
    have h3 : (0 : ℝ) ≤ X.L.k := by show (0 : ℝ) ≤ (X.L.m : ℝ) + 1; positivity
    have h4 : (0 : ℝ) ≤ X.L.Q := by show (0 : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'; positivity
    positivity
  have hLa : (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 := by
    show X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2 ≤ 1
    have h1 : X.L.La C0 / ((X.L.m : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [hF.La_lt]
    have h2 : 4 / (X.L.p : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hdeg : ∀ x, (((blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).lettersAt j jp).deg x : ℝ) ≤
      2 * (X.L.a : ℝ) + X.s * ((X.L.a : ℝ) / 10) + 2 * (2 * (X.L.a : ℝ)) * X.s + (X.L.a : ℝ) / 10 := by
    intro x
    have h1 : ((blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).lettersAt j jp).deg x ≤
        (segChain X.p (X.S C0 CE1 CE2) aTop b).deg x :=
      (Nat.sub_le _ _).trans (Nat.sub_le _ _)
    refine le_trans (Nat.cast_le.2 h1) ?_
    refine segChain_deg_le (X.S C0 CE1 CE2) aTop b hK hp1 hE0 hF.La0 hLa (2 * (X.L.a : ℝ)) ((X.L.a : ℝ) / 10)
      (fun i => ?_) ?_ (fun i => ?_) ?_ x
    · exact (hF.bT_le _ (segPos_mem X.L.TT X.j i)).trans hb10
    · exact (hF.bT_le _ (segNext_mem X.L.TT X.j)).trans hb10
    · have h2 := (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 haTop i)).2
      have h3 : (aTop i : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast h2
      exact (h3.trans (Nat.floor_le hF.win0)).trans hF.win_le
    · show (X.L.a : ℝ) ≤ 2 * (X.L.a : ℝ)
      linarith
  have hsum : ((degIn ((blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).lettersAt j jp).deg S : ℕ) : ℝ) ≤
      (2 * (X.s : ℝ) + 1) *
        (2 * (X.L.a : ℝ) + X.s * ((X.L.a : ℝ) / 10) + 2 * (2 * (X.L.a : ℝ)) * X.s + (X.L.a : ℝ) / 10) := by
    refine le_trans (Nat.cast_le.2 (degIn_le_sum _ S)) ?_
    push_cast
    refine (Finset.sum_le_sum fun x _ => hdeg x).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    exact le_rfl
  have hs : 2 * (X.s : ℝ) + 2 ≤ (X.L.m : ℝ) := by exact_mod_cast hF.s_le
  have hfin := final_num (X.L.a : ℝ) (X.L.m : ℝ) (X.s : ℝ) (X.L.p : ℝ) hF.a1 hmR (Nat.cast_nonneg _) hs hF.p_ge
  have : (2 * (degIn ((blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).lettersAt j jp).deg S : ℝ) + (X.L.m : ℝ)) ≤
      (X.L.p : ℝ) ^ 2 * (8 * (X.L.a : ℝ) + (X.L.m : ℝ)) ^ 2 := by linarith
  exact_mod_cast this

theorem kap_num (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (X : flipOneThree.Inst) (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1)
    (hCE2 : 0 ≤ CE2) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (LL : ChainLetters (2 * X.s + 1))
    (hLL : X.BlockLetters C0 CE1 CE2 LL) (n : ℕ) (hn : n ≤ X.r) (S : Set (Fin (2 * X.s + 1))) :
    N0 n * Nat.log X.p (2 * degIn LL.deg S + n - 1) ≤ ⌈kappaOneExponent X.p X.L.a X.r⌉₊ :=
  exp_le X.p X.L.a X.r n (degIn LL.deg S) hn
    (block_size C0 CYb Cde Ck CD Cb CE1 CE2 Cc X hCYb hCE1 hCE2 hH LL hLL S)

theorem r_ge (C0 CYb Cde Ck CD Cb Cc : ℝ) (X : flipOneThree.Inst) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : 4 ≤ X.r := by
  have h6 : 1 ≤ X.L.N1 := hH.1.2.2.2.2.2.1
  have h7 : 2 * X.L.N1 + 2 ≤ X.L.m := hH.1.2.2.2.2.2.2.1
  show 4 ≤ X.L.m
  omega

theorem p_prime (X : flipOneThree.Inst) : X.p.Prime := X.std.1.prime

theorem lat_facts (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S0 : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) :
    CharZero (KK O) ∧ ∀ (N r : ℕ) (Lt : Letters (Fin N)),
      (∀ S : Set (Fin N), ∀ u ∈ UZgens (glOps (KK O) r Lt S),
        (∀ F ∈ IntPol O (Fin N × Fin r), u F ∈ IntPol O (Fin N × Fin r)) ∧
        ∀ F ∈ bbSpec O p (Fin N × Fin r) 1, u F ∈ bbSpec O p (Fin N × Fin r) 1) ∧
      ∀ d : Fin N → ℕ, (latticeMultidegreePart (IntPol O (Fin N × Fin r)) d).FG ∧
        MQ (K := KK O) (latticeMultidegreePart (IntPol O (Fin N × Fin r)) d) = ⊤ ∧
        (latticeMultidegreePart (bbSpec O p (Fin N × Fin r) 1) d).FG ∧
        MQ (K := KK O) (latticeMultidegreePart (bbSpec O p (Fin N × Fin r) 1) d) = ⊤ := by
  obtain ⟨hc, h⟩ := integral_formula_lattice_holds p n' O S0 hG
  refine ⟨hc, fun N r Lt => ?_⟩
  obtain ⟨-, h2, BBs, hBB, h3⟩ := h r (Fin N) Lt
  have hV := valuation_properties_hold hG.1 S0
  have hEq : bbSpec O p (Fin N × Fin r) 1 = BBs := by
    ext F
    rw [mem_bbSpec_one_iff hV, hBB]
  refine ⟨fun S u hu => ⟨(h2 S u hu).1, fun F hF => ?_⟩, fun d => ?_⟩
  · rw [mem_bbSpec_one_iff hV] at hF ⊢
    exact (h2 S u hu).2 F hF
  · rw [hEq]
    exact h3 d

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

section ExtAbs

variable {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

def lowIm (E : GLOps n K V) : Submodule K V :=
  ⨆ (a : Fin n) (b : Fin n) (_ : b < a), LinearMap.range (E a b)

def hwK (E : GLOps n K V) : Submodule K V :=
  ⨅ (a : Fin n) (b : Fin n) (_ : a < b), LinearMap.ker (E a b)

theorem mem_hwK (E : GLOps n K V) (x : V) : x ∈ hwK E ↔ ∀ a b, a < b → E a b x = 0 := by
  simp only [hwK, Submodule.mem_iInf, LinearMap.mem_ker]

theorem range_le_lowIm (E : GLOps n K V) {a b : Fin n} (h : b < a) : LinearMap.range (E a b) ≤ lowIm E :=
  le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le h le_rfl))

theorem ext_word_wt {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {w : V} (hw : IsHWV E mu w)
    {u : Module.End K V} (hu : u ∈ loweringMonoid E) :
    ∃ ν, raisingFunctional ν ≤ raisingFunctional mu ∧ u w ∈ weightSp E ν := by
  unfold loweringMonoid at hu
  induction hu using Submonoid.closure_induction_left with
  | one => exact ⟨mu, le_rfl, hw.2.1⟩
  | mul_left g hg y _ ih =>
    obtain ⟨c, d, hcd, rfl⟩ := hg
    obtain ⟨ν, hν, hy⟩ := ih
    refine ⟨ν + rootW c d, ?_, gl_rep_weight_shift hE hy c d⟩
    rw [raising_functional_add_root]
    have : (d.val : ℤ) < (c.val : ℤ) := by exact_mod_cast hcd
    omega

theorem ext_word {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {w : V} (hw : IsHWV E mu w)
    {u : Module.End K V} (hu : u ∈ loweringMonoid E) :
    u w ∈ (weightSp E mu ⊓ hwK E) ⊔ (lowIm E ⊓ ⨆ (ν : Fin n → ℤ) (_ : ν ≠ mu), weightSp E ν) := by
  have hu' := hu
  unfold loweringMonoid at hu'
  induction hu' using Submonoid.closure_induction_left with
  | one =>
    exact Submodule.mem_sup_left ⟨hw.2.1, (mem_hwK E w).2 hw.2.2⟩
  | mul_left g hg y hy _ =>
    obtain ⟨c, d, hcd, rfl⟩ := hg
    obtain ⟨ν, hν, hyw⟩ := ext_word_wt hE hw (u := y) hy
    refine Submodule.mem_sup_right ⟨range_le_lowIm E hcd ⟨y w, rfl⟩, ?_⟩
    have hne : ν + rootW c d ≠ mu := by
      intro h
      have h1 := raising_functional_add_root ν c d
      rw [h] at h1
      have : (d.val : ℤ) < (c.val : ℤ) := by exact_mod_cast hcd
      omega
    exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hne (gl_rep_weight_shift hE hyw c d))

theorem ext_Z_le {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) :
    hwvLoweringSpan E mu ≤ (weightSp E mu ⊓ hwK E) ⊔ (lowIm E ⊓ ⨆ (ν : Fin n → ℤ) (_ : ν ≠ mu), weightSp E ν) := by
  unfold hwvLoweringSpan
  rw [Submodule.span_le]
  rintro x ⟨u, hu, w, hw, rfl⟩
  exact ext_word hE hw hu

theorem weight_vector_own_isotypic_highest {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {x : V} (hx : x ∈ isoSub E mu)
    (hw : x ∈ weightSp E mu) : x ∈ hwK E := by
  obtain ⟨h, hh, l, hl, rfl⟩ := Submodule.mem_sup.1 (ext_Z_le hE mu (isotypic_le_lowering_span hE mu hx))
  have h1 : l ∈ weightSp E mu := by
    have := Submodule.sub_mem _ hw hh.1
    simpa using this
  have h0 : l = 0 := (Submodule.disjoint_def.1 (weightSpace_independent E mu)) l h1 hl.2
  rw [h0, add_zero]
  exact hh.2

theorem lowIm_diag {E : GLOps n K V} (hE : IsGLRep E) (c : Fin n) : ∀ x ∈ lowIm E, E c c x ∈ lowIm E := by
  have : lowIm E ≤ (lowIm E).comap (E c c) := by
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_comap, gl_commutation_apply hE c c a b y]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (range_le_lowIm E hab ⟨_, rfl⟩) ?_) ?_
    · split_ifs with h
      · subst h; exact range_le_lowIm E hab ⟨_, rfl⟩
      · exact Submodule.zero_mem _
    · split_ifs with h
      · subst h; exact range_le_lowIm E hab ⟨_, rfl⟩
      · exact Submodule.zero_mem _
  exact fun x hx => this hx

theorem weight_vector_other_isotypic_in_lowering_image {E : GLOps n K V} (hE : IsGLRep E) {mu ν : Fin n → ℤ} (hne : mu ≠ ν) {x : V}
    (hx : x ∈ isoSub E ν) (hw : x ∈ weightSp E mu) : x ∈ lowIm E := by
  classical
  obtain ⟨h, hh, l, hl, hxe⟩ := Submodule.mem_sup.1 (ext_Z_le hE ν (isotypic_le_lowering_span hE ν hx))
  have key := weight_components_mem_invariant E (lowIm E) (lowIm_diag hE) {mu, ν} (fun κ => if κ = mu then x else -h)
    (by
      intro κ hκ
      rcases Finset.mem_insert.1 hκ with rfl | hκ
      · simpa using hw
      · rw [Finset.mem_singleton] at hκ
        subst hκ
        simp only [if_neg (Ne.symm hne)]
        exact Submodule.neg_mem _ hh.1)
    (by
      rw [Finset.sum_pair hne]
      simp only [if_true, if_neg (Ne.symm hne)]
      have : x + -h = l := by rw [← hxe]; abel
      rw [this]; exact hl.1)
    mu (Finset.mem_insert_self _ _)
  simpa using key

end ExtAbs

section ExtMain

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem wt_isCompl {n : ℕ} {E : GLOps n K V} (hE : IsGLRep E) (la : Fin n → ℤ) :
    IsCompl (weightSp E la) (⨆ (ν : Fin n → ℤ) (_ : ν ≠ la), weightSp E ν) := by
  refine ⟨weightSpace_independent E la, ?_⟩
  rw [codisjoint_iff, ← iSup_split_single]
  exact hE.2.2

def wtProj {n : ℕ} {E : GLOps n K V} (hE : IsGLRep E) (la : Fin n → ℤ) : Module.End K V :=
  (weightSp E la).subtype ∘ₗ Submodule.projectionOnto _ _ (wt_isCompl hE la)

theorem wtProj_mem {n : ℕ} {E : GLOps n K V} (hE : IsGLRep E) (la : Fin n → ℤ) (x : V) :
    wtProj hE la x ∈ weightSp E la := (Submodule.projectionOnto _ _ (wt_isCompl hE la) x).2

theorem wtProj_same {n : ℕ} {E : GLOps n K V} (hE : IsGLRep E) (la : Fin n → ℤ) {x : V}
    (hx : x ∈ weightSp E la) : wtProj hE la x = x := by
  have := Submodule.projectionOnto_apply_left (wt_isCompl hE la) ⟨x, hx⟩
  show ((Submodule.projectionOnto _ _ (wt_isCompl hE la) x : weightSp E la) : V) = x
  rw [this]

theorem wtProj_other {n : ℕ} {E : GLOps n K V} (hE : IsGLRep E) (la : Fin n → ℤ) {x : V}
    (hx : x ∈ ⨆ (ν : Fin n → ℤ) (_ : ν ≠ la), weightSp E ν) : wtProj hE la x = 0 := by
  have := (Submodule.projectionOnto_apply_eq_zero_iff (wt_isCompl hE la)).2 hx
  show ((Submodule.projectionOnto _ _ (wt_isCompl hE la) x : weightSp E la) : V) = 0
  rw [this]; rfl

theorem wt_split {n : ℕ} {E : GLOps n K V} (hE : IsGLRep E) (la : Fin n → ℤ) (x : V) :
    ∃ a ∈ weightSp E la, ∃ b ∈ ⨆ (ν : Fin n → ℤ) (_ : ν ≠ la), weightSp E ν, a + b = x := by
  have : x ∈ weightSp E la ⊔ ⨆ (ν : Fin n → ℤ) (_ : ν ≠ la), weightSp E ν := by
    rw [(wt_isCompl hE la).sup_eq_top]; trivial
  exact Submodule.mem_sup.1 this

theorem wtProj_stable {n : ℕ} {E : GLOps n K V} (hE : IsGLRep E) (la : Fin n → ℤ) (U : Submodule K V)
    (hU : ∀ a, ∀ x ∈ U, E a a x ∈ U) {x : V} (hx : x ∈ U) : wtProj hE la x ∈ U := by
  classical
  have hx' : x ∈ ⨆ ν : Fin n → ℤ, weightSp E ν := by rw [hE.2.2]; trivial
  obtain ⟨f, hf, hsum'⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have hsum : ∑ ν ∈ f.support, f ν = x := hsum'
  have hall := weight_components_mem_invariant E U hU f.support (fun ν => f ν) (fun ν _ => hf ν) (by rw [hsum]; exact hx)
  have hfla : f la ∈ U := by
    by_cases h : la ∈ f.support
    · exact hall la h
    · rw [Finsupp.notMem_support_iff.1 h]; exact Submodule.zero_mem _
  have : wtProj hE la x = f la := by
    rw [← hsum, map_sum]
    by_cases h : la ∈ f.support
    · rw [Finset.sum_eq_single la]
      · exact wtProj_same hE la (hf la)
      · intro ν _ hν
        exact wtProj_other hE la (Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem hν (hf ν)))
      · intro h'; exact absurd h h'
    · rw [Finsupp.notMem_support_iff.1 h]
      refine Finset.sum_eq_zero fun ν hν => ?_
      have hne : ν ≠ la := fun h' => h (h' ▸ hν)
      exact wtProj_other hE la (Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem hne (hf ν)))
  rw [this]; exact hfla

theorem wt_orth {n : ℕ} {E : GLOps n K V} (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ a b x y, B (E a b x) y = B x (E b a y)) {la ν : Fin n → ℤ} (hne : ν ≠ la) {x z : V}
    (hx : x ∈ weightSp E la) (hz : z ∈ weightSp E ν) : B x z = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, ν c ≠ la c := by
    by_contra h
    exact hne (funext fun a => by_contra fun h' => h ⟨a, h'⟩)
  have h1 := hB c c x z
  rw [(mem_weightSpace_iff_diagonal_rep E la x).1 hx c, (mem_weightSpace_iff_diagonal_rep E ν z).1 hz c, map_smul, map_smul,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  have h2 : ((la c : K) - (ν c : K)) * B x z = 0 := by rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    apply hc
    have : (la c : K) = (ν c : K) := sub_eq_zero.1 h3
    exact_mod_cast this.symm
  · exact h3

theorem ext_abs {r n : ℕ} (E : GLOps r K V) (φ : Fin n → Fin r) (hE : IsGLRep E)
    (hE' : IsGLRep (fun a b => E (φ a) (φ b) : GLOps n K V))
    (hT' : (⨆ mu : Fin n → ℤ, isoSub (fun a b => E (φ a) (φ b) : GLOps n K V) mu) = ⊤)
    (B : V →ₗ[K] V →ₗ[K] K) (hB : ∀ a b x y, B (E a b x) y = B x (E b a y))
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (la : Fin r → ℤ) (e' : Module.End K V)
    (he' : IsIsoProjSet (fun a b => E (φ a) (φ b) : GLOps n K V) {la ∘ φ} e') :
    ∃ P : Module.End K V, P * P = P ∧
      LinearMap.range P = weightSp E la ⊓ hwK (fun a b => E (φ a) (φ b) : GLOps n K V) ∧
      LinearMap.ker P ⊓ weightSp E la = lowIm (fun a b => E (φ a) (φ b) : GLOps n K V) ⊓ weightSp E la ∧
      (∀ F ∈ weightSp E la, ∀ G ∈ weightSp E la, B (P F) G = B F (P G)) ∧
      ∀ F ∈ weightSp E la, P F = e' F := by
  set E' : GLOps n K V := fun a b => E (φ a) (φ b) with hE'def
  set la' : Fin n → ℤ := la ∘ φ with hla'
  have hiso : IsIsoProj E' la' e' :=
    ⟨fun x hx => he'.1 la' rfl x hx, fun mu hmu x hx => he'.2 mu (by simpa using hmu) x hx⟩
  have hB' : ∀ a b x y, B (E' a b x) y = B x (E' b a y) := fun a b x y => hB (φ a) (φ b) x y
  have hadj : ∀ x y, B (e' x) y = B x (e' y) :=
    isotypic_projector_selfAdjoint E' hT' la' e' hiso B (contravariant_orthogonality_holds K V n E' hE' B hB')

  have hdiag : ∀ c mu, ∀ x ∈ isoSub E' mu, E c c x ∈ isoSub E' mu := by
    intro c mu x hx
    by_cases hc : ∃ a, φ a = c
    · obtain ⟨a, rfl⟩ := hc
      exact isotypic_stable_gl_operator E' mu a a x hx
    · refine isotypic_stable_commuting E' (E c c) ?_ mu x hx
      intro a b
      have h := hE.1 c c (φ a) (φ b)
      rw [if_neg (fun h : c = φ a => hc ⟨a, h.symm⟩), if_neg (fun h : φ b = c => hc ⟨b, h⟩), sub_zero,
        sub_eq_zero] at h
      exact h
  have hcd : ∀ c x, e' (E c c x) = E c c (e' x) := fun c x =>
    congrArg (fun f : Module.End K V => f x) (isotypic_projector_commutes E' hT' la' e' hiso (E c c) (hdiag c))
  have hewt : ∀ ν, ∀ x ∈ weightSp E ν, e' x ∈ weightSp E ν := by
    intro ν x hx
    rw [mem_weightSpace_iff_diagonal_rep] at hx ⊢
    intro c
    rw [← hcd, hx c, map_smul]
  have heoth : ∀ x ∈ (⨆ (ν : Fin r → ℤ) (_ : ν ≠ la), weightSp E ν),
      e' x ∈ ⨆ (ν : Fin r → ℤ) (_ : ν ≠ la), weightSp E ν := by
    have : (⨆ (ν : Fin r → ℤ) (_ : ν ≠ la), weightSp E ν) ≤
        (⨆ (ν : Fin r → ℤ) (_ : ν ≠ la), weightSp E ν).comap e' :=
      iSup₂_le fun ν hν x hx => Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem hν (hewt ν x hx))
    exact fun x hx => this hx
  have hcomm : ∀ x, e' (wtProj hE la x) = wtProj hE la (e' x) := by
    intro x
    obtain ⟨a, ha, b, hb, rfl⟩ := wt_split hE la x
    have h1 : wtProj hE la (a + b) = a := by
      rw [map_add, wtProj_same hE la ha, wtProj_other hE la hb, add_zero]
    have h2 : wtProj hE la (e' (a + b)) = e' a := by
      rw [map_add, map_add, wtProj_same hE la (hewt la a ha), wtProj_other hE la (heoth b hb), add_zero]
    rw [h1, h2]
  have hran : ∀ y, e' y ∈ isoSub E' la' := by
    intro y
    have hy : y ∈ (⨆ mu : Fin n → ℤ, isoSub E' mu) := by rw [hT']; trivial
    induction hy using Submodule.iSup_induction' with
    | mem mu y hy =>
      by_cases h : mu = la'
      · subst h; rw [hiso.1 y hy]; exact hy
      · rw [hiso.2 mu h y hy]; exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  have hwt' : ∀ x ∈ weightSp E la, x ∈ weightSp E' la' := by
    intro x hx
    rw [mem_weightSpace_iff_diagonal_rep] at hx ⊢
    intro a
    exact hx (φ a)
  have hPwt : ∀ x ∈ weightSp E la, (e' * wtProj hE la) x = e' x := by
    intro x hx
    rw [Module.End.mul_apply, wtProj_same hE la hx]
  have hmem : ∀ x, (e' * wtProj hE la) x ∈ weightSp E la ⊓ hwK E' := by
    intro x
    have h1 : (e' * wtProj hE la) x ∈ weightSp E la := hewt la _ (wtProj_mem hE la x)
    exact ⟨h1, weight_vector_own_isotypic_highest hE' (hran _) (hwt' _ h1)⟩
  have hfix : ∀ x ∈ weightSp E la ⊓ hwK E', (e' * wtProj hE la) x = x := by
    intro x hx
    rw [hPwt x hx.1]
    by_cases h0 : x = 0
    · rw [h0, map_zero]
    · exact hiso.1 x (Submodule.subset_span
        ⟨1, (Umon E').one_mem, x, ⟨h0, hwt' x hx.1, (mem_hwK E' x).1 hx.2⟩, rfl⟩)

  have hoth : ∀ y, y - e' y ∈ ⨆ (mu : Fin n → ℤ) (_ : mu ≠ la'), isoSub E' mu := by
    intro y
    have hy : y ∈ (⨆ mu : Fin n → ℤ, isoSub E' mu) := by rw [hT']; trivial
    induction hy using Submodule.iSup_induction' with
    | mem mu y hy =>
      by_cases h : mu = la'
      · subst h; rw [hiso.1 y hy, sub_self]; exact Submodule.zero_mem _
      · rw [hiso.2 mu h y hy, sub_zero]
        exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem h hy)
    | zero => simp
    | add y z _ _ hy hz =>
      have : y + z - e' (y + z) = (y - e' y) + (z - e' z) := by rw [map_add]; abel
      rw [this]; exact Submodule.add_mem _ hy hz
  have hlow : (⨆ (mu : Fin n → ℤ) (_ : mu ≠ la'), isoSub E' mu) ≤ (lowIm E').comap (wtProj hE' la') := by
    refine iSup₂_le fun mu hmu x hx => ?_
    rw [Submodule.mem_comap]
    exact weight_vector_other_isotypic_in_lowering_image hE' (Ne.symm hmu)
      (wtProj_stable hE' la' (isoSub E' mu) (fun a y hy => isotypic_stable_gl_operator E' mu a a y hy) hx)
      (wtProj_mem hE' la' x)
  refine ⟨e' * wtProj hE la, ?_, ?_, ?_, ?_, hPwt⟩
  · ext x
    rw [Module.End.mul_apply (e' * wtProj hE la)]
    exact hfix _ (hmem x)
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact hmem x
    · intro x hx
      exact ⟨x, hfix x hx⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
      refine Submodule.mem_inf.2 ⟨?_, hx2⟩
      rw [LinearMap.mem_ker, hPwt x hx2] at hx1
      have h1 := hoth x
      rw [hx1, sub_zero] at h1
      have h2 := hlow h1
      rwa [Submodule.mem_comap, wtProj_same hE' la' (hwt' x hx2)] at h2
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
      refine Submodule.mem_inf.2 ⟨?_, hx2⟩
      rw [LinearMap.mem_ker, hPwt x hx2]
      refine hnd _ fun y => ?_
      rw [hadj]

      have hpr : ∀ z, B x z = B x (wtProj hE la z) := by
        intro z
        obtain ⟨a, ha, b, hb, rfl⟩ := wt_split hE la z
        have hb0 : B x b = 0 := by
          have : (⨆ (ν : Fin r → ℤ) (_ : ν ≠ la), weightSp E ν) ≤ LinearMap.ker (B x) :=
            iSup₂_le fun ν hν z hz => wt_orth B hB hν hx2 hz
          exact this hb
        have h1 : wtProj hE la (a + b) = a := by
          rw [map_add, wtProj_same hE la ha, wtProj_other hE la hb, add_zero]
        rw [h1, map_add, hb0, add_zero]
      rw [hpr, ← hcomm]
      have hh : e' (wtProj hE la y) ∈ hwK E' := (hmem y).2
      have : lowIm E' ≤ LinearMap.ker (B.flip (e' (wtProj hE la y))) := by
        refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
        rintro _ ⟨z, rfl⟩
        rw [LinearMap.mem_ker, LinearMap.flip_apply, hB', (mem_hwK E' _).1 hh b a hab, map_zero]
      exact this hx1
  · intro F hF G hG
    rw [hPwt F hF, hPwt G hG]
    exact hadj F G

end ExtMain

section ExtPoly

theorem ext_rep {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r n : ℕ} {E : GLOps r K V} (hE : IsGLRep E)
    {φ : Fin n → Fin r} (hφ : Function.Injective φ) : IsGLRep (fun a b => E (φ a) (φ b) : GLOps n K V) := by
  refine ⟨fun a b c d => ?_, fun x => ?_, ?_⟩
  · have := hE.1 (φ a) (φ b) (φ c) (φ d)
    simpa only [hφ.eq_iff] using this
  · obtain ⟨W, hW, hx, hst⟩ := hE.2.1 x
    exact ⟨W, hW, hx, fun a b y hy => hst (φ a) (φ b) y hy⟩
  · rw [eq_top_iff, ← hE.2.2]
    refine iSup_le fun mu => le_iSup_of_le (mu ∘ φ) ?_
    intro x hx
    rw [mem_weightSpace_iff_diagonal_rep] at hx ⊢
    intro a
    exact hx (φ a)

theorem ext_fock_nondeg {K : Type} [Field K] [CharZero K] {σ : Type} (x : MvPolynomial σ K)
    (h : ∀ y, fock x y = 0) : x = 0 := by
  ext m
  have h1 := h (monomial m 1)
  rw [fock_form_symm, fock_form_monomial, one_mul] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · simpa using h2
  · exfalso
    exact exponent_factorial_ne_zero_of m (by exact_mod_cast h2)

theorem ext_poly (D : Formalism.BasicNotions.D7) {K : Type} [Field K] [CharZero K] {N r n : ℕ} (Lt : Letters (Fin N))
    (S : Set (Fin N)) (φ : Fin n → Fin r) (hφ : Function.Injective φ) (la : Fin r → ℤ)
    (e' : Module.End K (MvPolynomial (Fin N × Fin r) K)) (he' : IsIsoProjSet (subOps K Lt S φ) {la ∘ φ} e') :
    ∃ P : Module.End K (MvPolynomial (Fin N × Fin r) K), P * P = P ∧
      LinearMap.range P = weightSp (glOps K r Lt S) la ⊓ hwK (subOps K Lt S φ) ∧
      LinearMap.ker P ⊓ weightSp (glOps K r Lt S) la = lowIm (subOps K Lt S φ) ⊓ weightSp (glOps K r Lt S) la ∧
      (∀ F ∈ weightSp (glOps K r Lt S) la, ∀ G ∈ weightSp (glOps K r Lt S) la, fock (P F) G = fock F (P G)) ∧
      ∀ F ∈ weightSp (glOps K r Lt S) la, P F = e' F := by
  have hE : IsGLRep (glOps K r Lt S) := polynomial_isGLRep Lt S
  have hE' : IsGLRep (fun a b => glOps K r Lt S (φ a) (φ b) : GLOps n K _) := ext_rep hE hφ
  exact ext_abs (glOps K r Lt S) φ hE hE' (complete_reducibility_of_semisimple D (Formalism.MainNotions.G.GLWeightTheory.weight_condition_from_integral_form D) K _ n _ hE')
    (fockBilinear K (Fin N × Fin r)) (fun a b x y => fock_form_contravariant Lt S a b x y)
    (fun x hx => ext_fock_nondeg x hx) la e' he'

theorem exponent_bound_of_positivity (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (X : flipOneThree.Inst)
    (h1 : adm1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) : adm3 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X := by
  intro hH LL hLL j hj la _
  have : CharZero (KK X.O) := dvr_fraction_field_char_zero X.std.1.prime X.setting
  obtain ⟨⟨e', he'⟩, hall⟩ := ((h1 hH LL hLL).1 j hj).2
    {fun a : Fin (X.r - 1) => la (Fin.castLE (Nat.sub_le X.r 1) a)}
  obtain ⟨-, hint, -⟩ := hall e' he'
  obtain ⟨P, hPP, hr, hk, hadj, hPe⟩ := ext_poly D (K := KK X.O) (⟨LL.vec⟩ : Letters (Fin (2 * X.s + 1)))
    {i : Fin (2 * X.s + 1) | (i : ℕ) < j} (Fin.castLE (Nat.sub_le X.r 1)) (Fin.castLE_injective _) la e' he'
  refine ⟨P, hPP, hr, hk, hadj, fun F hF hFi hFw => ?_⟩
  rw [hPe F hFw]
  exact hint F hF hFi

end ExtPoly

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem ptool_sub (D : Formalism.BasicNotions.D7) (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S0 : UniformizedDVR p O) (hG : AdmissibleDVR p n' O) (N r n : ℕ) (hn : 0 < n) (LL : ChainLetters N) (S : Set (Fin N))
    (φ : Fin n → Fin r) (hφ : Function.Injective φ) (e1 : ℕ)
    (he1 : N0 n * Nat.log p (2 * degIn LL.deg S + n - 1) ≤ e1) :
    PTool O p LL (subOps (KK O) (⟨LL.vec⟩ : Letters (Fin N)) S φ) e1 := by
  have hp : p.Prime := hG.1
  have : CharZero (KK O) := dvr_fraction_field_char_zero hp S0
  have hRep := subOps_rep (K := KK O) (⟨LL.vec⟩ : Letters (Fin N)) S φ hφ
  intro T
  refine ⟨subOps_exists D _ S φ hRep T, fun e he => ⟨fun F _ G _ => subOps_selfadj D _ S φ hRep T e he F G, ?_, ?_⟩⟩
  · intro F hF hFI
    exact ((subOps_int_lat D p n' O S0 hG N r n hn _ S φ hφ (fun lam => subOps_exists D _ S φ hRep {lam})
      LL.deg T e he e1 he1) F hF).1 hFI
  · intro F hF hFB
    rw [mem_bbSpec_one_iff' hp S0] at hFB ⊢
    exact ((subOps_int_lat D p n' O S0 hG N r n hn _ S φ hφ (fun lam => subOps_exists D _ S φ hRep {lam})
      LL.deg T e he e1 he1) F hF).2 hFB

theorem positivity_condition_holds (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1)
    (hCE2 : 0 ≤ CE2) (X : flipOneThree.Inst) : adm1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X := by
  intro hH LL hLL
  have hr := r_ge C0 CYb Cde Ck CD Cb Cc X hH
  have : CharZero (KK X.O) := dvr_fraction_field_char_zero (p_prime X) X.setting
  refine ⟨fun j _ => ⟨?_, ?_⟩, fun j j' hjj _ => ?_⟩
  · rw [chOps_eq]
    exact ptool_sub D X.p X.L.n' X.O X.setting X.instance_ring_standard _ X.r X.r (by omega) LL _ id Function.injective_id _
      (kap_num C0 CYb Cde Ck CD Cb CE1 CE2 Cc X hCYb hCE1 hCE2 hH LL hLL X.r le_rfl _)
  · rw [chOps'_eq]
    exact ptool_sub D X.p X.L.n' X.O X.setting X.instance_ring_standard _ X.r (X.r - 1) (by omega) LL _ _
      (Fin.castLE_injective _) _
      (kap_num C0 CYb Cde Ck CD Cb CE1 CE2 Cc X hCYb hCE1 hCE2 hH LL hLL (X.r - 1) (Nat.sub_le _ _) _)
  · exact chOps_comm3 D LL
      (fun j => subOps_rep (K := KK X.O) (⟨LL.vec⟩ : Letters (Fin (2 * X.s + 1))) _ id Function.injective_id)
      (fun j => subOps_rep (K := KK X.O) (⟨LL.vec⟩ : Letters (Fin (2 * X.s + 1))) _ _ (Fin.castLE_injective _)) j j' hjj

theorem exponent_condition_holds (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1)
    (hCE2 : 0 ≤ CE2) (X : flipOneThree.Inst) : adm3 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X :=
  exponent_bound_of_positivity D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X (positivity_condition_holds D C0 CYb Cde Ck CD Cb CE1 CE2 Cc hCYb hCE1 hCE2 X)

theorem thr_of_ge {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cc, 1 ≤ CYb → 0 ≤ CE1 → 0 ≤ CE2 → P C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : TransportedAlt P :=
  fun Cc _ => ⟨1, one_pos, fun C0 _ => ⟨1, one_pos, fun CE1 CE2 h1 h2 => ⟨1, one_pos, fun CYb Cde Ck CD Cb hY _ _ _ _ =>
    h C0 CYb Cde Ck CD Cb CE1 CE2 Cc hY (zero_le_one.trans h1) (zero_le_one.trans h2)⟩⟩⟩

theorem positivity_condition_eventually (D : Formalism.BasicNotions.D7) :
    TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ X : flipOneThree.Inst, adm1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X :=
  thr_of_ge fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc h1 h2 h3 X => positivity_condition_holds D C0 CYb Cde Ck CD Cb CE1 CE2 Cc h1 h2 h3 X

theorem exponent_bound_eventually (D : Formalism.BasicNotions.D7) :
    TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ X : flipOneThree.Inst, adm3 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X :=
  thr_of_ge fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc h1 h2 h3 X => exponent_condition_holds D C0 CYb Cde Ck CD Cb CE1 CE2 Cc h1 h2 h3 X

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.MainNotions.G Finset

section Bad

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {V : Type*}
  [AddCommGroup V] [Module O V] {be : V → V → KK O} {L L₁ : Submodule O V} {D D' κ : ℝ}

theorem finrank_le_of_le (h : L₁ ≤ L) (h0 : Module.finrank O L ≠ 0) :
    Module.finrank O L₁ ≤ Module.finrank O L := by
  have h1 : Module.rank O L₁ ≤ Module.rank O L := Submodule.rank_mono h
  have h2 : Module.rank O L < Cardinal.aleph0 := by
    by_contra hc
    exact h0 (Cardinal.toNat_apply_of_aleph0_le (not_lt.mp hc))
  exact Cardinal.toNat_le_toNat h1 h2

theorem badShare_le_one : badShare p be L D ≤ 1 := by
  unfold badShare
  split_ifs with h0
  · exact zero_le_one
  · have hpos : (0 : ℝ) < (Module.finrank O L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    rw [div_le_one hpos]
    have : (0 : ℝ) ≤ ((sSup {n : ℕ | ∃ L₁ : Submodule O V, GoodSub p be L L₁ D ∧ Module.finrank O L₁ = n} : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith

theorem badShare_le_of_goodShare (hκ : 0 ≤ κ) (h : GoodShare p be L D κ) : badShare p be L D ≤ κ := by
  unfold badShare
  split_ifs with h0
  · exact hκ
  · obtain ⟨L₁, hg, hr⟩ := h
    have hpos : (0 : ℝ) < (Module.finrank O L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hb : BddAbove {n : ℕ | ∃ L₁ : Submodule O V, GoodSub p be L L₁ D ∧ Module.finrank O L₁ = n} :=
      ⟨Module.finrank O L, by rintro n ⟨L', hL', rfl⟩; exact finrank_le_of_le hL'.1.1 h0⟩
    have h1 : Module.finrank O L₁ ≤
        sSup {n : ℕ | ∃ L₁ : Submodule O V, GoodSub p be L L₁ D ∧ Module.finrank O L₁ = n} :=
      le_csSup hb ⟨L₁, hg, rfl⟩
    have h2 : (Module.finrank O L₁ : ℝ) ≤
        ((sSup {n : ℕ | ∃ L₁ : Submodule O V, GoodSub p be L L₁ D ∧ Module.finrank O L₁ = n} : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [div_le_iff₀ hpos]
    linarith

theorem vLE_mono {x : KK O} (h : D ≤ D') (hx : vLE p x D) : vLE p x D' := by
  obtain ⟨q, hq, hD⟩ := hx
  exact ⟨q, hq, hD.trans h⟩

theorem GoodSub_mono (h : D ≤ D') (hg : GoodSub p be L L₁ D) : GoodSub p be L L₁ D' :=
  ⟨hg.1, fun u hu => by obtain ⟨u', hu', hv⟩ := hg.2 u hu; exact ⟨u', hu', vLE_mono h hv⟩⟩

end Bad

section LemmaD

variable {s : ℕ} (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r]
  (S : SegData s)

def blockForm (b : SegBlock s r) :
    MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) → MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) → KK O :=
  fun f g => ((specConst p S b : ℕ) : KK O) * fock f g

open Classical in

def segSub (aTop : Fin s → ℕ)
    (L₂ : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O))) :
    Submodule O (SegVs O r s S.t) :=
  Submodule.pi Set.univ (fun b => if Kept p r S aTop b then L₂ b else ⊥)

theorem fock_zero_right' {R : Type*} [CommSemiring R] {σ : Type*} (F : MvPolynomial σ R) :
    fock F (0 : MvPolynomial σ R) = 0 := by
  unfold fock; simp

open Classical in

theorem segSub_good (aTop : Fin s → ℕ) (aPlus : ℕ) (m D : ℝ)
    (L₂ : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)))
    (h : ∀ b, Kept p r S aTop b → GoodSub p (blockForm O p r S b) (blockLat O p r S aTop aPlus m b) (L₂ b) D) :
    GoodSub p (segForm O p r S) (segLat O p r S aTop aPlus m) (segSub O p r S aTop L₂) D := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx b _
    have hb := hx b (Set.mem_univ b)
    by_cases hk : Kept p r S aTop b
    · simp only [if_pos hk] at hb ⊢
      exact (h b hk).1.1 hb
    · simp only [if_neg hk] at hb ⊢
      exact hb
  · intro c x hc hx hcx b _
    have hb := hx b (Set.mem_univ b)
    have hcb := hcx b (Set.mem_univ b)
    by_cases hk : Kept p r S aTop b
    · simp only [if_pos hk] at hb hcb ⊢
      exact (h b hk).1.2 c (x b) hc hb hcb
    · simp only [if_neg hk] at hb ⊢
      exact hb
  · intro u hu
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hex : ∃ b, Kept p r S aTop b ∧ PrimIn (L₂ b) (u b) := by
      by_contra hno
      push Not at hno
      have hdiv : ∀ b, ∃ y, (y ∈ (if Kept p r S aTop b then L₂ b else ⊥ :
          Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)))) ∧ u b = ϖ • y := by
        intro b
        have hb := hu.1 b (Set.mem_univ b)
        by_cases hk : Kept p r S aTop b
        · simp only [if_pos hk] at hb ⊢
          have hnp := hno b hk
          unfold PrimIn at hnp
          push Not at hnp
          obtain ⟨c, x, hx, hux, hc⟩ := hnp hb
          have hcm : c ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal c).2 hc
          rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hcm
          obtain ⟨c', rfl⟩ := hcm
          exact ⟨c' • x, (L₂ b).smul_mem c' hx, by rw [hux, mul_smul]⟩
        · simp only [if_neg hk] at hb ⊢
          exact ⟨0, Submodule.zero_mem _, by rw [(Submodule.mem_bot O).1 hb, smul_zero]⟩
      choose y hy huy using hdiv
      have : IsUnit ϖ := hu.2 ϖ y (fun b _ => hy b) (funext fun b => by rw [Pi.smul_apply]; exact huy b)
      exact hϖ.not_isUnit this
    obtain ⟨b, hk, hprim⟩ := hex
    obtain ⟨u', hu', hv⟩ := (h b hk).2 (u b) hprim
    refine ⟨Pi.single b u', ?_, ?_⟩
    · intro b' _
      by_cases hbb : b' = b
      · subst hbb
        simp only [if_pos hk, Pi.single_eq_same]
        exact hu'
      · rw [Pi.single_eq_of_ne hbb]
        exact Submodule.zero_mem _
    · have : segForm O p r S u (Pi.single b u') = blockForm O p r S b (u b) u' := by
        unfold segForm blockForm
        rw [finsum_eq_single _ b]
        · rw [Pi.single_eq_same]
        · intro b' hbb
          rw [Pi.single_eq_of_ne hbb, fock_zero_right', mul_zero]
      rw [this]
      exact hv

end LemmaD

theorem card_box (X : flipOneThree.Inst) :
    ((Fintype.piFinset (fun _ : Fin X.s => X.winA)).card : ℝ) * (X.winA.card : ℝ) = (X.winA.card : ℝ) ^ (X.s + 1) := by
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_succ]
  push_cast
  ring

def meanBox (X : flipOneThree.Inst) (κ : (Fin X.s → ℕ) → ℕ → ℝ) : ℝ :=
  (∑ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∑ aPlus ∈ X.winA, κ aTop aPlus) /
    (X.winA.card : ℝ) ^ (X.s + 1)

theorem meanBox_mono (X : flipOneThree.Inst) (κ κ' : (Fin X.s → ℕ) → ℕ → ℝ)
    (h : ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA, κ aTop aPlus ≤ κ' aTop aPlus) :
    meanBox X κ ≤ meanBox X κ' := by
  unfold meanBox
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun aTop ha => Finset.sum_le_sum fun aPlus hp => h aTop ha aPlus hp) (by positivity)

theorem meanBox_one_le (X : flipOneThree.Inst) : meanBox X (fun _ _ => 1) ≤ 1 := by
  unfold meanBox
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [card_box]
  exact div_self_le_one _

theorem meanKapT_eq (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) (D : ℝ) :
    meanKapT C0 CE1 CE2 X D = meanBox X (fun aTop aPlus => kapT X.O X.p X.r (X.S C0 CE1 CE2) X.m D aTop aPlus) := rfl

theorem meanKapT_le_one (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) (D : ℝ) : meanKapT C0 CE1 CE2 X D ≤ 1 := by
  rw [meanKapT_eq]
  exact (meanBox_mono X _ _ fun _ _ _ _ => badShare_le_one).trans (meanBox_one_le X)

theorem counting_statement_small_range (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst)
    (hY : X.L.Y ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁) : Conclusion1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X := by
  intro hH
  have h1 : (1 : ℝ) ≤ X.L.Y := hH.1.1
  refine (meanKapT_le_one C0 CE1 CE2 X _).trans ?_
  rw [le_div_iff₀ (by linarith), one_mul]
  exact hY

def RemainingCountingStatement (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ < X.L.Y →
    ∃ κ : (Fin X.s → ℕ) → ℕ → ℝ,
      (∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA, 0 ≤ κ aTop aPlus ∧
        ∃ L₂ : SegBlock X.s X.r → Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
          (∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
            GoodSub X.p (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b)
              (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) (L₂ b)
              (depthD C X.p X.L.a X.Nt X.N₁ X.r X.L.Y)) ∧
          (1 - κ aTop aPlus) *
              (Module.finrank X.O (segLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m) : ℝ) ≤
            (Module.finrank X.O (segSub X.O X.p X.r (X.S C0 CE1 CE2) aTop L₂) : ℝ)) ∧
      meanBox X κ ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ / X.L.Y

theorem counting_statement_of_block_form (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst)
    (h : RemainingCountingStatement C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X) : Conclusion1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X := by
  by_cases hY : X.L.Y ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁
  · exact counting_statement_small_range D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X hY
  · intro hH
    obtain ⟨κ, hκ, hmean⟩ := h hH (not_le.mp hY)
    rw [meanKapT_eq]
    refine (meanBox_mono X _ κ fun aTop ha aPlus hp => ?_).trans hmean
    obtain ⟨h0, L₂, hg, hr⟩ := hκ aTop ha aPlus hp
    exact badShare_le_of_goodShare h0 ⟨_, segSub_good X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m _ L₂ hg, hr⟩

theorem thr_mono {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cc, P C0 CYb Cde Ck CD Cb CE1 CE2 Cc → Q C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : TransportedAlt P) : TransportedAlt Q := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hP Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 a1 a2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 a1 a2
  exact ⟨T2, hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => h _ _ _ _ _ _ _ _ _ (h2 CYb Cde Ck CD Cb b1 b2 b3 b4 b5)⟩

def AdmNoK (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs : ℝ) (X : flipOneThree.Inst) : Prop :=
  adm1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X ∧ adm2 D X ∧ adm3 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X ∧ adm8 D X ∧
    adm9 D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X ∧ adm10 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X ∧
    adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X

theorem admissible_without_key_of_admissible {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs : ℝ} {X : flipOneThree.Inst}
    (h : admitted D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X) : AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩

def BlockFormRemaining (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C : ℝ) : Prop :=
  ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RemainingCountingStatement C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X

def BlockFormRemainingUniform (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ C : ℝ, 0 < C ∧
    BlockFormRemaining D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C

def RemainingCountingBound : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∃ C : ℝ, 0 < C ∧ ∀ X : flipOneThree.Inst, RemainingCountingStatement C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.MainNotions.G Finset

section Kept

variable {s r : ℕ}

theorem rk_coarseA_le (p : ℕ) (S : SegData s) (b : SegBlock s r) (i : Fin s) : coarseA p S b i ≤ S.bTop i :=
  (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem rk_coarseC_le (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) (i : Fin s) :
    coarseC p S aTop b i ≤ aTop i :=
  (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem rk_cap_le (p : ℕ) (S : SegData s) (b : SegBlock s r) (l : ℕ) :
    cap p S b l ≤ S.A0 p + ∑ i : Fin s, (S.bTop i : ℤ) := by
  unfold cap
  refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)
  have h1 : (coarseA p S b i : ℤ) ≤ (S.bTop i : ℤ) := by exact_mod_cast rk_coarseA_le p S b i
  have h2 : (0 : ℤ) ≤ (oEff S b i : ℤ) := Int.natCast_nonneg _
  have h3 : (0 : ℤ) ≤ (S.bTop i : ℤ) := Int.natCast_nonneg _
  split_ifs <;> omega

theorem kept_finite (p r : ℕ) (S : SegData s) (aTop : Fin s → ℕ) : {b : SegBlock s r | Kept p r S aTop b}.Finite := by
  classical
  set M : ℝ := ((S.A0 p + ∑ i : Fin s, (S.bTop i : ℤ) : ℤ) : ℝ) +
    (S.La / (r + 1) + 4 / (p : ℝ) ^ 2) * ∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ) + S.La * (S.bPlus : ℝ) / (r + 1) with hM
  let f : SegBlock s r → (Fin s → Fin (r + 1) → ℕ) × (Fin s → Fin (r + 1) → ℕ) × (Fin s → ℕ) × (Fin s → ℕ) ×
      (Fin s → ℕ) × ℕ := fun b => (b.rz, b.ry, b.o, b.w, b.sg, b.oPlus)
  have hf : Function.Injective f := by
    rintro ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩ h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    subst h1 h2 h3 h4 h5 h6
    rfl
  have hD : {g : Fin s → Fin (r + 1) → ℕ | ∀ i, g i ∈ {h : Fin (r + 1) → ℕ | ∀ c, h c ∈ Set.Iio (S.P p i)}}.Finite :=
    Set.Finite.pi' fun i => Set.Finite.pi' fun _ => Set.finite_Iio _
  have hB : {g : Fin s → ℕ | ∀ i, g i ∈ Set.Iic (S.bTop i)}.Finite := Set.Finite.pi' fun i => Set.finite_Iic _
  have hA : {g : Fin s → ℕ | ∀ i, g i ∈ Set.Iic (aTop i)}.Finite := Set.Finite.pi' fun i => Set.finite_Iic _
  have hfin := (hD.prod (hD.prod (hB.prod (hB.prod (hA.prod (Set.finite_Iic ⌊M⌋₊)))))).preimage (hf.injOn)
  refine hfin.subset ?_
  intro b hb
  obtain ⟨⟨hd, -, -⟩, hU, hS, hO⟩ := hb
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_Iio, Set.mem_Iic, f]
  refine ⟨fun i c => (hd i c).1, fun i c => (hd i c).2, fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · rcases Nat.lt_or_ge (i : ℕ) S.sigma with h | h
    · rw [(hS i h).1]; exact Nat.zero_le _
    · exact (hU i h).1.trans (rk_coarseA_le p S b i)
  · rcases Nat.lt_or_ge (i : ℕ) S.sigma with h | h
    · exact (hS i h).2.1.trans (rk_coarseA_le p S b i)
    · rw [(hU i h).2.2.1]; exact Nat.zero_le _
  · rcases Nat.lt_or_ge (i : ℕ) S.sigma with h | h
    · exact (hS i h).2.2.1.trans (rk_coarseC_le p S aTop b i)
    · rw [(hU i h).2.2.2]; exact Nat.zero_le _
  · apply Nat.le_floor
    refine hO.trans ?_
    unfold Oplus
    rw [hM]
    have : ((cap p S b s : ℤ) : ℝ) ≤ ((S.A0 p + ∑ i : Fin s, (S.bTop i : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast rk_cap_le p S b s
    linarith

end Kept

section RankPi

variable {O : Type} [CommRing O] [IsDomain O]

theorem rank_prod_dom (M N : Type) [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] :
    Module.rank O (M × N) = Module.rank O M + Module.rank O N := by
  have h := rank_quotient_add_rank_of_isDomain (LinearMap.ker (LinearMap.snd O M N))
  have e1 : ((M × N) ⧸ LinearMap.ker (LinearMap.snd O M N)) ≃ₗ[O] N :=
    (LinearMap.snd O M N).quotKerEquivOfSurjective LinearMap.snd_surjective
  have e2 : M ≃ₗ[O] LinearMap.ker (LinearMap.snd O M N) := by
    rw [LinearMap.ker_snd]
    exact LinearEquiv.ofInjective (LinearMap.inl O M N) LinearMap.inl_injective
  rw [e1.rank_eq, ← e2.rank_eq] at h
  rw [← h, add_comm]

theorem rank_pi_dom (ι : Type) [Finite ι] : ∀ (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module O (M i)],
    Module.rank O (∀ i, M i) = ∑ᶠ i, Module.rank O (M i) := by
  refine Finite.induction_empty_option (P := fun ι => ∀ (M : ι → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module O (M i)], Module.rank O (∀ i, M i) = ∑ᶠ i, Module.rank O (M i)) ?_ ?_ ?_ ι
  · intro α β e h M _ _
    have h1 := h (fun a => M (e a))
    have e2 : (∀ a, M (e a)) ≃ₗ[O] (∀ b, M b) := LinearEquiv.piCongrLeft O M e
    rw [← e2.rank_eq, h1]
    exact finsum_comp_equiv e (f := fun b => Module.rank O (M b))
  · intro M _ _
    rw [finsum_of_isEmpty]
    simp
  · intro α _ h M _ _
    have e2 : (∀ i : Option α, M i) ≃ₗ[O] (M none × ∀ a : α, M (some a)) := LinearEquiv.piOptionEquivProd O
    rw [e2.rank_eq, rank_prod_dom, h (fun a => M (some a))]
    have := Fintype.ofFinite α
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_option]

end RankPi

section SegRank

variable {s : ℕ} (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r]
  (S : SegData s)

def keptSet (aTop : Fin s → ℕ) : Finset (SegBlock s r) := (kept_finite p r S aTop).toFinset

theorem mem_keptSet (aTop : Fin s → ℕ) (b : SegBlock s r) : b ∈ keptSet p r S aTop ↔ Kept p r S aTop b := by
  unfold keptSet
  rw [Set.Finite.mem_toFinset]
  rfl

theorem mem_segSub (aTop : Fin s → ℕ)
    (L₂ : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O))) (x : SegVs O r s S.t) :
    x ∈ segSub O p r S aTop L₂ ↔ (∀ b, Kept p r S aTop b → x b ∈ L₂ b) ∧ ∀ b, ¬ Kept p r S aTop b → x b = 0 := by
  classical
  unfold segSub
  rw [Submodule.mem_pi]
  constructor
  · intro h
    refine ⟨fun b hk => ?_, fun b hk => ?_⟩
    · have := h b (Set.mem_univ _)
      simpa only [if_pos hk] using this
    · have := h b (Set.mem_univ _)
      simp only [if_neg hk] at this
      exact (Submodule.mem_bot O).1 this
  · rintro ⟨h1, h2⟩ b -
    by_cases hk : Kept p r S aTop b
    · simp only [if_pos hk]; exact h1 b hk
    · simp only [if_neg hk]; rw [h2 b hk]; exact Submodule.zero_mem _

def segSubMap (aTop : Fin s → ℕ)
    (L₂ : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O))) :
    segSub O p r S aTop L₂ →ₗ[O] (∀ b : keptSet p r S aTop, L₂ b.1) where
  toFun := fun x b => ⟨x.1 b.1, ((mem_segSub O p r S aTop L₂ x.1).1 x.2).1 b.1 ((mem_keptSet p r S aTop b.1).1 b.2)⟩
  map_add' := fun x y => by funext b; apply Subtype.ext; rfl
  map_smul' := fun c x => by funext b; apply Subtype.ext; rfl

open Classical in

def segSubEquiv (aTop : Fin s → ℕ)
    (L₂ : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O))) :
    segSub O p r S aTop L₂ ≃ₗ[O] (∀ b : keptSet p r S aTop, L₂ b.1) :=
  LinearEquiv.ofBijective (segSubMap O p r S aTop L₂)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      funext b
      by_cases hk : Kept p r S aTop b
      · have := congrFun hxy ⟨b, (mem_keptSet p r S aTop b).2 hk⟩
        exact congrArg Subtype.val this
      · rw [((mem_segSub O p r S aTop L₂ x.1).1 x.2).2 b hk, ((mem_segSub O p r S aTop L₂ y.1).1 y.2).2 b hk],
     by
      intro y
      refine ⟨⟨fun b => if hk : Kept p r S aTop b then
        ((y ⟨b, (mem_keptSet p r S aTop b).2 hk⟩ : L₂ b) : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) else 0, ?_⟩, ?_⟩
      · rw [mem_segSub]
        refine ⟨fun b hk => ?_, fun b hk => ?_⟩
        · simp only [dif_pos hk]
          exact (y ⟨b, (mem_keptSet p r S aTop b).2 hk⟩).2
        · simp only [dif_neg hk]
      · funext b
        apply Subtype.ext
        show (if hk : Kept p r S aTop b.1 then
          ((y ⟨b.1, (mem_keptSet p r S aTop b.1).2 hk⟩ : L₂ b.1) : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) else 0) = _
        rw [dif_pos ((mem_keptSet p r S aTop b.1).1 b.2)]⟩

theorem rank_segSub (aTop : Fin s → ℕ)
    (L₂ : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O))) :
    Module.rank O (segSub O p r S aTop L₂) = ∑ b ∈ keptSet p r S aTop, Module.rank O (L₂ b) := by
  rw [(segSubEquiv O p r S aTop L₂).rank_eq, rank_pi_dom, finsum_eq_sum_of_fintype]
  exact Finset.sum_coe_sort (keptSet p r S aTop) (fun b => Module.rank O (L₂ b))

theorem finrank_segSub (aTop : Fin s → ℕ)
    (L₂ : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)))
    (h : ∀ b ∈ keptSet p r S aTop, Module.rank O (L₂ b) < Cardinal.aleph0) :
    Module.finrank O (segSub O p r S aTop L₂) = ∑ b ∈ keptSet p r S aTop, Module.finrank O (L₂ b) := by
  unfold Module.finrank
  rw [rank_segSub]
  have h1 : ∑ b ∈ keptSet p r S aTop, Module.rank O (L₂ b) =
      ((∑ b ∈ keptSet p r S aTop, Cardinal.toNat (Module.rank O (L₂ b)) : ℕ) : Cardinal) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun b hb => (Cardinal.cast_toNat_of_lt_aleph0 (h b hb)).symm
  rw [h1, Cardinal.toNat_natCast]

theorem finrank_segSub_zero (aTop : Fin s → ℕ)
    (L₂ : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)))
    (b : SegBlock s r) (hb : b ∈ keptSet p r S aTop) (h : Cardinal.aleph0 ≤ Module.rank O (L₂ b)) :
    Module.finrank O (segSub O p r S aTop L₂) = 0 := by
  unfold Module.finrank
  rw [rank_segSub]
  apply Cardinal.toNat_apply_of_aleph0_le
  exact h.trans (Finset.single_le_sum (f := fun b => Module.rank O (L₂ b)) (fun _ _ => zero_le) hb)

theorem segLat_eq_segSub (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) :
    segLat O p r S aTop aPlus m = segSub O p r S aTop (fun b => blockLat O p r S aTop aPlus m b) := rfl

end SegRank

def shareB (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) (g : (Fin X.s → ℕ) → ℕ → SegBlock X.s X.r → ℕ)
    (aTop : Fin X.s → ℕ) (aPlus : ℕ) : ℝ :=
  ((∑ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop, g aTop aPlus b : ℕ) : ℝ) /
    ((∑ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop,
      Module.finrank X.O (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) : ℕ) : ℝ)

def BlockFormSegmentRemaining (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ < X.L.Y →
    ∃ g : (Fin X.s → ℕ) → ℕ → SegBlock X.s X.r → ℕ,
      (∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
        ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
          ∃ L₂ : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
            GoodSub X.p (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b)
              (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) L₂
              (depthD C X.p X.L.a X.Nt X.N₁ X.r X.L.Y) ∧
            Module.finrank X.O (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) ≤
              Module.finrank X.O L₂ + g aTop aPlus b) ∧
      meanBox X (shareB C0 CE1 CE2 X g) ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ / X.L.Y

theorem block_form_of_segment_form (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst)
    (h : BlockFormSegmentRemaining C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X) : RemainingCountingStatement C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X := by
  classical
  intro hH hY
  obtain ⟨g, hg, hmean⟩ := h hH hY
  refine ⟨shareB C0 CE1 CE2 X g, fun aTop ha aPlus hp => ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩, hmean⟩
  choose L₂ hL₂ using hg aTop ha aPlus hp
  set L : SegBlock X.s X.r → Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)) :=
    fun b => if hk : Kept X.p X.r (X.S C0 CE1 CE2) aTop b then L₂ b hk else ⊥ with hL
  have hLk : ∀ b (hk : Kept X.p X.r (X.S C0 CE1 CE2) aTop b), L b = L₂ b hk := fun b hk => by
    rw [hL]; simp only [dif_pos hk]
  refine ⟨L, fun b hk => by rw [hLk b hk]; exact (hL₂ b hk).1, ?_⟩
  rw [segLat_eq_segSub]
  by_cases hinf : ∃ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop,
      Cardinal.aleph0 ≤ Module.rank X.O (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b)
  · obtain ⟨b, hb, hbi⟩ := hinf
    rw [finrank_segSub_zero X.O X.p X.r (X.S C0 CE1 CE2) aTop _ b hb hbi, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _
  · push Not at hinf
    have hfin2 : ∀ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop, Module.rank X.O (L b) < Cardinal.aleph0 := by
      intro b hb
      have hk := (mem_keptSet X.p X.r (X.S C0 CE1 CE2) aTop b).1 hb
      refine lt_of_le_of_lt (Submodule.rank_mono ?_) (hinf b hb)
      rw [hLk b hk]
      exact (hL₂ b hk).1.1.1
    rw [finrank_segSub X.O X.p X.r (X.S C0 CE1 CE2) aTop _ hinf, finrank_segSub X.O X.p X.r (X.S C0 CE1 CE2) aTop _ hfin2]
    have hsum : ∑ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop,
          Module.finrank X.O (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) ≤
        ∑ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop, Module.finrank X.O (L b) +
          ∑ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop, g aTop aPlus b := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun b hb => ?_
      have hk := (mem_keptSet X.p X.r (X.S C0 CE1 CE2) aTop b).1 hb
      rw [hLk b hk]
      exact (hL₂ b hk).2
    unfold shareB
    generalize (∑ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop,
      Module.finrank X.O (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b)) = R at hsum ⊢
    generalize (∑ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop, Module.finrank X.O (L b)) = R₂ at hsum ⊢
    generalize (∑ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop, g aTop aPlus b) = G at hsum ⊢
    have hsumR : (R : ℝ) ≤ (R₂ : ℝ) + (G : ℝ) := by exact_mod_cast hsum
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp
    · have hR' : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
      have : (1 - (G : ℝ) / (R : ℝ)) * (R : ℝ) = (R : ℝ) - (G : ℝ) := by field_simp
      rw [this]
      linarith

theorem counting_statement_of_segment_form (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst)
    (h : BlockFormSegmentRemaining C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X) : Conclusion1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X :=
  counting_statement_of_block_form D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X (block_form_of_segment_form C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X h)

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.MainNotions.G Finset

open Classical in

theorem double_count {α δ : Type*} (A : Finset α) (Dl : Finset δ) (rel : δ → α → Prop)
    (n rk m : δ → α → ℝ) (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hn : ∀ d ∈ Dl, ∀ a ∈ A, 0 ≤ n d a) (hm : ∀ d ∈ Dl, ∀ a ∈ A, 0 ≤ m d a)
    (hrk : ∀ d ∈ Dl, ∀ a ∈ A, rel d a → m d a / 2 ≤ rk d a)
    (hC5 : ∀ d ∈ Dl, ∑ a ∈ A.filter (rel d), n d a ≤ ε * ∑ a ∈ A.filter (rel d), m d a)
    (hFlat : ∀ a ∈ A, ∀ a' ∈ A, ∑ d ∈ Dl.filter (fun d => rel d a), m d a ≤
      K * ∑ d ∈ Dl.filter (fun d => rel d a'), m d a') :
    ∑ a ∈ A, (∑ d ∈ Dl.filter (fun d => rel d a), n d a) / (∑ d ∈ Dl.filter (fun d => rel d a), rk d a) ≤
      2 * ε * K * A.card := by
  set N : α → ℝ := fun a => ∑ d ∈ Dl.filter (fun d => rel d a), n d a with hN
  set M : α → ℝ := fun a => ∑ d ∈ Dl.filter (fun d => rel d a), m d a with hM
  set Den : α → ℝ := fun a => ∑ d ∈ Dl.filter (fun d => rel d a), rk d a with hDen
  have hN0 : ∀ a ∈ A, 0 ≤ N a := fun a ha => Finset.sum_nonneg fun d hd => hn d (Finset.mem_filter.1 hd).1 a ha
  have hM0 : ∀ a ∈ A, 0 ≤ M a := fun a ha => Finset.sum_nonneg fun d hd => hm d (Finset.mem_filter.1 hd).1 a ha
  have hDM : ∀ a ∈ A, M a / 2 ≤ Den a := by
    intro a ha
    simp only [hM, hDen]
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun d hd => hrk d (Finset.mem_filter.1 hd).1 a ha (Finset.mem_filter.1 hd).2
  have swap : ∀ f : δ → α → ℝ, ∑ a ∈ A, ∑ d ∈ Dl.filter (fun d => rel d a), f d a =
      ∑ d ∈ Dl, ∑ a ∈ A.filter (rel d), f d a := by
    intro f
    simp only [Finset.sum_filter]
    exact Finset.sum_comm
  have hNM : ∑ a ∈ A, N a ≤ ε * ∑ a ∈ A, M a := by
    simp only [hN, hM]
    rw [swap n, swap m, Finset.mul_sum]
    exact Finset.sum_le_sum hC5
  set T : ℝ := ∑ a ∈ A, M a with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg hM0
  have hc0 : 0 ≤ K * (A.card : ℝ) := mul_nonneg hK (Nat.cast_nonneg _)
  rcases hT0.eq_or_lt with h0 | hpos
  · have hNs : ∑ a ∈ A, N a ≤ 0 := by rw [← h0, mul_zero] at hNM; exact hNM
    have hNz : ∀ a ∈ A, N a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hN0).1 (le_antisymm hNs (Finset.sum_nonneg hN0))
    have hz : ∑ a ∈ A, N a / Den a = 0 := Finset.sum_eq_zero fun a ha => by rw [hNz a ha, zero_div]
    rw [hz]
    have := mul_nonneg hε hc0
    nlinarith
  · have hTa : ∀ a ∈ A, T ≤ K * (A.card : ℝ) * M a := by
      intro a ha
      calc T = ∑ a' ∈ A, M a' := rfl
        _ ≤ ∑ _a' ∈ A, K * M a := Finset.sum_le_sum fun a' ha' => hFlat a' ha' a ha
        _ = K * (A.card : ℝ) * M a := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hterm : ∀ a ∈ A, N a / Den a ≤ N a * (2 * (K * (A.card : ℝ)) / T) := by
      intro a ha
      have h1 := hTa a ha
      have hMa := hM0 a ha
      have hcpos : 0 < K * (A.card : ℝ) := by
        rcases hc0.eq_or_lt with h | h
        · rw [← h, zero_mul] at h1; linarith
        · exact h
      have hD := hDM a ha
      have hDpos : 0 < Den a := by
        have : 0 < M a := by
          by_contra hc
          have : M a = 0 := le_antisymm (not_lt.1 hc) hMa
          rw [this, mul_zero] at h1; linarith
        linarith
      rw [div_le_iff₀ hDpos]
      have h2 : 1 ≤ 2 * (K * (A.card : ℝ)) / T * Den a := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul]
        nlinarith
      calc N a = N a * 1 := (mul_one _).symm
        _ ≤ N a * (2 * (K * (A.card : ℝ)) / T * Den a) := mul_le_mul_of_nonneg_left h2 (hN0 a ha)
        _ = N a * (2 * (K * (A.card : ℝ)) / T) * Den a := by ring
    calc ∑ a ∈ A, N a / Den a ≤ ∑ a ∈ A, N a * (2 * (K * (A.card : ℝ)) / T) := Finset.sum_le_sum hterm
      _ = (∑ a ∈ A, N a) * (2 * (K * (A.card : ℝ)) / T) := by rw [Finset.sum_mul]
      _ ≤ (ε * T) * (2 * (K * (A.card : ℝ)) / T) :=
          mul_le_mul_of_nonneg_right hNM (div_nonneg (by linarith) hT0)
      _ = 2 * ε * K * A.card := by field_simp

section Realise

variable {n' : ℕ}

theorem posAdd_inj (x : Fin n') (d d' : ℕ) (hd : d < n') (hd' : d' < n') (h : posAdd x d = posAdd x d') : d = d' := by
  have h1 : (x.val + d) % n' = (x.val + d') % n' := congrArg Fin.val h
  have h2 : d % n' = d' % n' := Nat.ModEq.add_left_cancel' x.val h1
  rwa [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd'] at h2

theorem segG_le (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : segG TT j ≤ n' := by
  unfold segG
  split_ifs
  · exact le_rfl
  · unfold cdist
    exact (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) (segStart TT j).isLt)).le

theorem segDists_mem (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    0 < (segDists TT j).get i ∧ (segDists TT j).get i < segG TT j := by
  have key : ∀ d ∈ segDists TT j, 0 < d ∧ d < segG TT j := by
    intro d h
    unfold segDists at h
    rw [Finset.mem_sort, Finset.mem_image] at h
    obtain ⟨s, hs, hsd⟩ := h
    rw [Finset.mem_filter] at hs
    rw [← hsd]
    exact ⟨hs.2.2.1, hs.2.2.2⟩
  exact key _ (List.get_mem _ _)

theorem segDists_nodup (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : (segDists TT j).Nodup := by
  unfold segDists
  exact Finset.sort_nodup _ _

theorem segPos_inj (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Function.Injective (segPos TT j) := by
  intro i i' h
  unfold segPos at h
  have h1 := posAdd_inj _ _ _ ((segDists_mem TT j i).2.trans_le (segG_le TT j))
    ((segDists_mem TT j i').2.trans_le (segG_le TT j)) h
  exact (List.Nodup.get_inj_iff (segDists_nodup TT j)).1 h1

theorem segPos_ne_next (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ≠ segNext TT j := by
  intro h
  obtain ⟨h0, h1⟩ := segDists_mem TT j i
  set d := (segDists TT j).get i with hd
  have hn : d < n' := h1.trans_le (segG_le TT j)
  have hx := (segStart TT j).isLt
  have hv : (segNext TT j).val = ((segStart TT j).val + d) % n' := by rw [← h]; rfl
  have hc : cdist (segStart TT j) (segNext TT j) = d := by
    unfold cdist
    rw [hv]
    have : (((segStart TT j).val + d) % n' + n' - (segStart TT j).val) % n' = d % n' := by
      have e1 : (((segStart TT j).val + d) % n' + n' - (segStart TT j).val) =
          ((segStart TT j).val + d) % n' + (n' - (segStart TT j).val) := by omega
      rw [e1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have e2 : (segStart TT j).val + d + (n' - (segStart TT j).val) = d + n' := by omega
      rw [e2, Nat.add_mod_right]
    rw [this, Nat.mod_eq_of_lt hn]
  unfold segG at h1
  rw [hc] at h1
  split_ifs at h1 with hz
  · omega
  · omega

open Classical in

def realW (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (a0 : ℕ) (aTop : Fin (segS TT j) → ℕ) (aPlus : ℕ) :
    Fin n' → ℕ :=
  fun s => if h : ∃ i, segPos TT j i = s then aTop h.choose else if s = segNext TT j then aPlus else a0

theorem realW_top (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (a0 : ℕ) (aTop : Fin (segS TT j) → ℕ) (aPlus : ℕ) :
    segATop TT (realW TT j a0 aTop aPlus) j = aTop := by
  funext i
  unfold segATop realW
  have h : ∃ i', segPos TT j i' = segPos TT j i := ⟨i, rfl⟩
  rw [dif_pos h]
  exact congrArg aTop (segPos_inj TT j h.choose_spec)

theorem realW_plus (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (a0 : ℕ) (aTop : Fin (segS TT j) → ℕ) (aPlus : ℕ) :
    segAPlus TT (realW TT j a0 aTop aPlus) j = aPlus := by
  unfold segAPlus realW
  have h : ¬ ∃ i', segPos TT j i' = segNext TT j := fun ⟨i, hi⟩ => segPos_ne_next TT j i hi
  rw [dif_neg h, if_pos rfl]

theorem realW_mem (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (a0 : ℕ) (aTop : Fin (segS TT j) → ℕ) (aPlus : ℕ)
    (P : ℕ → Prop) (h0 : P a0) (hT : ∀ i, P (aTop i)) (hP : P aPlus) (s : Fin n') :
    P (realW TT j a0 aTop aPlus s) := by
  unfold realW
  split_ifs
  · exact hT _
  · exact hP
  · exact h0

end Realise

section Concrete

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

abbrev DCl (X : flipOneThree.Inst) := (Fin X.s → Fin (X.r + 1) → ℕ) × (Fin X.s → Fin (X.r + 1) → ℕ)

def digSet : Finset (Fin X.s → Fin (X.r + 1) → ℕ) :=
  Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin (X.r + 1) => Finset.range ((X.S C0 CE1 CE2).P X.p i)

def clSet : Finset (DCl X) := digSet C0 CE1 CE2 X ×ˢ digSet C0 CE1 CE2 X

def Compat (dl : DCl X) (aTop : Fin X.s → ℕ) : Prop :=
  DigitsOK X.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2)

def mCl (dl : DCl X) (aTop : Fin X.s → ℕ) : ℕ :=
  Formalism.MainNotions.ColumnSystems.dimMM (X.L.m + 1) ((X.S C0 CE1 CE2).A0 X.L.p)
            (fun i => coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) i)
            (fun i => coarseC X.L.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) i) *
    Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) ((X.S C0 CE1 CE2).bPlus : ℤ)

open Classical in

def keptSum (f : SegBlock X.s X.r → ℕ) (aTop : Fin X.s → ℕ) : ℕ :=
  ∑ᶠ b : SegBlock X.s X.r, if Kept X.p X.r (X.S C0 CE1 CE2) aTop b then f b else 0

open Classical in

def clSum (f : SegBlock X.s X.r → ℕ) (aTop : Fin X.s → ℕ) (dl : DCl X) : ℕ :=
  ∑ᶠ b : SegBlock X.s X.r,
    if Kept X.p X.r (X.S C0 CE1 CE2) aTop b ∧ b.rz = dl.1 ∧ b.ry = dl.2 then f b else 0

abbrev bRank (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) : ℕ :=
  blockRank X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b

def box : Finset ((Fin X.s → ℕ) × ℕ) := Fintype.piFinset (fun _ : Fin X.s => X.winA) ×ˢ X.winA

variable {C0 CE1 CE2 X}

theorem keptSum_eq_sum {aTop : Fin X.s → ℕ} (hfin : {b | Kept X.p X.r (X.S C0 CE1 CE2) aTop b}.Finite)
    (f : SegBlock X.s X.r → ℕ) : keptSum C0 CE1 CE2 X f aTop = ∑ b ∈ hfin.toFinset, f b := by
  classical
  unfold keptSum
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hk : Kept X.p X.r (X.S C0 CE1 CE2) aTop b := hfin.mem_toFinset.1 hb
    rw [if_pos hk]
  · intro b hb
    rw [Function.mem_support] at hb
    rw [Finset.mem_coe, hfin.mem_toFinset]
    by_contra hk
    exact hb (if_neg hk)

theorem clSum_eq_sum {aTop : Fin X.s → ℕ} (hfin : {b | Kept X.p X.r (X.S C0 CE1 CE2) aTop b}.Finite)
    (f : SegBlock X.s X.r → ℕ) (dl : DCl X) :
    clSum C0 CE1 CE2 X f aTop dl = ∑ b ∈ hfin.toFinset.filter (fun b => (b.rz, b.ry) = dl), f b := by
  classical
  unfold clSum
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset), Finset.sum_filter]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hk : Kept X.p X.r (X.S C0 CE1 CE2) aTop b := hfin.mem_toFinset.1 hb
    by_cases h : (b.rz, b.ry) = dl
    · rw [if_pos h, if_pos ⟨hk, congrArg Prod.fst h, congrArg Prod.snd h⟩]
    · rw [if_neg h, if_neg]
      rintro ⟨-, h1, h2⟩
      exact h (Prod.ext h1 h2)
  · intro b hb
    rw [Function.mem_support] at hb
    rw [Finset.mem_coe, hfin.mem_toFinset]
    by_contra hk
    exact hb (if_neg fun h => hk h.1)

open Classical in

theorem keptSum_eq_classes {aTop : Fin X.s → ℕ} (hfin : {b | Kept X.p X.r (X.S C0 CE1 CE2) aTop b}.Finite)
    (f : SegBlock X.s X.r → ℕ) :
    keptSum C0 CE1 CE2 X f aTop =
      ∑ dl ∈ (clSet C0 CE1 CE2 X).filter (fun dl => Compat C0 CE1 CE2 X dl aTop), clSum C0 CE1 CE2 X f aTop dl := by
  rw [keptSum_eq_sum hfin]
  simp only [clSum_eq_sum hfin]
  refine (Finset.sum_fiberwise_of_maps_to (g := fun b : SegBlock X.s X.r => (b.rz, b.ry)) ?_ f).symm
  intro b hb
  have hk : Kept X.p X.r (X.S C0 CE1 CE2) aTop b := hfin.mem_toFinset.1 hb
  have hd : DigitsOK X.p (X.S C0 CE1 CE2) aTop b := hk.1
  rw [Finset.mem_filter]
  refine ⟨?_, hd⟩
  unfold clSet digSet
  rw [Finset.mem_product]
  constructor
  · rw [Fintype.mem_piFinset]; intro i
    rw [Fintype.mem_piFinset]; intro c
    exact Finset.mem_range.2 (hd.1 i c).1
  · rw [Fintype.mem_piFinset]; intro i
    rw [Fintype.mem_piFinset]; intro c
    exact Finset.mem_range.2 (hd.1 i c).2

theorem rankOnDigits_eq (aT' : Fin X.L.n' → ℕ) (rz ry : Fin X.s → Fin (X.r + 1) → ℕ) :
    Formalism.MainNotions.ColumnSystems.rankOnDigits X.O C0 CE1 CE2 (X.LA aT') X.j X.m rz ry =
      clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X (segATop X.L.TT aT' X.j) (segAPlus X.L.TT aT' X.j))
        (segATop X.L.TT aT' X.j) (rz, ry) := rfl

theorem realise {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (aTop : Fin X.s → ℕ) (aPlus : ℕ)
    (hT : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (hP : aPlus ∈ X.winA) :
    X.InWinA (realW X.L.TT X.j X.L.a aTop aPlus) := by
  obtain ⟨h0, -, hxa, -, -, -, hb, -, -, -⟩ := hH
  have hY : (1 : ℝ) ≤ X.L.Y := h0.1
  have hk : (0 : ℝ) < X.L.k := by unfold Formalism.MainNotions.ColumnSystems.Loc.k; positivity
  have hq : (0 : ℝ) ≤ (X.L.a : ℝ) / (X.L.k * X.L.Y) := by
    apply div_nonneg (Nat.cast_nonneg _)
    exact (mul_pos hk (by linarith)).le
  have hw : ∀ x ∈ X.winA, (X.L.a : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ X.L.a + X.L.a / (X.L.k * X.L.Y) + X.xa := by
    intro x hx
    unfold flipOneThree.Inst.winA at hx
    rw [Finset.mem_Icc] at hx
    refine ⟨by exact_mod_cast hx.1, ?_⟩
    have h1 : (x : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast hx.2
    exact h1.trans (Nat.floor_le (by positivity))
  refine ⟨fun s _ => ?_, hb⟩
  exact realW_mem X.L.TT X.j X.L.a aTop aPlus
    (fun x => (X.L.a : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ X.L.a + X.L.a / (X.L.k * X.L.Y) + X.xa)
    ⟨le_rfl, by linarith⟩ (fun i => hw _ (Fintype.mem_piFinset.1 hT i)) (hw _ hP) s

theorem rank_ge {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (aTop : Fin X.s → ℕ) (aPlus : ℕ)
    (hT : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (hP : aPlus ∈ X.winA) (dl : DCl X)
    (hc : Compat C0 CE1 CE2 X dl aTop) :
    (mCl C0 CE1 CE2 X dl aTop : ℝ) / 2 ≤ (clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop dl : ℝ) := by
  have hIn := realise hH aTop aPlus hT hP
  have hm0 : 0 ≤ X.m := hH.2.2.2.2.2.2.2.2.1
  have hm1 : X.m ≤ X.L.b' / (X.L.k * X.L.Q * X.L.Y) := hH.2.2.2.2.2.2.2.2.2
  have h := h11 hH (realW X.L.TT X.j X.L.a aTop aPlus) hIn X.m hm0 hm1 dl.1 dl.2
  rw [rankOnDigits_eq, realW_top, realW_plus] at h
  exact (h hc).1

variable (C0 CE1 CE2 X)

open Classical in

def MCl (aTop : Fin X.s → ℕ) : ℝ :=
  ∑ dl ∈ (clSet C0 CE1 CE2 X).filter (fun dl => Compat C0 CE1 CE2 X dl aTop), (mCl C0 CE1 CE2 X dl aTop : ℝ)

open Classical in

def DigitClassDimensionComparison (g : (Fin X.s → ℕ) → ℕ → SegBlock X.s X.r → ℕ) (ε : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X,
    ∑ a ∈ (box X).filter (fun a => Compat C0 CE1 CE2 X dl a.1), (clSum C0 CE1 CE2 X (g a.1 a.2) a.1 dl : ℝ) ≤
      ε * ∑ a ∈ (box X).filter (fun a => Compat C0 CE1 CE2 X dl a.1), (mCl C0 CE1 CE2 X dl a.1 : ℝ)

def RestFlat (K : ℝ) : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aTop' ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA),
    MCl C0 CE1 CE2 X aTop ≤ K * MCl C0 CE1 CE2 X aTop'

variable {C0 CE1 CE2 X}

theorem box_card : ((box X).card : ℝ) = (X.winA.card : ℝ) ^ (X.s + 1) := by
  unfold box
  rw [Finset.card_product, Nat.cast_mul, card_box]

theorem meanBox_eq (κ : (Fin X.s → ℕ) → ℕ → ℝ) :
    meanBox X κ = (∑ a ∈ box X, κ a.1 a.2) / (X.winA.card : ℝ) ^ (X.s + 1) := by
  unfold meanBox box
  rw [Finset.sum_product]

open Classical in

theorem mean_of_classes {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X)
    (hfin : ∀ aTop : Fin X.s → ℕ, {b | Kept X.p X.r (X.S C0 CE1 CE2) aTop b}.Finite)
    (g : (Fin X.s → ℕ) → ℕ → SegBlock X.s X.r → ℕ) (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hC5 : DigitClassDimensionComparison C0 CE1 CE2 X g ε) (hFlat : RestFlat C0 CE1 CE2 X K) :
    meanBox X (fun aTop aPlus => (keptSum C0 CE1 CE2 X (g aTop aPlus) aTop : ℝ) /
      (keptSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop : ℝ)) ≤ 2 * ε * K := by
  rw [meanBox_eq]
  have hmem : ∀ a ∈ box X, a.1 ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ a.2 ∈ X.winA := by
    intro a ha
    unfold box at ha
    exact Finset.mem_product.1 ha
  have key := double_count (box X) (clSet C0 CE1 CE2 X) (fun dl a => Compat C0 CE1 CE2 X dl a.1)
    (fun dl a => (clSum C0 CE1 CE2 X (g a.1 a.2) a.1 dl : ℝ))
    (fun dl a => (clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X a.1 a.2) a.1 dl : ℝ))
    (fun dl a => (mCl C0 CE1 CE2 X dl a.1 : ℝ)) ε K hε hK
    (fun _ _ _ _ => Nat.cast_nonneg _) (fun _ _ _ _ => Nat.cast_nonneg _)
    (fun dl _ a ha hc => rank_ge hH h11 a.1 a.2 (hmem a ha).1 (hmem a ha).2 dl hc)
    hC5 (fun a ha a' ha' => hFlat a.1 (hmem a ha).1 a'.1 (hmem a' ha').1)
  have hsum : ∑ a ∈ box X, (keptSum C0 CE1 CE2 X (g a.1 a.2) a.1 : ℝ) /
      (keptSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X a.1 a.2) a.1 : ℝ) ≤ 2 * ε * K * (box X).card := by
    refine le_trans (le_of_eq ?_) key
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [keptSum_eq_classes (hfin a.1), keptSum_eq_classes (hfin a.1), Nat.cast_sum, Nat.cast_sum]
  rw [box_card] at hsum
  exact div_le_of_le_mul₀ (by positivity) (by positivity) hsum

end Concrete

def RestRk (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      Module.finrank X.O (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) =
        blockRank X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b

def ScaledSegmentRemaining (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ < X.L.Y →
    ∃ (g : (Fin X.s → ℕ) → ℕ → SegBlock X.s X.r → ℕ) (ε K : ℝ), 0 ≤ ε ∧ 0 ≤ K ∧
      2 * ε * K ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ / X.L.Y ∧
      (∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
        ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
          ∃ L₂ : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
            GoodSub X.p (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b)
              (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) L₂
              (depthD C X.p X.L.a X.Nt X.N₁ X.r X.L.Y) ∧
            Module.finrank X.O (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) ≤
              Module.finrank X.O L₂ + g aTop aPlus b) ∧
      DigitClassDimensionComparison C0 CE1 CE2 X g ε ∧ RestFlat C0 CE1 CE2 X K

theorem shareB_eq {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst} (hrk : RestRk C0 CE1 CE2 X)
    (g : (Fin X.s → ℕ) → ℕ → SegBlock X.s X.r → ℕ) (aTop : Fin X.s → ℕ)
    (ha : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (aPlus : ℕ) (hp : aPlus ∈ X.winA) :
    shareB C0 CE1 CE2 X g aTop aPlus = (keptSum C0 CE1 CE2 X (g aTop aPlus) aTop : ℝ) /
      (keptSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop : ℝ) := by
  unfold shareB
  rw [keptSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop),
    keptSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop)]
  have h2 : ∑ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop,
      Module.finrank X.O (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) =
      ∑ b ∈ keptSet X.p X.r (X.S C0 CE1 CE2) aTop, bRank C0 CE1 CE2 X aTop aPlus b :=
    Finset.sum_congr rfl fun b hb => hrk aTop ha aPlus hp b ((mem_keptSet X.p X.r (X.S C0 CE1 CE2) aTop b).1 hb)
  rw [h2]
  rfl

theorem segment_form_of_scaled_form (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (hrk : RestRk C0 CE1 CE2 X)
    (h : ScaledSegmentRemaining C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X) : BlockFormSegmentRemaining C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X := by
  intro hH hY
  obtain ⟨g, ε, K, hε, hK, hb, hg, hC5, hFlat⟩ := h hH hY
  refine ⟨g, hg, ?_⟩
  have hm := mean_of_classes hH h11 (fun aTop => kept_finite X.p X.r (X.S C0 CE1 CE2) aTop) g ε K hε hK hC5 hFlat
  refine le_trans (meanBox_mono X _ _ fun aTop ha aPlus hp => le_of_eq ?_) (hm.trans hb)
  exact shareB_eq hrk g aTop ha aPlus hp

theorem counting_theorem_of_remaining_sum (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (hrk : RestRk C0 CE1 CE2 X)
    (h : ScaledSegmentRemaining C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X) : Conclusion1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X :=
  counting_statement_of_segment_form D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X
    (segment_form_of_scaled_form D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X h11 hrk h)

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.MainNotions.G Finset

section Digits

def Ev (k n : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => range (n + 1)).filter (fun e => ∑ c, e c = n)

theorem mem_Ev {k n : ℕ} (e : Fin k → ℕ) : e ∈ Ev k n ↔ ∑ c, e c = n := by
  unfold Ev
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun c => ?_, h⟩⟩
  rw [Finset.mem_range, Nat.lt_succ_iff, ← h]
  exact Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

theorem card_Ev (k n : ℕ) : (Ev k n).card = (k + n - 1).choose n := by
  have h := Finset.card_finsuppAntidiag_nat_eq_choose (s := (Finset.univ : Finset (Fin k))) n
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  symm
  refine Finset.card_bij (fun f _ => (f : Fin k → ℕ)) ?_ ?_ ?_
  · intro f hf
    rw [mem_Ev]
    exact (Finset.mem_finsuppAntidiag.1 hf).1
  · intro f _ g _ hfg
    exact DFunLike.coe_injective hfg
  · intro e he
    refine ⟨Finsupp.equivFunOnFinite.symm e, ?_, rfl⟩
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨(mem_Ev e).1 he, Finset.subset_univ _⟩

open Classical in

theorem card_Ev_digits (k a P : ℕ) (hP : 0 < P) :
    (Ev k a).card = ∑ ρ ∈ Fintype.piFinset (fun _ : Fin k => range P),
      if (∑ c, ρ c ≤ a ∧ P ∣ a - ∑ c, ρ c) then (Ev k ((a - ∑ c, ρ c) / P)).card else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun e : Fin k → ℕ => fun c => e c % P)
    (t := Fintype.piFinset (fun _ : Fin k => range P))]
  · refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hρ' : ∀ c, ρ c < P := fun c => Finset.mem_range.1 (Fintype.mem_piFinset.1 hρ c)
    split_ifs with hok
    · obtain ⟨hle, hdvd⟩ := hok
      symm
      refine Finset.card_bij (fun e' _ => fun c => ρ c + P * e' c) ?_ ?_ ?_
      · intro e' he'
        rw [Finset.mem_filter, mem_Ev]
        constructor
        · rw [Finset.sum_add_distrib, ← Finset.mul_sum, (mem_Ev e').1 he', Nat.mul_div_cancel' hdvd]
          omega
        · funext c
          show (ρ c + P * e' c) % P = ρ c
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hρ' c)]
      · intro e1 _ e2 _ h
        funext c
        have := congrFun h c
        have h2 : P * e1 c = P * e2 c := by omega
        exact Nat.eq_of_mul_eq_mul_left hP h2
      · intro e he
        rw [Finset.mem_filter, mem_Ev] at he
        obtain ⟨hs, hm⟩ := he
        have hdec : ∀ c, e c = ρ c + P * (e c / P) := by
          intro c
          have h1 := congrFun hm c
          rw [← h1]
          exact (Nat.mod_add_div _ _).symm
        refine ⟨fun c => e c / P, ?_, ?_⟩
        · rw [mem_Ev]
          have h3 : a = ∑ c, ρ c + P * ∑ c, e c / P := by
            rw [← hs, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun c _ => hdec c
          have h4 : a - ∑ c, ρ c = P * ∑ c, e c / P := by omega
          rw [h4, Nat.mul_div_cancel_left _ hP]
        · funext c
          exact (hdec c).symm
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hm
      apply hok
      have hs := (mem_Ev e).1 he
      have hdec : ∀ c, e c = ρ c + P * (e c / P) := by
        intro c
        have h1 := congrFun hm c
        rw [← h1]
        exact (Nat.mod_add_div _ _).symm
      have h3 : a = ∑ c, ρ c + P * ∑ c, e c / P := by
        rw [← hs, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun c _ => hdec c
      refine ⟨by omega, ⟨∑ c, e c / P, by omega⟩⟩
  · intro e _
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro c
    exact Finset.mem_range.2 (Nat.mod_lt _ hP)

theorem symDim_eq (r n : ℕ) : Formalism.MainNotions.ColumnSystems.symDim (r + 1) (n : ℤ) = (Ev (r + 1) n).card := by
  unfold Formalism.MainNotions.ColumnSystems.symDim
  rw [if_neg (by omega), card_Ev, Int.toNat_natCast]
  have e1 : n + (r + 1) - 1 = n + r := by omega
  have e2 : r + 1 + n - 1 = n + r := by omega
  have e3 : r + 1 - 1 = r := by omega
  rw [e1, e2, e3]
  exact Nat.choose_symm_add.symm

theorem symDim_choose (r n : ℕ) : Formalism.MainNotions.ColumnSystems.symDim (r + 1) (n : ℤ) = (n + r).choose r := by
  unfold Formalism.MainNotions.ColumnSystems.symDim
  rw [if_neg (by omega), Int.toNat_natCast]
  have e1 : n + (r + 1) - 1 = n + r := by omega
  have e3 : r + 1 - 1 = r := by omega
  rw [e1, e3]

open Classical in

theorem symDim_digits (r a P : ℕ) (hP : 0 < P) :
    ∑ ρ ∈ Fintype.piFinset (fun _ : Fin (r + 1) => range P),
      (if (∑ c, ρ c ≤ a ∧ P ∣ a - ∑ c, ρ c) then Formalism.MainNotions.ColumnSystems.symDim (r + 1) (((a - ∑ c, ρ c) / P : ℕ) : ℤ) else 0) =
      Formalism.MainNotions.ColumnSystems.symDim (r + 1) (a : ℤ) := by
  rw [symDim_eq, card_Ev_digits (r + 1) a P hP]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  split_ifs
  · exact symDim_eq r _
  · rfl

theorem choose_ratio (r x y : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    (((y + r).choose r : ℕ) : ℝ) ≤ ((y : ℝ) / x) ^ r * (((x + r).choose r : ℕ) : ℝ) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hq : (1 : ℝ) ≤ (y : ℝ) / x := by rw [le_div_iff₀ hx0, one_mul]; exact_mod_cast hxy
  induction r with
  | zero => simp
  | succ r ih =>
    have hy := Nat.add_one_mul_choose_eq (y + r) r
    have hxx := Nat.add_one_mul_choose_eq (x + r) r
    have hy' : ((y : ℝ) + r + 1) * ((y + r).choose r : ℝ) = ((y + (r + 1)).choose (r + 1) : ℝ) * ((r : ℝ) + 1) := by
      have := congrArg (Nat.cast : ℕ → ℝ) hy
      push_cast at this
      rw [show y + (r + 1) = y + r + 1 by ring]
      linarith
    have hx' : ((x : ℝ) + r + 1) * ((x + r).choose r : ℝ) = ((x + (r + 1)).choose (r + 1) : ℝ) * ((r : ℝ) + 1) := by
      have := congrArg (Nat.cast : ℕ → ℝ) hxx
      push_cast at this
      rw [show x + (r + 1) = x + r + 1 by ring]
      linarith
    have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have hstep : (y : ℝ) + r + 1 ≤ (y : ℝ) / x * ((x : ℝ) + r + 1) := by
      have e : (y : ℝ) / x * ((x : ℝ) + r + 1) = y + (y : ℝ) / x * ((r : ℝ) + 1) := by
        field_simp
        ring
      rw [e]
      nlinarith
    have hc0 : (0 : ℝ) ≤ ((x + r).choose r : ℝ) := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ ((y : ℝ) / x) ^ r := by positivity
    have hmain : ((y + (r + 1)).choose (r + 1) : ℝ) * ((r : ℝ) + 1) ≤
        (((y : ℝ) / x) ^ (r + 1) * ((x + (r + 1)).choose (r + 1) : ℝ)) * ((r : ℝ) + 1) := by
      rw [← hy', mul_assoc, ← hx']
      calc ((y : ℝ) + r + 1) * ((y + r).choose r : ℝ)
          ≤ ((y : ℝ) + r + 1) * (((y : ℝ) / x) ^ r * ((x + r).choose r : ℝ)) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ ((y : ℝ) / x * ((x : ℝ) + r + 1)) * (((y : ℝ) / x) ^ r * ((x + r).choose r : ℝ)) :=
            mul_le_mul_of_nonneg_right hstep (mul_nonneg hq0 hc0)
        _ = ((y : ℝ) / x) ^ (r + 1) * (((x : ℝ) + r + 1) * ((x + r).choose r : ℝ)) := by ring
    exact le_of_mul_le_mul_right hmain hr1

end Digits

section Flat

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

open Classical in

def fA (i : Fin X.s) (ρ : Fin (X.r + 1) → ℕ) : ℕ :=
  if (∑ c, ρ c ≤ (X.S C0 CE1 CE2).bTop i ∧ (X.S C0 CE1 CE2).P X.p i ∣ (X.S C0 CE1 CE2).bTop i - ∑ c, ρ c) then
    Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) ((((X.S C0 CE1 CE2).bTop i - ∑ c, ρ c) / (X.S C0 CE1 CE2).P X.p i : ℕ) : ℤ) else 0

open Classical in

def fC (i : Fin X.s) (a : ℕ) (ρ : Fin (X.r + 1) → ℕ) : ℕ :=
  if (∑ c, ρ c ≤ a ∧ (X.S C0 CE1 CE2).P X.p i ∣ a - ∑ c, ρ c) then
    Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (((a - ∑ c, ρ c) / (X.S C0 CE1 CE2).P X.p i : ℕ) : ℤ) else 0

def cstM : ℕ :=
  Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) ((X.S C0 CE1 CE2).A0 X.p) * Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) ((X.S C0 CE1 CE2).bPlus : ℤ) *
    ∏ i : Fin X.s, ∑ ρ ∈ Fintype.piFinset (fun _ : Fin (X.r + 1) => range ((X.S C0 CE1 CE2).P X.p i)),
      fA C0 CE1 CE2 X i ρ

variable {C0 CE1 CE2 X}

open Classical in
theorem mCl_factor (rz ry : Fin X.s → Fin (X.r + 1) → ℕ) (hrz : rz ∈ digSet C0 CE1 CE2 X)
    (hry : ry ∈ digSet C0 CE1 CE2 X) (aTop : Fin X.s → ℕ) :
    (if Compat C0 CE1 CE2 X (rz, ry) aTop then mCl C0 CE1 CE2 X (rz, ry) aTop else 0) =
      Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) ((X.S C0 CE1 CE2).A0 X.p) *
        Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) ((X.S C0 CE1 CE2).bPlus : ℤ) *
        ((∏ i, fA C0 CE1 CE2 X i (rz i)) * ∏ i, fC C0 CE1 CE2 X i (aTop i) (ry i)) := by
  by_cases hc : Compat C0 CE1 CE2 X (rz, ry) aTop
  · rw [if_pos hc]
    obtain ⟨-, hA, hC⟩ := hc
    have e1 : (∏ i, fA C0 CE1 CE2 X i (rz i)) = ∏ i, Formalism.MainNotions.ColumnSystems.symDim (X.r + 1)
        ((coarseA X.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock rz ry) i : ℕ) : ℤ) :=
      Finset.prod_congr rfl fun i _ => by unfold fA; exact if_pos (hA i)
    have e2 : (∏ i, fC C0 CE1 CE2 X i (aTop i) (ry i)) = ∏ i, Formalism.MainNotions.ColumnSystems.symDim (X.r + 1)
        ((coarseC X.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock rz ry) i : ℕ) : ℤ) :=
      Finset.prod_congr rfl fun i _ => by unfold fC; exact if_pos (hC i)
    rw [e1, e2, ← Finset.prod_mul_distrib]
    unfold mCl Formalism.MainNotions.ColumnSystems.dimMM
    ring
  · rw [if_neg hc]
    have hd : ∀ i c, rz i c < (X.S C0 CE1 CE2).P X.p i ∧ ry i c < (X.S C0 CE1 CE2).P X.p i := by
      intro i c
      unfold digSet at hrz hry
      exact ⟨Finset.mem_range.1 (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hrz i) c),
        Finset.mem_range.1 (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hry i) c)⟩
    have hz : (∏ i, fA C0 CE1 CE2 X i (rz i)) * ∏ i, fC C0 CE1 CE2 X i (aTop i) (ry i) = 0 := by
      by_contra hne
      apply hc
      have h1 : (∏ i, fA C0 CE1 CE2 X i (rz i)) ≠ 0 := left_ne_zero_of_mul hne
      have h2 : (∏ i, fC C0 CE1 CE2 X i (aTop i) (ry i)) ≠ 0 := right_ne_zero_of_mul hne
      rw [Finset.prod_ne_zero_iff] at h1 h2
      refine ⟨hd, fun i => ?_, fun i => ?_⟩
      · by_contra hn
        exact h1 i (Finset.mem_univ i) (by unfold fA; exact if_neg hn)
      · by_contra hn
        exact h2 i (Finset.mem_univ i) (by unfold fC; exact if_neg hn)
    rw [hz, mul_zero]

open Classical in

theorem MCl_eq (hp : 0 < X.p) (aTop : Fin X.s → ℕ) :
    MCl C0 CE1 CE2 X aTop =
      ((cstM C0 CE1 CE2 X * ∏ i, Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop i : ℤ) : ℕ) : ℝ) := by
  unfold MCl
  rw [← Nat.cast_sum, Nat.cast_inj, Finset.sum_filter]
  unfold clSet
  rw [Finset.sum_product]
  have h1 : ∀ rz ∈ digSet C0 CE1 CE2 X, ∀ ry ∈ digSet C0 CE1 CE2 X,
      (if Compat C0 CE1 CE2 X (rz, ry) aTop then mCl C0 CE1 CE2 X (rz, ry) aTop else 0) =
      Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) ((X.S C0 CE1 CE2).A0 X.p) *
        Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) ((X.S C0 CE1 CE2).bPlus : ℤ) *
        ((∏ i, fA C0 CE1 CE2 X i (rz i)) * ∏ i, fC C0 CE1 CE2 X i (aTop i) (ry i)) :=
    fun rz hrz ry hry => mCl_factor rz ry hrz hry aTop
  rw [Finset.sum_congr rfl fun rz hrz => Finset.sum_congr rfl fun ry hry => h1 rz hrz ry hry]
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  have hA : ∑ rz ∈ digSet C0 CE1 CE2 X, ∏ i, fA C0 CE1 CE2 X i (rz i) =
      ∏ i : Fin X.s, ∑ ρ ∈ Fintype.piFinset (fun _ : Fin (X.r + 1) => range ((X.S C0 CE1 CE2).P X.p i)),
        fA C0 CE1 CE2 X i ρ := by
    unfold digSet
    exact (Finset.prod_univ_sum _ _).symm
  have hC : ∑ ry ∈ digSet C0 CE1 CE2 X, ∏ i, fC C0 CE1 CE2 X i (aTop i) (ry i) =
      ∏ i : Fin X.s, Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop i : ℤ) := by
    unfold digSet
    rw [← Finset.prod_univ_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold fC
    exact symDim_digits X.r (aTop i) _ (Nat.pow_pos hp)
  rw [hA, hC]
  unfold cstM
  ring

theorem restFlat_proved (hp : 0 < X.p) (ha : 1 ≤ X.L.a) :
    RestFlat C0 CE1 CE2 X
      (((((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) / X.L.a) ^ X.r) ^ X.s) := by
  intro aTop hT aTop' hT'
  rw [MCl_eq hp, MCl_eq hp]
  set hi : ℕ := ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ with hhi
  have hw : ∀ (f : Fin X.s → ℕ), f ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) → ∀ i, X.L.a ≤ f i ∧ f i ≤ hi := by
    intro f hf i
    have := Fintype.mem_piFinset.1 hf i
    unfold flipOneThree.Inst.winA at this
    exact Finset.mem_Icc.1 this
  have hone : ∀ i, (Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop i : ℤ) : ℝ) ≤
      ((hi : ℝ) / X.L.a) ^ X.r * (Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop' i : ℤ) : ℝ) := by
    intro i
    rw [symDim_choose, symDim_choose]
    have h1 : (((aTop i + X.r).choose X.r : ℕ) : ℝ) ≤ (((hi + X.r).choose X.r : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose X.r (Nat.add_le_add_right (hw aTop hT i).2 _)
    have h2 := choose_ratio X.r X.L.a hi ha ((hw aTop hT i).1.trans (hw aTop hT i).2)
    have h3 : (((X.L.a + X.r).choose X.r : ℕ) : ℝ) ≤ (((aTop' i + X.r).choose X.r : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose X.r (Nat.add_le_add_right (hw aTop' hT' i).1 _)
    have hq : (0 : ℝ) ≤ ((hi : ℝ) / X.L.a) ^ X.r := by positivity
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hq))
  have hprod : (∏ i, (Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop i : ℤ) : ℝ)) ≤
      (((hi : ℝ) / X.L.a) ^ X.r) ^ X.s * ∏ i, (Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop' i : ℤ) : ℝ) := by
    calc (∏ i, (Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop i : ℤ) : ℝ))
        ≤ ∏ i : Fin X.s, (((hi : ℝ) / X.L.a) ^ X.r * (Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop' i : ℤ) : ℝ)) :=
          Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hone i)
      _ = (((hi : ℝ) / X.L.a) ^ X.r) ^ X.s * ∏ i, (Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop' i : ℤ) : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  have hc : (0 : ℝ) ≤ (cstM C0 CE1 CE2 X : ℝ) := Nat.cast_nonneg _
  calc (cstM C0 CE1 CE2 X : ℝ) * ∏ i, (Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop i : ℤ) : ℝ)
      ≤ (cstM C0 CE1 CE2 X : ℝ) * ((((hi : ℝ) / X.L.a) ^ X.r) ^ X.s *
          ∏ i, (Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop' i : ℤ) : ℝ)) := mul_le_mul_of_nonneg_left hprod hc
    _ = (((hi : ℝ) / X.L.a) ^ X.r) ^ X.s * ((cstM C0 CE1 CE2 X : ℝ) *
          ∏ i, (Formalism.MainNotions.ColumnSystems.symDim (X.r + 1) (aTop' i : ℤ) : ℝ)) := by ring

theorem Kflat_num (A k Y La b' xa pp Yb N : ℝ) (r s : ℕ) (hkr : k = (r : ℝ) + 1) (hY : 1 ≤ Y)
    (hpk : k ^ 2 * Y ^ 2 ≤ pp) (hN : 1 ≤ N) (hLa0 : 0 ≤ La) (hb' : 0 < b') (hYb1 : 1 ≤ Yb)
    (hLak : 2 * Yb * N * La < k) (hA : 0 < A) (hpa : pp < A / b') (hxa0 : 0 ≤ xa) (hxa : xa ≤ 2 * (La * b' / k))
    (hs : (s : ℝ) ≤ Y) :
    ((((⌊A + A / (k * Y) + xa⌋₊ : ℕ) : ℝ) / A) ^ r) ^ s ≤ Real.exp 3 := by
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hs0' : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by rw [hkr]; linarith
  have hLk : La ≤ k := by
    have h2 : (1 : ℝ) ≤ 2 * Yb * N := by nlinarith
    have h3 : La ≤ 2 * Yb * N * La := by nlinarith [mul_le_mul_of_nonneg_right h2 hLa0]
    linarith
  have hpb : pp * b' < A := (lt_div_iff₀ hb').1 hpa
  have hxb : xa ≤ 2 * b' := by
    have h1 : La * b' / k ≤ b' := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hkY : (0 : ℝ) < k * Y := by positivity
  have hsr : (s : ℝ) * (r : ℝ) ≤ k * Y := by
    have : (r : ℝ) ≤ k := by rw [hkr]; linarith
    nlinarith
  have hkY1 : (1 : ℝ) ≤ k * Y := by nlinarith
  have hkk : k * Y ≤ k ^ 2 * Y ^ 2 := by nlinarith
  set δ : ℝ := 1 / (k * Y) + xa / A with hδ
  have hhi : ((⌊A + A / (k * Y) + xa⌋₊ : ℕ) : ℝ) ≤ A + A / (k * Y) + xa :=
    Nat.floor_le (by positivity)
  have hq : ((⌊A + A / (k * Y) + xa⌋₊ : ℕ) : ℝ) / A ≤ Real.exp δ := by
    have h1 : ((⌊A + A / (k * Y) + xa⌋₊ : ℕ) : ℝ) / A ≤ δ + 1 := by
      rw [div_le_iff₀ hA, hδ]
      have e : (1 / (k * Y) + xa / A + 1) * A = A + A / (k * Y) + xa := by
        field_simp
        ring
      rw [e]
      exact hhi
    exact h1.trans (Real.add_one_le_exp δ)
  have hq0 : (0 : ℝ) ≤ ((⌊A + A / (k * Y) + xa⌋₊ : ℕ) : ℝ) / A := by positivity
  have hpow : ((((⌊A + A / (k * Y) + xa⌋₊ : ℕ) : ℝ) / A) ^ r) ^ s ≤ (Real.exp δ ^ r) ^ s :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hq0 hq _) _
  refine hpow.trans ?_
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have t1 : (s : ℝ) * (r : ℝ) * (1 / (k * Y)) ≤ 1 := by
    rw [mul_one_div, div_le_one hkY]
    exact hsr
  have t2 : (s : ℝ) * (r : ℝ) * (xa / A) ≤ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hA]
    have h1 : (s : ℝ) * (r : ℝ) * xa ≤ (k * Y) * (2 * b') :=
      mul_le_mul hsr hxb hxa0 hkY.le
    have h2 : (k * Y) * b' ≤ pp * b' := mul_le_mul_of_nonneg_right (hkk.trans hpk) hb'.le
    nlinarith
  have e : (s : ℝ) * ((r : ℝ) * δ) =
      (s : ℝ) * (r : ℝ) * (1 / (k * Y)) + (s : ℝ) * (r : ℝ) * (xa / A) := by
    rw [hδ]; ring
  rw [e]
  linarith

theorem Kflat_le {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hs : (X.s : ℝ) ≤ X.L.Y) :
    ((((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) / X.L.a) ^ X.r) ^ X.s ≤ Real.exp 3 := by
  obtain ⟨h0, -, hxa0, hxa, -⟩ := hH
  obtain ⟨hY, hpk, ⟨s0, hs0, -⟩, -, -, -, -, hLa8, hb', -, -, -, -, hYb, hLak, -, -, hpa, -⟩ := h0
  have hN : (1 : ℝ) ≤ X.L.N := by
    unfold Formalism.MainNotions.ColumnSystems.Loc.N
    exact_mod_cast Finset.card_pos.2 ⟨s0, hs0⟩
  have hLa0 : 0 ≤ X.L.La C0 := by
    have h1 : (1 : ℝ) ≤ X.L.N * X.L.Y := by nlinarith
    have := Real.log_nonneg h1
    linarith
  have hp0 : (0 : ℝ) ≤ (X.L.p : ℝ) := Nat.cast_nonneg _
  have hA : (0 : ℝ) < (X.L.a : ℝ) := by
    by_contra h
    have hz : (X.L.a : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [hz, zero_div] at hpa
    linarith
  exact Kflat_num (X.L.a : ℝ) X.L.k X.L.Y (X.L.La C0) X.L.b' X.xa (X.L.p : ℝ) X.L.Yb X.L.N X.r X.s rfl hY hpk hN hLa0
    hb' (hCYb.trans hYb) hLak hA hpa hxa0 hxa hs

theorem restFlat_exp {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hs : (X.s : ℝ) ≤ X.L.Y) : RestFlat C0 CE1 CE2 X (Real.exp 3) := by
  have hp : 0 < X.p := X.std.1.prime.pos
  have ha : 1 ≤ X.L.a := by
    obtain ⟨-, -, -, -, -, -, -, -, hb', -, -, -, -, -, -, -, -, hpa, -⟩ := hH.1
    by_contra h
    have hz : X.L.a = 0 := by omega
    rw [hz, Nat.cast_zero, zero_div] at hpa
    have : (0 : ℝ) ≤ (X.L.p : ℝ) := Nat.cast_nonneg _
    linarith
  intro aTop hT aTop' hT'
  have h1 := restFlat_proved (C0 := C0) (CE1 := CE1) (CE2 := CE2) hp ha aTop hT aTop' hT'
  have h2 := Kflat_le hCYb hH hs
  have h3 : 0 ≤ MCl C0 CE1 CE2 X aTop' := by
    unfold MCl
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  exact h1.trans (mul_le_mul_of_nonneg_right h2 h3)

end Flat

def SegmentWeightedCountingBound (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ < X.L.Y →
    ∃ (g : (Fin X.s → ℕ) → ℕ → SegBlock X.s X.r → ℕ) (ε : ℝ), 0 ≤ ε ∧
      2 * ε * Real.exp 3 ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ / X.L.Y ∧
      (∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
        ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
          ∃ L₂ : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
            GoodSub X.p (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b)
              (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) L₂
              (depthD C X.p X.L.a X.Nt X.N₁ X.r X.L.Y) ∧
            Module.finrank X.O (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) ≤
              Module.finrank X.O L₂ + g aTop aPlus b) ∧
      DigitClassDimensionComparison C0 CE1 CE2 X g ε

theorem remaining_of_segment_bound (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst) (hCYb : 1 ≤ CYb) (hC : 1 ≤ C)
    (h : SegmentWeightedCountingBound C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X) : ScaledSegmentRemaining C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X := by
  intro hH hY
  obtain ⟨g, ε, hε, hb, hg, hC5⟩ := h hH hY
  have hsN : X.s ≤ X.N₁ := (hH.1.2.2.2.2.1 X.j).2
  have hs : (X.s : ℝ) ≤ X.L.Y := by
    have h1 : (X.s : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast hsN
    have h2 : (0 : ℝ) ≤ (X.N₁ : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).t : ℝ) := Nat.cast_nonneg _
    have h4 : (1 : ℝ) ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) := by nlinarith
    have h5 : (X.N₁ : ℝ) ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ := by nlinarith
    linarith
  exact ⟨g, ε, Real.exp 3, hε, (Real.exp_pos 3).le, hb, hg, hC5, restFlat_exp hCYb hH hs⟩

theorem counting_statement_of_digit_class_rank_form (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : flipOneThree.Inst) (hCYb : 1 ≤ CYb)
    (hC : 1 ≤ C) (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (hrk : RestRk C0 CE1 CE2 X)
    (h : SegmentWeightedCountingBound C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X) : Conclusion1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X :=
  counting_theorem_of_remaining_sum D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X h11 hrk
    (remaining_of_segment_bound C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X hCYb hC h)

theorem counting_statement_of_digit_class_form (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C : ℝ) (hCYb : 1 ≤ CYb) (hC : 1 ≤ C)
    (h : ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X →
      RestRk C0 CE1 CE2 X ∧ SegmentWeightedCountingBound C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X) :
    IntegralityFromMetric D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C := fun X hA =>
  counting_statement_of_digit_class_rank_form D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X hCYb hC (admissible_without_key_of_admissible hA).2.2.2.2.2.2
    (h X (admissible_without_key_of_admissible hA)).1 (h X (admissible_without_key_of_admissible hA)).2

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

section RankSpan

variable {O : Type} [CommRing O] [IsDomain O] {V : Type} [AddCommGroup V] [Module O V] [Module (KK O) V]
  [IsScalarTower O (KK O) V]

theorem span_denominator (M : Submodule O V) (y : V) (hy : y ∈ Submodule.span (KK O) (M : Set V)) :
    ∃ s : O, s ≠ 0 ∧ s • y ∈ M := by
  first | exact Bl.general_b_fact_left_bis_form.goal1 .. | (apply Bl.general_b_fact_left_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_bis_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_bis_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_bis_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_bis_form.goal1 <;> first | assumption | infer_instance)

def toSpan (M : Submodule O V) : M →ₗ[O] (Submodule.span (KK O) (M : Set V)) where
  toFun x := ⟨x.1, Submodule.subset_span x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance toSpan_loc (M : Submodule O V) : IsLocalizedModule (nonZeroDivisors O) (toSpan M) := by
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro x
    have hx0 : (x : O) ≠ 0 := nonZeroDivisors.ne_zero x.2
    have hxK : algebraMap O (KK O) x ≠ 0 :=
      (map_ne_zero_iff (algebraMap O (KK O)) (IsFractionRing.injective O (KK O))).2 hx0
    rw [Module.End.isUnit_iff]
    constructor
    · intro y z hyz
      simp only [Module.algebraMap_end_apply] at hyz
      rw [← algebraMap_smul (KK O) (x : O) y, ← algebraMap_smul (KK O) (x : O) z] at hyz
      exact smul_right_injective _ hxK hyz
    · intro y
      refine ⟨(algebraMap O (KK O) x)⁻¹ • y, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul (KK O) (x : O), smul_smul, mul_inv_cancel₀ hxK, one_smul]
  · intro y
    obtain ⟨s, hs, hsy⟩ := span_denominator M y.1 y.2
    exact ⟨(⟨s • y.1, hsy⟩, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), rfl⟩
  · intro x₁ x₂ h
    refine ⟨1, ?_⟩
    have : x₁ = x₂ := Subtype.ext (congrArg (fun z : Submodule.span (KK O) (M : Set V) => (z : V)) h)
    rw [this]

theorem rank_eq_rank_span (M : Submodule O V) :
    Module.rank O M = Module.rank (KK O) (Submodule.span (KK O) (M : Set V)) := by
  rw [IsLocalization.rank_eq (KK O) (nonZeroDivisors O) le_rfl]
  exact (IsLocalizedModule.rank_eq (nonZeroDivisors O) le_rfl (toSpan M)).symm

theorem finrank_eq_finrank_span (M : Submodule O V) :
    Module.finrank O M = Module.finrank (KK O) (Submodule.span (KK O) (M : Set V)) := by
  unfold Module.finrank
  rw [rank_eq_rank_span]

end RankSpan

section Absorb

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}

theorem intPol_le_bbSpec (hV : ValuationProperties p O) (σ : Type) (sp : ℕ) : IntPol O σ ≤ bbSpec O p σ sp := by
  intro F hF
  rw [mem_integral_poly_iff_coeff] at hF
  rw [F.as_sum]
  refine Submodule.sum_mem _ fun m _ => Submodule.subset_span ⟨m, F.coeff m, ?_, rfl⟩
  have h1 : (0 : WithTop ℚ) ≤ vK p (F.coeff m) := (hV.2.2.2.2.2 _).2 (hF m)
  have h2 : (0 : WithTop ℚ) ≤
      (((padicValNat p (expFact m) : ℚ) / 2 + (padicValNat p sp : ℚ) / 2 : ℚ) : WithTop ℚ) := by
    have : (0 : ℚ) ≤ (padicValNat p (expFact m) : ℚ) / 2 + (padicValNat p sp : ℚ) / 2 := by positivity
    exact_mod_cast this
  exact add_nonneg h1 h2

theorem exists_smul_mem_intPol {σ : Type} (F : MvPolynomial σ (KK O)) : ∃ d : O, d ≠ 0 ∧ d • F ∈ IntPol O σ := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) (F.support.image F.coeff)
  refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
  rw [mem_integral_poly_iff_coeff]
  intro m
  by_cases hm : m ∈ F.support
  · obtain ⟨o, ho⟩ := hb (F.coeff m) (Finset.mem_image_of_mem _ hm)
    refine ⟨o, ?_⟩
    rw [MvPolynomial.coeff_smul, ho]
  · refine ⟨0, ?_⟩
    rw [MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.1 hm, smul_zero, map_zero]

theorem span_inf_bbSpec (hV : ValuationProperties p O) {σ : Type} (sp : ℕ) (W : Submodule (KK O) (MvPolynomial σ (KK O))) :
    Submodule.span (KK O) ((W.restrictScalars O ⊓ bbSpec O p σ sp : Submodule O (MvPolynomial σ (KK O))) :
      Set (MvPolynomial σ (KK O))) = W := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun x hx => hx.1
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem_intPol (O := O) x
    have hdK : algebraMap O (KK O) d ≠ 0 :=
      (map_ne_zero_iff (algebraMap O (KK O)) (IsFractionRing.injective O (KK O))).2 hd
    have h1 : d • x ∈ (W.restrictScalars O ⊓ bbSpec O p σ sp : Submodule O (MvPolynomial σ (KK O))) := by
      refine ⟨?_, intPol_le_bbSpec hV σ sp hdx⟩
      show d • x ∈ W
      rw [← algebraMap_smul (KK O) d x]
      exact W.smul_mem _ hx
    have h2 : x = (algebraMap O (KK O) d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul (KK O) d x, smul_smul, inv_mul_cancel₀ hdK, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end Absorb

theorem finrank_blockLat {s : ℕ} (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r]
    (hV : ValuationProperties p O) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) :
    Module.finrank O (blockLat O p r S aTop aPlus m b) = blockRank O p r S aTop aPlus m b := by
  rw [finrank_eq_finrank_span]
  unfold blockLat blockRank
  simp only
  rw [span_inf_bbSpec hV]

theorem restRk_proved (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestRk C0 CE1 CE2 X :=
  fun aTop _ aPlus _ b _ =>
    finrank_blockLat X.O X.p X.r (valuation_properties_hold X.std.1.prime X.setting) (X.S C0 CE1 CE2) aTop aPlus X.m b

section FinDim

variable {O : Type} [CommRing O] [IsDomain O] {N r : ℕ}

theorem totalDegree_pol_le {K : Type} [CommSemiring K] (d : Fin N → ℕ) (y : MvPolynomial (Fin N × Fin r) K)
    (hy : y ∈ Pol K r d) : y.totalDegree ≤ ∑ a, d a := by
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => ?_
  have h1 : ∀ i, multideg m i = d i := (MvPolynomial.mem_restrictSupport_iff K).1 hy (by simpa using hm)
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
  exact le_of_eq (Finset.sum_congr rfl fun i _ => h1 i)

theorem totalDegree_xi_le (t b : ℕ) (g : MvPolynomial (BVar N r t) (KK O)) (hg : g ∈ XiPolZ O N r t b) :
    g.totalDegree ≤ b := by
  classical
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => ?_
  obtain ⟨h1, h2⟩ := (MvPolynomial.mem_restrictSupport_iff (KK O)).1 hg.1 (by simpa using hm)
  rw [← h2]
  unfold Finsupp.sum
  have hinj : Function.Injective (xiVar N r t) := by
    intro c c' h
    unfold xiVar at h
    simpa using h
  calc ∑ v ∈ m.support, m v ≤ ∑ v ∈ Finset.univ.image (xiVar N r t), m v := by
        refine Finset.sum_le_sum_of_subset fun v hv => ?_
        obtain ⟨c, rfl⟩ := h1 v hv
        exact Finset.mem_image_of_mem _ (Finset.mem_univ c)
    _ = ∑ c, m (xiVar N r t c) := Finset.sum_image fun a _ b _ h => hinj h

theorem totalDegree_XX_le {K σ : Type} [CommSemiring K] (u v : σ) :
    (X u * X v : MvPolynomial σ K).totalDegree ≤ 2 := by
  rcases subsingleton_or_nontrivial K with h | h
  · have : (X u * X v : MvPolynomial σ K) = 0 := Subsingleton.elim _ _
    rw [this]; simp
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]

theorem totalDegree_pair_le {K σ ι : Type} [CommSemiring K] [Fintype ι] (u v : σ) (f g : ι → σ) :
    (X u * X v + ∑ c, X (f c) * X (g c) : MvPolynomial σ K).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (totalDegree_XX_le u v) ?_)
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => totalDegree_XX_le _ _)

theorem totalDegree_Xpow_le {K σ : Type} [CommSemiring K] (u : σ) (n : ℕ) :
    (X u ^ n : MvPolynomial σ K).totalDegree ≤ n := by
  rcases subsingleton_or_nontrivial K with h | h
  · have : (X u ^ n : MvPolynomial σ K) = 0 := Subsingleton.elim _ _
    rw [this]; simp
  · refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, mul_one]

def degBound (D : BlockData N) : ℕ :=
  (∑ i, D.LL.deg (D.letterAt (D.T.pos i)) * 2) + D.B * 2 + (∑ i, D.T.z i) + D.zPlus + (∑ a, D.LL.deg a) + D.B

theorem lettersAt_deg_le (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) (a : Fin N) :
    (D.lettersAt j jp).deg a ≤ D.LL.deg a := by
  unfold BlockData.lettersAt
  exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)

theorem gens_totalDegree_le [NeZero r] (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) (hl : D.LevelOK j jp)
    (x : MvPolynomial (BVar N r D.T.t) (KK O)) (hx : x ∈ D.gens O (r := r) j jp) : x.totalDegree ≤ degBound D := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  have hy1 : y ∈ Pol (KK O) r (D.lettersAt j jp).deg := hy.1.1
  have h1 : (∏ i, D.Ehat O (r := r) i ^ j i).totalDegree ≤ ∑ i, D.LL.deg (D.letterAt (D.T.pos i)) * 2 := by
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    exact Nat.mul_le_mul (hl.1 i).1 (totalDegree_pair_le _ _ _ _)
  have h2 : (D.Eplus O (r := r) ^ jp).totalDegree ≤ D.B * 2 := by
    refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    exact Nat.mul_le_mul (hl.2.trans (min_le_right _ _)) (totalDegree_pair_le _ _ _ _)
  have h3 : (∏ i, (X (scalZ N r D.T.t (Fin.castSucc i)) : MvPolynomial (BVar N r D.T.t) (KK O)) ^ D.T.z i).totalDegree ≤
      ∑ i, D.T.z i :=
    (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => totalDegree_Xpow_le _ _)
  have h4 : ((X (scalZ N r D.T.t (Fin.last D.T.t)) : MvPolynomial (BVar N r D.T.t) (KK O)) ^ D.zPlus).totalDegree ≤
      D.zPlus := totalDegree_Xpow_le _ _
  have h5 : (rename (chainEmb N r D.T.t) y).totalDegree ≤ ∑ a, D.LL.deg a :=
    (MvPolynomial.totalDegree_rename_le _ _).trans ((totalDegree_pol_le _ y hy1).trans
      (Finset.sum_le_sum fun a _ => lettersAt_deg_le D j jp a))
  have h6 : g.totalDegree ≤ D.B := (totalDegree_xi_le _ _ g hg).trans (Nat.sub_le _ _)
  unfold degBound
  refine (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ?_ h6)
  refine (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ?_ h5)
  refine (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ?_ h4)
  refine (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ?_ h3)
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add h1 h2)

theorem span_SSZ_le [NeZero r] (D : BlockData N) :
    Submodule.span (KK O) ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
      Set (MvPolynomial (BVar N r D.T.t) (KK O))) ≤
      MvPolynomial.restrictTotalDegree (BVar N r D.T.t) (KK O) (degBound D) := by
  refine Submodule.span_le.2 ?_
  have : D.SSZ O (r := r) ≤
      (MvPolynomial.restrictTotalDegree (BVar N r D.T.t) (KK O) (degBound D)).restrictScalars O := by
    unfold BlockData.SSZ
    refine Submodule.span_le.2 ?_
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, hl, hx⟩ := hx
    exact (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (gens_totalDegree_le D j jp hl x hx)
  exact this

theorem span_SSZ_finite [NeZero r] (D : BlockData N) :
    FiniteDimensional (KK O) (Submodule.span (KK O)
      ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
        Set (MvPolynomial (BVar N r D.T.t) (KK O)))) :=
  Submodule.finiteDimensional_of_le (span_SSZ_le D)

end FinDim

theorem counting_statement_of_digit_class_rank (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C : ℝ) (hCYb : 1 ≤ CYb) (hC : 1 ≤ C)
    (h : ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X →
      SegmentWeightedCountingBound C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X) :
    IntegralityFromMetric D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C :=
  counting_statement_of_digit_class_form D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C hCYb hC fun X hA => ⟨restRk_proved C0 CE1 CE2 X, h X hA⟩

end Formalism.MainNotions.G.CountingStatementReduction

namespace Formalism.MainNotions.G.CountingStatementReduction

open Formalism.MainNotions.flipOneThree Formalism.MainNotions.G Finset

theorem thr_mono_ge {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cc, 1 ≤ CYb →
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cc → Q C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : TransportedAlt P) : TransportedAlt Q := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hP Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 a1 a2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 a1 a2
  refine ⟨max T2 1, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => ?_⟩
  exact h _ _ _ _ _ _ _ _ _ ((le_max_right _ _).trans b1)
    (h2 CYb Cde Ck CD Cb ((le_max_left _ _).trans b1) ((le_max_left _ _).trans b2) ((le_max_left _ _).trans b3)
      ((le_max_left _ _).trans b4) ((le_max_left _ _).trans b5))

def DigitClassRemaining (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C : ℝ) : Prop :=
  ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X →
    SegmentWeightedCountingBound C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X

def DigitClassRemainingUniform (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ C : ℝ, 1 ≤ C ∧
    DigitClassRemaining D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C

theorem counting_statement_uniform_of_digit_class (D : Formalism.BasicNotions.D7) (h : DigitClassRemainingUniform D) : IntegralityFromMetricForLargeConstants D :=
  thr_mono_ge (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hY h1 Ckap Cs => by
    obtain ⟨C, hC, h2⟩ := h1 Ckap Cs
    exact ⟨C, zero_lt_one.trans_le hC, counting_statement_of_digit_class_rank D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C hY hC h2⟩) h

end Formalism.MainNotions.G.CountingStatementReduction

end
