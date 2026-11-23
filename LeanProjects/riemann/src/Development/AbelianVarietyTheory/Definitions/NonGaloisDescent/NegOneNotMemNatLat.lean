import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.RSJ.Model

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def eLast (R : Type*) [CommRing R] (a : ℕ) : Fin a → R := fun i => if (i : ℕ) + 1 = a then 1 else 0

theorem secRow_eLast {R : Type*} [CommRing R] : secRow (eLast R a) = 1 := by
  ext i j
  simp only [secRow, eLast, Matrix.of_apply, Matrix.one_apply]
  by_cases h : (i : ℕ) + 1 = a
  · rw [if_pos h]
    by_cases h2 : (j : ℕ) + 1 = a
    · rw [if_pos h2, if_pos (Fin.ext (by omega))]
    · rw [if_neg h2, if_neg (fun e : i = j => h2 (e ▸ h))]
  · rw [if_neg h]

theorem secRow_eq_updateRow {R : Type*} [CommRing R] {n : ℕ} (y : Fin (n + 1) → R) :
    secRow y = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).updateRow (Fin.last n) y := by
  ext i j
  simp only [secRow, Matrix.of_apply, Matrix.updateRow_apply]
  by_cases h : i = Fin.last n
  · subst h; simp
  · rw [if_neg h, if_neg (fun e => h (Fin.ext (by simpa using e)))]

theorem det_secRow {R : Type*} [CommRing R] {n : ℕ} (y : Fin (n + 1) → R) : (secRow y).det = y (Fin.last n) := by
  rw [secRow_eq_updateRow, ← Matrix.cramer_transpose_apply]
  simp

theorem eLast_vecMul_secRow {R : Type*} [CommRing R] {n : ℕ} (y : Fin (n + 1) → R) :
    Matrix.vecMul (eLast R (n + 1)) (secRow y) = y := by
  funext j
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp [eLast, secRow]
  · intro b _ hb
    have : ¬ ((b : ℕ) + 1 = n + 1) := fun e => hb (Fin.ext (by simpa using e))
    simp only [eLast, if_neg this, zero_mul]
  · simp

omit [NumberField E] [IsTotallyComplex E] in

theorem secRow_mul_secInv {n : ℕ} (y : Fin (n + 1) → Cinf E) (hy : ∀ w, y (Fin.last n) w ≠ 0) :
    secRow y * (secInv y : Matrix (Fin (n + 1)) (Fin (n + 1)) (Cinf E)) = 1 := by
  have h : IsUnit (secRow y).det := by
    rw [det_secRow]; exact Pi.isUnit_iff.2 fun w => (hy w).isUnit
  rw [secInv, dif_pos h]
  exact (Matrix.nonsingInvUnit (secRow y) h).mul_inv

omit [NumberField E] [IsTotallyComplex E] in

theorem vecMul_secInv {n : ℕ} (y : Fin (n + 1) → Cinf E) (hy : ∀ w, y (Fin.last n) w ≠ 0) :
    Matrix.vecMul y (secInv y : Matrix (Fin (n + 1)) (Fin (n + 1)) (Cinf E)) = eLast (Cinf E) (n + 1) := by
  conv_lhs => rw [← eLast_vecMul_secRow y]
  rw [eLast_vecMul_secRow y]
  conv_lhs => congr; rw [← eLast_vecMul_secRow y]
  rw [Matrix.vecMul_vecMul, secRow_mul_secInv y hy, Matrix.vecMul_one]

omit [NumberField E] [IsTotallyComplex E] in
theorem secInv_eLast : secInv (eLast (Cinf E) a) = 1 := by
  unfold secInv
  split_ifs with h
  · rw [inv_eq_one]; exact Units.ext secRow_eLast
  · rfl

omit [IsTotallyComplex E] in
theorem rowAct_ratGL_mul (ξ : Fin a → E) (γ : GL (Fin a) E) (g : GA E a) :
    rowAct ξ (ratGL E a γ * g) = rowAct (Matrix.vecMul ξ (γ : Matrix (Fin a) (Fin a) E)) g := by
  unfold rowAct
  rw [Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  funext j
  simp [Matrix.vecMul, dotProduct, ratGL]

omit [IsTotallyComplex E] in
theorem detPow_mul (x : ℝ) (g h : GA E a) : detPow E a x (g * h) = detPow E a x g * detPow E a x h := by
  simp [detPow]

omit [IsTotallyComplex E] in
theorem detPow_pos (x : ℝ) (g : GA E a) : 0 < detPow E a x g := by
  simp [detPow]

omit [IsTotallyComplex E] in

theorem detPow_ratGL (x : ℝ) (γ : GL (Fin a) E) : detPow E a x (ratGL E a γ) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (ratGL E a γ) = diagUnits E (Matrix.GeneralLinearGroup.det γ) :=
    Units.ext (det_map (algebraMap E (Ad E)) γ)
  have h2 := (GlobalTheory.HeckeGal.Model.absPow E x).2.2 (Matrix.GeneralLinearGroup.det γ)
  unfold detPow chiDet
  rw [MonoidHom.comp_apply, h, h2]; simp

omit [IsTotallyComplex E] in

theorem norm_absPow_val (x : ℝ) (v : HeightOneSpectrum (𝓞 E)) :
    (((GlobalTheory.HeckeGal.Model.absPow E x).val v : ℂˣ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ (-(x : ℂ)) :=
  (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E x).2.1 v

theorem thetaSum_ratGL_mul (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ)
    (hφ : ∀ γ g, φ (ratGL E a γ * g) = φ g) (hφ' : ∀ γ g, φ' (ratGL E a γ * g) = φ' g)
    (γ : GL (Fin a) E) (g : GA E a) : thetaSum φ φ' Φ N (ratGL E a γ * g) = thetaSum φ φ' Φ N g := by
  let e : {ξ : Fin a → E // ξ ≠ 0} ≃ {ξ : Fin a → E // ξ ≠ 0} :=
    { toFun := fun ξ => ⟨Matrix.vecMul ξ.1 (γ : Matrix (Fin a) (Fin a) E), fun h => ξ.2 (by
        have := congrArg (fun u => Matrix.vecMul u ((γ⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) h
        simpa [Matrix.vecMul_vecMul] using this)⟩
      invFun := fun ξ => ⟨Matrix.vecMul ξ.1 ((γ⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E), fun h => ξ.2 (by
        have := congrArg (fun u => Matrix.vecMul u (γ : Matrix (Fin a) (Fin a) E)) h
        simpa [Matrix.vecMul_vecMul] using this)⟩
      left_inv := fun ξ => Subtype.ext (by simp [Matrix.vecMul_vecMul])
      right_inv := fun ξ => Subtype.ext (by simp [Matrix.vecMul_vecMul]) }
  unfold thetaSum
  rw [← e.tsum_eq fun ξ => Psi φ φ' Φ N g (rowAct ξ.1 g)]
  refine tsum_congr fun ξ => ?_
  rw [rowAct_ratGL_mul]
  simp only [Psi, mul_assoc, hφ, hφ']
  rfl

omit [IsTotallyComplex E] in
theorem indN_eLast (N : ℕ) : indN N (eLast (Af E) a) = 1 := by
  unfold indN
  rw [if_pos]
  intro i
  exact ⟨0, fun v => zero_mem _, by simp [eLast]⟩

omit [IsTotallyComplex E] in

theorem neg_one_notMem_natLat (N : ℕ) (v : HeightOneSpectrum (𝓞 E)) (hv : (N : 𝓞 E) ∈ v.asIdeal) :
    (-1 : Af E) ∉ natLat E N := by
  rintro ⟨z, hz, h⟩
  have h1 := congrArg (fun t => Valued.v (pLoc E v t)) h
  simp only [map_neg, map_one, map_mul, map_natCast, Valuation.map_neg] at h1
  have h2 : Valued.v (pLoc E v z) ≤ 1 := hz v
  have h3 : Valued.v (N : v.adicCompletion E) < 1 := by
    have : (N : v.adicCompletion E) = algebraMap E _ (algebraMap (𝓞 E) E (N : 𝓞 E)) := by simp
    rw [this]
    change Valued.v ((algebraMap (𝓞 E) E (N : 𝓞 E) : E) : v.adicCompletion E) < 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hv
  exact absurd h1 (ne_of_gt (mul_lt_one_of_lt_of_le h3 h2))

omit [IsTotallyComplex E] in
theorem indN_zero {n : ℕ} (N : ℕ) (v : HeightOneSpectrum (𝓞 E)) (hv : (N : 𝓞 E) ∈ v.asIdeal) :
    indN N (0 : Fin (n + 1) → Af E) = 0 := by
  unfold indN
  rw [if_neg]
  intro h
  have := h (Fin.last n)
  simp only [Fin.val_last, if_true, Pi.zero_apply, zero_sub] at this
  exact neg_one_notMem_natLat N v hv this

theorem pInf_rowAct_one (ξ : Fin a → E) (i : Fin a) (w : InfinitePlace E) :
    pInf E (rowAct ξ 1 i) w = w.embedding (ξ i) := by
  simp [rowAct, pInf_algebraMap]

open Classical in

theorem thetaSum_point {n : ℕ} (φ φ' : GA E (n + 1) → ℂ) (N : ℕ) :
    thetaSum φ φ' (fun y => if y = eLast (Cinf E) (n + 1) then 1 else 0) N 1 = φ 1 * starRingEnd ℂ (φ' 1) := by
  have h0 : eLast E (n + 1) ≠ 0 := fun h => by simpa [eLast] using congrFun h (Fin.last n)
  unfold thetaSum
  rw [tsum_eq_single ⟨eLast E (n + 1), h0⟩]
  · have h1 : (fun i => pInf E (rowAct (eLast E (n + 1)) (1 : GA E (n + 1)) i)) = eLast (Cinf E) (n + 1) := by
      funext i; simp only [rowAct, eLast, Units.val_one, Matrix.vecMul_one, apply_ite, map_one, map_zero]; split_ifs <;> rfl
    have h2 : (fun i => GlobalTheory.RSJ.pFin E (rowAct (eLast E (n + 1)) (1 : GA E (n + 1)) i)) = eLast (Af E) (n + 1) := by
      funext i; simp only [rowAct, eLast, Units.val_one, Matrix.vecMul_one, apply_ite, map_one, map_zero]; split_ifs <;> rfl
    simp only [Psi, h1, h2, secInv_eLast, indN_eLast]; simp
  · intro ξ hξ
    have : (fun i => pInf E (rowAct ξ.1 (1 : GA E (n + 1)) i)) ≠ eLast (Cinf E) (n + 1) := by
      intro h
      apply hξ
      refine Subtype.ext (funext fun i => ?_)
      obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
      have := congrFun (congrFun h i) w
      rw [pInf_rowAct_one] at this
      apply w.embedding.injective
      rw [this]; simp only [eLast]; split_ifs <;> simp
    simp only [Psi, if_neg this]; simp

open Classical in

theorem zint_dirac {n : ℕ} (φ φ' : GA E (n + 1) → ℂ) (N : ℕ) (x : ℝ) :
    Zint (Measure.dirac 1) Set.univ φ φ' (fun y => if y = eLast (Cinf E) (n + 1) then 1 else 0) N x
      = φ 1 * starRingEnd ℂ (φ' 1) := by
  haveI : T2Space (Af E) := inferInstanceAs (T2Space (RestrictedProduct _ _ _))
  haveI : T2Space (InfiniteAdeleRing E) := inferInstanceAs (T2Space (∀ w : InfinitePlace E, w.Completion))
  haveI : T2Space (Ad E) := inferInstanceAs (T2Space (InfiniteAdeleRing E × Af E))
  haveI : T2Space (GA E (n + 1)) := Units.isEmbedding_embedProduct.t2Space
  unfold Zint
  rw [Measure.restrict_univ, integral_dirac, thetaSum_point]
  simp [detPow]

omit [IsTotallyComplex E] in
theorem pFin_eq : GlobalTheory.RSJ.pFin E = GlobalTheory.CuspRep.pFin E := rfl

end GlobalTheory.RSJ.Model
