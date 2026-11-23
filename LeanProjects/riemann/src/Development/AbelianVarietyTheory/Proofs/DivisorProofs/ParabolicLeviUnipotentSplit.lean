import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviTorusElementCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDualGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.StabLineLevi

open Matrix

section Ring

variable {R : Type} [CommRing R] (c : R →+* R) {d k : ℕ}

theorem map_mulVec_conj (M : Matrix (Fin d) (Fin k) R) (v : Fin k → R) :
    M.map c *ᵥ (fun i => c (v i)) = fun i => c ((M *ᵥ v) i) := by
  funext i; simp [mulVec, dotProduct, map_sum, map_mul]

theorem map_vecMulVec' (a : Fin d → R) (b : Fin k → R) :
    (vecMulVec a b).map c = vecMulVec (fun i => c (a i)) (fun i => c (b i)) := by
  ext i j; simp [vecMulVec]

theorem vmv_zero_right (a : Fin d → R) : vecMulVec a (0 : Fin k → R) = 0 := by ext; simp [vecMulVec]

theorem vmv_zero_left (b : Fin k → R) : vecMulVec (0 : Fin d → R) b = 0 := by ext; simp [vecMulVec]

theorem vmv_mulVec (u : Fin d → R) (v w : Fin k → R) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  funext i; simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

variable {c}
variable {J : Matrix (Fin d) (Fin d) R} {ι : Matrix (Fin d) (Fin k) R} {π : Matrix (Fin k) (Fin d) R} {x y : Fin d → R}

theorem transpose_mulVec_fix {Q : Matrix (Fin d) (Fin d) R} (hQ : Qᵀ * J * Q.map c = J) (hQx : Q *ᵥ x = x) :
    Qᵀ *ᵥ (J *ᵥ fun i => c (x i)) = J *ᵥ fun i => c (x i) := by
  conv_rhs => rw [← hQ]
  rw [← mulVec_mulVec, ← mulVec_mulVec, map_mulVec_conj, hQx]

variable (hD : vecMulVec x (J *ᵥ fun i => c (y i)) + ι * π - vecMulVec y (J *ᵥ fun i => c (x i)) = 1)
include hD

theorem iota_pi : ι * π = 1 - vecMulVec x (J *ᵥ fun i => c (y i)) + vecMulVec y (J *ᵥ fun i => c (x i)) := by
  rw [← hD]; abel

theorem mul_iota {Q : Matrix (Fin d) (Fin d) R} (hQ : Qᵀ * J * Q.map c = J) (hQx : Q *ᵥ x = x)
    (hιx : ιᵀ *ᵥ (J *ᵥ fun i => c (x i)) = 0) :
    Q * ι = vecMulVec x ((J *ᵥ fun i => c (y i)) ᵥ* (Q * ι)) + ι * (π * Q * ι) := by
  have hq : (J *ᵥ fun i => c (x i)) ᵥ* Q = J *ᵥ fun i => c (x i) := by
    rw [← mulVec_transpose]; exact transpose_mulVec_fix hQ hQx
  have hw : (J *ᵥ fun i => c (x i)) ᵥ* (Q * ι) = 0 := by
    rw [← vecMul_vecMul, hq, ← mulVec_transpose, hιx]
  calc Q * ι = (vecMulVec x (J *ᵥ fun i => c (y i)) + ι * π - vecMulVec y (J *ᵥ fun i => c (x i))) * (Q * ι) := by
        rw [hD, Matrix.one_mul]
    _ = _ := by
        rw [Matrix.sub_mul, Matrix.add_mul, vecMulVec_mul, vecMulVec_mul, hw, vmv_zero_right, sub_zero]
        simp only [Matrix.mul_assoc]

theorem proj_x (hπι : π * ι = 1) (hxx : x ⬝ᵥ (J *ᵥ fun i => c (x i)) = 0)
    (hxy : x ⬝ᵥ (J *ᵥ fun i => c (y i)) = 1) : π *ᵥ x = 0 := by
  have h : ι *ᵥ (π *ᵥ x) = 0 := by
    rw [mulVec_mulVec, iota_pi hD, add_mulVec, sub_mulVec, one_mulVec, vecMulVec_mulVec, vecMulVec_mulVec,
      dotProduct_comm, hxy, dotProduct_comm, hxx]
    simp
  rw [← Matrix.one_mulVec (π *ᵥ x), ← hπι, ← mulVec_mulVec, h, mulVec_zero]

theorem proj_y (hπι : π * ι = 1) (hyy : y ⬝ᵥ (J *ᵥ fun i => c (y i)) = 0)
    (hyx : y ⬝ᵥ (J *ᵥ fun i => c (x i)) = -1) : π *ᵥ y = 0 := by
  have h : ι *ᵥ (π *ᵥ y) = 0 := by
    rw [mulVec_mulVec, iota_pi hD, add_mulVec, sub_mulVec, one_mulVec, vecMulVec_mulVec, vecMulVec_mulVec,
      dotProduct_comm, hyy, dotProduct_comm, hyx]
    simp
  rw [← Matrix.one_mulVec (π *ᵥ y), ← hπι, ← mulVec_mulVec, h, mulVec_zero]

theorem gram_left (hxι : x ᵥ* (J * ι.map c) = 0) (hyι : y ᵥ* (J * ι.map c) = 0) :
    J * ι.map c = πᵀ * (ιᵀ * J * ι.map c) := by
  have : πᵀ * (ιᵀ * J * ι.map c) = (ι * π)ᵀ * (J * ι.map c) := by
    rw [transpose_mul]; simp only [Matrix.mul_assoc]
  rw [this, iota_pi hD, transpose_add, transpose_sub, transpose_one, transpose_vecMulVec, transpose_vecMulVec,
    Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, vecMulVec_mul, vecMulVec_mul, hxι, hyι, vmv_zero_right,
    vmv_zero_right, sub_zero, add_zero]

theorem gram_right (hιx : ιᵀ *ᵥ (J *ᵥ fun i => c (x i)) = 0)
    (hιy : ιᵀ *ᵥ (J *ᵥ fun i => c (y i)) = 0) :
    ιᵀ * J = (ιᵀ * J * ι.map c) * π.map c := by
  have e : (ι * π).map c = ι.map c * π.map c := Matrix.map_mul
  rw [Matrix.mul_assoc, ← e, iota_pi hD, Matrix.map_add _ (map_add c), Matrix.map_sub _ (map_sub c),
    Matrix.map_one _ (map_zero c) (map_one c), map_vecMulVec', map_vecMulVec', Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_one, mul_vecMulVec, mul_vecMulVec, ← mulVec_mulVec, ← mulVec_mulVec, hιx, hιy, vmv_zero_left,
    vmv_zero_left, sub_zero, add_zero]

theorem unitary_compress {Q : Matrix (Fin d) (Fin d) R} (hQ : Qᵀ * J * Q.map c = J) (hQx : Q *ᵥ x = x)
    (hιx : ιᵀ *ᵥ (J *ᵥ fun i => c (x i)) = 0) (hxι : x ᵥ* (J * ι.map c) = 0)
    (hxx : x ⬝ᵥ (J *ᵥ fun i => c (x i)) = 0) :
    (π * Q * ι)ᵀ * (ιᵀ * J * ι.map c) * (π * Q * ι).map c = ιᵀ * J * ι.map c := by
  set b := (J *ᵥ fun i => c (y i)) ᵥ* (Q * ι) with hb
  have hA : ι * (π * Q * ι) = Q * ι - vecMulVec x b := by
    rw [mul_iota hD hQ hQx hιx]; abel
  have e1 : (π * Q * ι)ᵀ * (ιᵀ * J * ι.map c) * (π * Q * ι).map c =
      (ι * (π * Q * ι))ᵀ * J * (ι * (π * Q * ι)).map c := by
    simp only [transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
  have hJx : x ᵥ* (J * Q.map c) = x ᵥ* J := by
    conv_lhs => rw [← hQx, ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc, hQ]
  have T1 : (Q * ι)ᵀ * J * (Q * ι).map c = ιᵀ * J * ι.map c := by
    rw [transpose_mul, Matrix.map_mul]
    calc _ = ιᵀ * (Qᵀ * J * Q.map c) * ι.map c := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ]
  have T2 : (Q * ι)ᵀ * J * (vecMulVec x b).map c = 0 := by
    rw [map_vecMulVec', mul_vecMulVec, ← mulVec_mulVec, transpose_mul, ← mulVec_mulVec,
      transpose_mulVec_fix hQ hQx, hιx, vmv_zero_left]
  have T3 : (vecMulVec x b)ᵀ * J * (Q * ι).map c = 0 := by
    rw [transpose_vecMulVec, vecMulVec_mul, vecMulVec_mul, Matrix.map_mul, ← vecMul_vecMul,
      vecMul_vecMul x J, hJx, vecMul_vecMul, hxι, vmv_zero_right]
  have T4 : (vecMulVec x b)ᵀ * J * (vecMulVec x b).map c = 0 := by
    rw [transpose_vecMulVec, vecMulVec_mul, map_vecMulVec', vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, hxx, zero_smul, vmv_zero_right]
  rw [e1, hA, transpose_sub, Matrix.map_sub _ (map_sub c), Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub, T1, T2, T3, T4]
  simp

omit hD in
theorem isUnit_det_of_unitary {A J₁ : Matrix (Fin k) (Fin k) R} (h : Aᵀ * J₁ * A.map c = J₁) (hJ : IsUnit J₁.det) :
    IsUnit A.det := by
  have h1 := congrArg det h
  have e : (A.map c).det = c A.det := (RingHom.map_det c A).symm
  rw [det_mul, det_mul, det_transpose, e] at h1
  obtain ⟨u, hu⟩ := hJ
  have h2 : (A.det * c A.det) * (u : R) = 1 * u := by rw [hu]; linear_combination h1
  have h3 : A.det * c A.det = 1 := (Units.mul_left_inj u).mp h2
  exact ⟨⟨A.det, c A.det, h3, by rw [mul_comm]; exact h3⟩, rfl⟩

end Ring
section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a b : UA σ J) : mat (a * b) = mat a * mat b := rfl

theorem mat_inv_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a : UA σ J) : mat a⁻¹ * mat a = 1 := Units.inv_mul a.1

theorem mat_mul_inv' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a : UA σ J) : mat a * mat a⁻¹ = 1 := Units.mul_inv a.1

theorem mulVec_inv_of_eigen {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a : UA σ J) (v : Fin n → AE F E) (s : (AE F E)ˣ)
    (h : mat a *ᵥ v = s.1 • v) : mat a⁻¹ *ᵥ v = (s⁻¹).1 • v := by
  have h1 : s.1 • (mat a⁻¹ *ᵥ v) = v := by
    rw [← mulVec_smul, ← h, mulVec_mulVec, mat_inv_mul', one_mulVec]
  calc mat a⁻¹ *ᵥ v = ((s⁻¹).1 * s.1) • (mat a⁻¹ *ᵥ v) := by rw [Units.inv_mul, one_smul]
    _ = (s⁻¹).1 • v := by rw [mul_smul, h1]

theorem cv_incV {n : ℕ} (v : Fin n → E) :
    (fun i => (cA σ).toRingHom (incV F v i)) = incV F (fun i => σ (v i)) :=
  funext fun i => GlobalTheory.LeviPlane.cAr_inclR σ (v i)

theorem incM_vecMulVec {m n : ℕ} (a : Fin m → E) (b : Fin n → E) :
    incM F (vecMulVec a b) = vecMulVec (incV F a) (incV F b) := by
  ext i j; simp [incM, incV, vecMulVec]

theorem incV_vecMul {m n : ℕ} (a : Fin m → E) (M : Matrix (Fin m) (Fin n) E) :
    incV F a ᵥ* incM F M = incV F (a ᵥ* M) := by
  funext j; simp [incM, incV, vecMul, dotProduct, map_sum, map_mul]

theorem incM_transpose {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) : (incM F M)ᵀ = incM F Mᵀ := rfl

theorem incV_zero {n : ℕ} : incV F (0 : Fin n → E) = 0 := by funext i; simp [incV]

theorem incM_add {m n : ℕ} (A B : Matrix (Fin m) (Fin n) E) : incM F (A + B) = incM F A + incM F B := by
  ext i j; simp [incM]

theorem incM_sub {m n : ℕ} (A B : Matrix (Fin m) (Fin n) E) : incM F (A - B) = incM F A - incM F B := by
  ext i j; simp [incM]

theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j; simp [incM, Matrix.one_apply]

theorem exists_levi_of_proj {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (H' : Plane E d d₁)
    (πa : Matrix (Fin d₁) (Fin d) (AE F E)) (q1 : πa * incM F H'.ι = 1)
    (q2 : incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = πaᵀ * incM F W₁.J)
    (q3 : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * πa.map (cA σ).toRingHom)
    (p4 : πa *ᵥ incV F H'.x = 0) (p5 : πa *ᵥ incV F H'.y = 0) (h₁ : UA σ W₁.J) :
    ∃ m : UA σ W.J, IsLevi H' 1 h₁ m := by
  have hfix : ∀ v, πa *ᵥ v = 0 → (1 + incM F H'.ι * (mat h₁ - 1) * πa) *ᵥ v = v := by
    intro v hv
    rw [add_mulVec, one_mulVec, ← mulVec_mulVec, hv, mulVec_zero, add_zero]
  refine ⟨⟨⟨1 + incM F H'.ι * (mat h₁ - 1) * πa, 1 + incM F H'.ι * ((h₁.1⁻¹).1 - 1) * πa, ?_, ?_⟩, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [GlobalTheory.LeviUnitary.ext_mul q1, mat, Units.mul_inv]; simp
  · rw [GlobalTheory.LeviUnitary.ext_mul q1, mat, Units.inv_mul]; simp
  · exact GlobalTheory.LeviUnitary.ext_unitary (cA σ).toRingHom q1 q2 q3 h₁.2
  · rw [Units.val_one, one_smul]; exact hfix _ p4
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hfix _ p5
  · show (1 + incM F H'.ι * (mat h₁ - 1) * πa) * incM F H'.ι = _
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one,
      add_sub_cancel]

end Adelic

theorem stab_line_eq_unip_mul_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n d₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E d₁) (H' : Plane E n d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ →
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (p : UA σ W.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H'.x = t.1 • incV F H'.x →
    ∃ n ∈ unip σ W H', ∃ m₁ : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m₁ ∧ ∃ (h₁ : UA σ W₁.J) (m₂ : UA σ W.J),
      IsLevi (W₁ := W₁) H' 1 h₁ m₂ ∧ p = n * m₁ * m₂ := by
  intro F E _ _ _ _ _ σ B n d₁ W W₁ H' r s i₀ i₁ hcm hW hH p t hp
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.LeviPlane.sigma_invol hcm
  obtain ⟨π, hπι, hdec, hdet⟩ := GlobalTheory.PlaneFrame.frame_dual_gram F E σ B n W r s d₁ W₁ H' i₀ i₁ hcm hW hH
  obtain ⟨m₁, hm₁x, hm₁y, hm₁ι⟩ := GlobalTheory.ThK.exists_isLevi F E σ B n d₁ W W₁ H' r s i₀ i₁ hcm hW hH t
  have hsk := GlobalTheory.PlaneFrame.form_skew hcm hW.skew

  have eιx : H'.ιᵀ *ᵥ (W.J *ᵥ fun i => σ (H'.x i)) = 0 := by
    funext j
    have h := (hH.orth (Pi.single j 1)).1
    rw [Matrix.mulVec_single_one] at h
    rw [Matrix.mulVec_transpose]
    show (W.J *ᵥ fun i => σ (H'.x i)) ⬝ᵥ (fun i => H'.ι i j) = 0
    rw [dotProduct_comm]; exact h
  have eιy : H'.ιᵀ *ᵥ (W.J *ᵥ fun i => σ (H'.y i)) = 0 := by
    funext j
    have h := (hH.orth (Pi.single j 1)).2
    rw [Matrix.mulVec_single_one] at h
    rw [Matrix.mulVec_transpose]
    show (W.J *ᵥ fun i => σ (H'.y i)) ⬝ᵥ (fun i => H'.ι i j) = 0
    rw [dotProduct_comm]; exact h
  have exι : H'.x ᵥ* (W.J * H'.ι.map σ) = 0 := by
    funext j
    have h := (hH.orth (Pi.single j 1)).1
    rw [Matrix.mulVec_single_one] at h
    rw [← vecMul_vecMul]
    show (H'.x ᵥ* W.J) ⬝ᵥ (fun i => σ (H'.ι i j)) = 0
    rw [← dotProduct_mulVec]
    have h2 := hsk H'.x (H'.ι.col j)
    rw [h, map_zero, neg_zero] at h2
    exact h2
  have eyι : H'.y ᵥ* (W.J * H'.ι.map σ) = 0 := by
    funext j
    have h := (hH.orth (Pi.single j 1)).2
    rw [Matrix.mulVec_single_one] at h
    rw [← vecMul_vecMul]
    show (H'.y ᵥ* W.J) ⬝ᵥ (fun i => σ (H'.ι i j)) = 0
    rw [← dotProduct_mulVec]
    have h2 := hsk H'.y (H'.ι.col j)
    rw [h, map_zero, neg_zero] at h2
    exact h2
  have eyx : form σ W.J H'.y H'.x = -1 := by rw [hsk, hH.xy, map_one]

  have hDa : vecMulVec (incV F H'.x) (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.y i)) +
      incM F H'.ι * incM F π - vecMulVec (incV F H'.y) (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.x i)) = 1 := by
    rw [cv_incV, cv_incV, GlobalTheory.LeviUnitary.incM_mulVec, GlobalTheory.LeviUnitary.incM_mulVec, ← incM_vecMulVec, ← incM_vecMulVec,
      ← GlobalTheory.LeviUnitary.incM_mul, ← incM_add, ← incM_sub, hdec, incM_one]
  have fa : ∀ a b : Fin n → E, incV F a ⬝ᵥ (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F b i)) =
      inclR (F := F) (AF F) (form σ W.J a b) := fun a b => GlobalTheory.LeviPlane.fm_inc σ W.J a b
  have hxxa := fa H'.x H'.x
  rw [hH.xx, map_zero] at hxxa
  have hxya := fa H'.x H'.y
  rw [hH.xy, map_one] at hxya
  have hyya := fa H'.y H'.y
  rw [hH.yy, map_zero] at hyya
  have hyxa := fa H'.y H'.x
  rw [eyx, map_neg, map_one] at hyxa
  have hιxa : (incM F H'.ι)ᵀ *ᵥ (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.x i)) = 0 := by
    rw [cv_incV, GlobalTheory.LeviUnitary.incM_mulVec, incM_transpose, GlobalTheory.LeviUnitary.incM_mulVec, eιx, incV_zero]
  have hιya : (incM F H'.ι)ᵀ *ᵥ (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.y i)) = 0 := by
    rw [cv_incV, GlobalTheory.LeviUnitary.incM_mulVec, incM_transpose, GlobalTheory.LeviUnitary.incM_mulVec, eιy, incV_zero]
  have hxιa : incV F H'.x ᵥ* (incM F W.J * (incM F H'.ι).map (cA σ).toRingHom) = 0 := by
    rw [GlobalTheory.LeviUnitary.incM_conj, ← GlobalTheory.LeviUnitary.incM_mul, incV_vecMul, exι, incV_zero]
  have hyιa : incV F H'.y ᵥ* (incM F W.J * (incM F H'.ι).map (cA σ).toRingHom) = 0 := by
    rw [GlobalTheory.LeviUnitary.incM_conj, ← GlobalTheory.LeviUnitary.incM_mul, incV_vecMul, eyι, incV_zero]
  have hπιa : incM F π * incM F H'.ι = 1 := by rw [← GlobalTheory.LeviUnitary.incM_mul, hπι, incM_one]
  have hgram : (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = incM F W₁.J := by
    rw [GlobalTheory.LeviUnitary.incM_conj, incM_transpose, ← GlobalTheory.LeviUnitary.incM_mul, ← GlobalTheory.LeviUnitary.incM_mul, hH.gram]
  have hdeta : IsUnit (incM F W₁.J).det := by
    have := hdet.map (inclR (F := F) (AF F))
    rwa [RingHom.map_det] at this
  have hQ : (mat (m₁⁻¹ * p))ᵀ * incM F W.J * (mat (m₁⁻¹ * p)).map (cA σ).toRingHom = incM F W.J := (m₁⁻¹ * p).2
  have hm₁inv : mat m₁⁻¹ *ᵥ incV F H'.x = (t⁻¹).1 • incV F H'.x := mulVec_inv_of_eigen m₁ _ t hm₁x
  have hQx : mat (m₁⁻¹ * p) *ᵥ incV F H'.x = incV F H'.x := by
    rw [mat_mul', ← mulVec_mulVec, hp, mulVec_smul, hm₁inv, smul_smul, Units.mul_inv, one_smul]
  have hAu := unitary_compress hDa hQ hQx hιxa hxιa hxxa
  rw [hgram] at hAu
  have hAdet := isUnit_det_of_unitary hAu hdeta
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hAdet
  let h₁ : UA σ W₁.J := ⟨u, by
    show (u : Matrix (Fin d₁) (Fin d₁) (AE F E))ᵀ * incM F W₁.J * (u : Matrix (Fin d₁) (Fin d₁) (AE F E)).map (cA σ) = _
    rw [hu]; exact hAu⟩
  have hh₁ : mat h₁ = incM F π * mat (m₁⁻¹ * p) * incM F H'.ι := hu
  have q2 := gram_left hDa hxιa hyιa
  rw [hgram] at q2
  have q3 := gram_right hDa hιxa hιya
  rw [hgram] at q3
  have p4 := proj_x hDa hπιa hxxa hxya
  have p5 := proj_y hDa hπιa hyya hyxa
  obtain ⟨m₂, hm₂x, hm₂y, hm₂ι⟩ := exists_levi_of_proj H' (incM F π) hπιa q2 q3 p4 p5 h₁
  have hdecQ := mul_iota hDa hQ hQx hιxa
  rw [← hh₁] at hdecQ
  obtain ⟨b, hb⟩ : ∃ b, mat (m₁⁻¹ * p) * incM F H'.ι = vecMulVec (incV F H'.x) b + incM F H'.ι * mat h₁ := ⟨_, hdecQ⟩
  have e4 : mat m₁ * incM F H'.ι = incM F H'.ι := by
    rw [hm₁ι]; exact Matrix.mul_one _
  have e1 : mat m₁⁻¹ * incM F H'.ι = incM F H'.ι := by
    calc mat m₁⁻¹ * incM F H'.ι = mat m₁⁻¹ * (mat m₁ * incM F H'.ι) := by rw [e4]
      _ = incM F H'.ι := by rw [← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]
  have e2 : mat m₂⁻¹ * incM F H'.ι = incM F H'.ι * mat h₁⁻¹ := by
    calc mat m₂⁻¹ * incM F H'.ι = mat m₂⁻¹ * incM F H'.ι * (mat h₁ * mat h₁⁻¹) := by rw [mat_mul_inv', Matrix.mul_one]
      _ = mat m₂⁻¹ * (mat m₂ * incM F H'.ι) * mat h₁⁻¹ := by rw [hm₂ι]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [← Matrix.mul_assoc (mat m₂⁻¹), mat_inv_mul', Matrix.one_mul]
  have e3 : mat p = mat m₁ * mat (m₁⁻¹ * p) := by rw [mat_mul', ← Matrix.mul_assoc, mat_mul_inv', Matrix.one_mul]
  have hm₂inv : mat m₂⁻¹ *ᵥ incV F H'.x = ((1 : (AE F E)ˣ)⁻¹).1 • incV F H'.x := mulVec_inv_of_eigen m₂ _ 1 hm₂x
  rw [inv_one, Units.val_one, one_smul] at hm₂inv
  have hn : mat (p * m₂⁻¹ * m₁⁻¹) * incM F H'.ι =
      vecMulVec (t.1 • incV F H'.x) (b ᵥ* mat h₁⁻¹) + incM F H'.ι := by
    calc mat (p * m₂⁻¹ * m₁⁻¹) * incM F H'.ι = mat p * (mat m₂⁻¹ * (mat m₁⁻¹ * incM F H'.ι)) := by
          rw [mat_mul', mat_mul']; simp only [Matrix.mul_assoc]
      _ = mat m₁ * (mat (m₁⁻¹ * p) * incM F H'.ι) * mat h₁⁻¹ := by rw [e1, e2, e3]; simp only [Matrix.mul_assoc]
      _ = mat m₁ * (vecMulVec (incV F H'.x) b + incM F H'.ι * mat h₁) * mat h₁⁻¹ := by rw [hb]
      _ = vecMulVec (mat m₁ *ᵥ incV F H'.x) (b ᵥ* mat h₁⁻¹) + mat m₁ * incM F H'.ι * (mat h₁ * mat h₁⁻¹) := by
          rw [Matrix.mul_add, Matrix.add_mul, mul_vecMulVec, vecMulVec_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hm₁x, e4, mat_mul_inv', Matrix.mul_one]
  refine ⟨p * m₂⁻¹ * m₁⁻¹, Subgroup.subset_closure ⟨?_, ?_⟩, m₁, ⟨hm₁x, hm₁y, hm₁ι⟩, h₁, m₂, ⟨hm₂x, hm₂y, hm₂ι⟩,
    by group⟩
  · rw [mat_mul', mat_mul', ← mulVec_mulVec, hm₁inv, mulVec_smul, ← mulVec_mulVec, hm₂inv, hp, smul_smul,
      Units.inv_mul, one_smul]
  · intro z
    refine ⟨((b ᵥ* mat h₁⁻¹) ⬝ᵥ z) * t.1, ?_⟩
    rw [mulVec_mulVec, hn, add_mulVec, vmv_mulVec, smul_smul, add_comm]

end GlobalTheory.StabLineLevi
