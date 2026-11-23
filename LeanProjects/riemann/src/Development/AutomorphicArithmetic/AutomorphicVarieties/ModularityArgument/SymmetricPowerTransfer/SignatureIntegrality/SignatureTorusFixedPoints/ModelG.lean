import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.EUInvApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.NormalG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralOfEv

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Classical Loc Glob

section Alg

variable {K : Type} [Field K] {Δ τ : K}

private theorem sigL_mul' (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL]

private theorem sigL_sigL' (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sigL_ofE' (z : Etau K τ) : sigL (ofE Δ z) = ofE Δ z := by
  ext <;> simp [sigL, ofE]

private def Am (y : Sp Δ τ) : Sp Δ τ := (y.1, ofE Δ (QuadraticAlgebra.omega : Etau K τ) * y.2)

private theorem semi_semi {d : EL Δ τ} (h : d * sigL d = ofE Δ (QuadraticAlgebra.omega : Etau K τ)) (y : Sp Δ τ) :
    semi d (semi d y) = Am y := by
  simp only [semi, Am, star_star, sigL_mul', sigL_sigL', ← mul_assoc, h]

private theorem semi_tor (d : EL Δ τ) (z : (Etau K τ)ˣ) (y : Sp Δ τ) :
    semi d (tor Δ z y) = tor Δ z (semi d y) := by
  simp only [semi, tor, sigL_mul', sigL_ofE']
  exact Prod.ext rfl (mul_left_comm _ _ _)

private theorem star_mulVec' (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ) :
    star (M *ᵥ v) = M.map star *ᵥ star v := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, star_mul']

private theorem mat_ext {V : Type} [AddCommGroup V] [Module (Lsq K Δ) V] (Q : V ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ))
    {M M' : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (h : ∀ y, M *ᵥ Q y = M' *ᵥ Q y) : M = M' :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using h (Q.symm v))

variable {c : K} {d m : EL Δ τ} {δ : U3 Δ} {ι : (Etau K τ)ˣ →* U3 Δ} {Q : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)}

private theorem N_act (hd : IsDat c d m) (h : Models c d m δ ι Q) (y : Sp Δ τ) :
    ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ Q y = Q (Am y) := by
  rw [← semi_semi hd.d_norm, h.semi, h.semi, star_mulVec', star_star, Matrix.mulVec_mulVec]
  rfl

private theorem comm_U (h : Models c d m δ ι Q) (t : (Etau K τ)ˣ) : δ * theta Δ (ι t) = ι t * δ := by
  apply Subtype.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  obtain ⟨y, rfl⟩ : ∃ y, star (Q y) = v := ⟨Q.symm (star v), by simp⟩
  simp only [Matrix.toLin'_apply]
  have e1 : ((δ * theta Δ (ι t) : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (Q y) = Q (semi d (tor Δ t y)) := by
    rw [h.semi, h.tor, star_mulVec', Matrix.mulVec_mulVec]
    rfl
  have e2 : ((ι t * δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (Q y) = Q (tor Δ t (semi d y)) := by
    rw [h.tor, h.semi, Matrix.mulVec_mulVec]
    rfl
  rw [e1, e2, semi_tor]

private def crd : (Fin 3 → Lsq K Δ) ≃ₗ[Lsq K Δ] Sp Δ τ where
  toFun v := (v 0, ⟨v 1, v 2⟩)
  invFun y := ![y.1, y.2.re, y.2.im]
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv y := by ext <;> simp

private def A0 (Δ τ : K) : Matrix (Fin 3) (Fin 3) (Lsq K Δ) :=
  !![1, 0, 0; 0, 0, -1; 0, 1, algebraMap K _ τ]

private theorem Am_crd (v : Fin 3 → Lsq K Δ) : Am (crd (τ := τ) v) = crd (A0 Δ τ *ᵥ v) := by
  ext <;> simp [Am, crd, A0, ofE, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem companion_charpoly_factor : (A0 Δ τ).charpoly = (X - 1) * (X ^ 2 - C (algebraMap K _ τ) * X + 1) := by
  simp [Matrix.charpoly, A0, Matrix.det_fin_three, Matrix.charmatrix_apply, Matrix.diagonal]
  ring

private theorem hasTau_of (hd : IsDat c d m) (h : Models c d m δ ι Q) : HasTau δ τ := by
  set R : (Fin 3 → Lsq K Δ) ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ) := (crd (τ := τ)).trans Q with hR
  let B := LinearMap.toMatrix' (R : (Fin 3 → Lsq K Δ) →ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ))
  let B' := LinearMap.toMatrix' (R.symm : (Fin 3 → Lsq K Δ) →ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ))
  have hB : ∀ v, B *ᵥ v = R v := fun v => by simp [B, LinearMap.toMatrix'_mulVec]
  have hB' : ∀ v, B' *ᵥ v = R.symm v := fun v => by simp [B', LinearMap.toMatrix'_mulVec]
  have h1 : B * B' = 1 := Matrix.toLin'.injective (LinearMap.ext fun v => by
    simp [← Matrix.mulVec_mulVec, hB, hB'])
  have h2 : B' * B = 1 := Matrix.toLin'.injective (LinearMap.ext fun v => by
    simp [← Matrix.mulVec_mulVec, hB, hB'])
  have h3 : ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * B = B * A0 Δ τ :=
    Matrix.toLin'.injective (LinearMap.ext fun v => by
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hB]
      simp only [hR, LinearEquiv.trans_apply]
      rw [N_act hd h, Am_crd])
  let u : (Matrix (Fin 3) (Fin 3) (Lsq K Δ))ˣ := ⟨B, B', h1, h2⟩
  have h4 : ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = u.val * A0 Δ τ * u⁻¹.val := by
    change _ = B * A0 Δ τ * B'
    rw [← h3, mul_assoc, h1, mul_one]
  unfold HasTau
  rw [h4, Matrix.coe_units_inv, Matrix.charpoly_units_conj, companion_charpoly_factor]

end Alg

section Mid

variable {K : Type} [Field K] {Δ τ : K}

private theorem tor_of_fst (z : (Etau K τ)ˣ) (w : Sp Δ τ) (hw : w.1 = 0) :
    tor Δ z w = algebraMap K (Lsq K Δ) (quo z).re • w + algebraMap K (Lsq K Δ) (quo z).im • Am w := by
  obtain ⟨w₀, w₁⟩ := w
  obtain rfl : w₀ = 0 := hw
  ext <;> simp [tor, Am, ofE] <;> ring

private theorem tor_of_snd (z : (Etau K τ)ˣ) (w : Sp Δ τ) (hw : w.2 = 0) : tor Δ z w = w := by
  obtain ⟨w₀, w₁⟩ := w
  obtain rfl : w₁ = 0 := hw
  simp [tor]

variable {c : K} {d m : EL Δ τ} {δ : U3 Δ} {ι : (Etau K τ)ˣ →* U3 Δ} {Q : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)}

private theorem id1 (hd : IsDat c d m) (h : Models c d m δ ι Q) (t : (Etau K τ)ˣ) :
    (ι t : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) - 1) =
      (algebraMap K (Lsq K Δ) (quo t).re • (1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) +
        algebraMap K (Lsq K Δ) (quo t).im • ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ))) *
      (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) - 1) := by
  apply mat_ext Q
  intro y
  have e : (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) - 1) *ᵥ Q y = Q (Am y - y) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, N_act hd h, map_sub]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, ← h.tor, tor_of_fst t _ (by simp [Am]),
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, N_act hd h, map_add, map_smul, map_smul]

private theorem id2 (hd : IsDat c d m) (h : Models c d m δ ι Q) (t : (Etau K τ)ˣ) :
    (ι t : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) -
        algebraMap K (Lsq K Δ) τ • ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) + 1) =
      ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) -
        algebraMap K (Lsq K Δ) τ • ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) + 1 := by
  apply mat_ext Q
  intro y
  have e : (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) -
        algebraMap K (Lsq K Δ) τ • ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) + 1) *ᵥ Q y =
      Q (Am (Am y) - algebraMap K (Lsq K Δ) τ • Am y + y) := by
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      N_act hd h, N_act hd h, map_add, map_sub, map_smul]
  rw [← Matrix.mulVec_mulVec, e, ← h.tor, tor_of_snd]
  ext <;> simp [Am, ofE] <;> ring

end Mid

section Lin

variable {K : Type} [Field K]

private theorem col_of {T : Matrix (Fin 3) (Fin 3) K} {u v : Fin 3 → K}
    (h : T * diagonal u = diagonal v * diagonal u) (j : Fin 3) (hj : u j ≠ 0) (i : Fin 3) :
    T i j = diagonal v i j := by
  have := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal] at this
  exact mul_right_cancel₀ hj this

private theorem diag_of {T : Matrix (Fin 3) (Fin 3) K} {a b re im τ : K} (ha : a ≠ 1) (hb : b ≠ 1) (ht : 2 - τ ≠ 0)
    (hA : a * a - τ * a + 1 = 0) (hB : b * b - τ * b + 1 = 0)
    (h1 : T * (diagonal ![a, 1, b] - 1) = (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • diagonal ![a, 1, b]) * (diagonal ![a, 1, b] - 1))
    (h2 : T * (diagonal ![a, 1, b] * diagonal ![a, 1, b] - τ • diagonal ![a, 1, b] + 1) =
      diagonal ![a, 1, b] * diagonal ![a, 1, b] - τ • diagonal ![a, 1, b] + 1) :
    T = diagonal ![re + im * a, 1, re + im * b] := by
  have e1 : (diagonal ![a, 1, b] - 1 : Matrix (Fin 3) (Fin 3) K) = diagonal ![a - 1, 0, b - 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  have e2 : (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • diagonal ![a, 1, b]) = diagonal ![re + im * a, re + im, re + im * b] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  have e3 : (diagonal ![a, 1, b] * diagonal ![a, 1, b] - τ • diagonal ![a, 1, b] + 1 : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![0, 2 - τ, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, hA, hB]
    ring
  rw [e1, e2] at h1
  rw [e3] at h2
  have h2' : T * diagonal ![0, 2 - τ, 0] = diagonal 1 * diagonal ![0, 2 - τ, 0] := by
    rw [h2, show (diagonal 1 : Matrix (Fin 3) (Fin 3) K) = 1 from Matrix.diagonal_one, one_mul]
  have c0 := col_of h1 0 (by simpa using sub_ne_zero.2 ha)
  have c2 := col_of h1 2 (by simpa using sub_ne_zero.2 hb)
  have c1 := col_of h2' 1 (by simpa using ht)
  ext i j
  fin_cases j
  · rw [show (⟨0, by omega⟩ : Fin 3) = 0 from rfl] ; rw [c0]; fin_cases i <;> simp
  · rw [show (⟨1, by omega⟩ : Fin 3) = 1 from rfl] ; rw [c1]; fin_cases i <;> simp
  · rw [show (⟨2, by omega⟩ : Fin 3) = 2 from rfl] ; rw [c2]; fin_cases i <;> simp

private theorem conj_ids {G Gi T D₀ Dm : Matrix (Fin 3) (Fin 3) K} {re im τ : K} (hG : Gi * G = 1) (hD : Dm * G = G * D₀)
    (h1 : T * (Dm - 1) = (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • Dm) * (Dm - 1))
    (h2 : T * (Dm * Dm - τ • Dm + 1) = Dm * Dm - τ • Dm + 1) :
    (Gi * T * G) * (D₀ - 1) = (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • D₀) * (D₀ - 1) ∧
    (Gi * T * G) * (D₀ * D₀ - τ • D₀ + 1) = D₀ * D₀ - τ • D₀ + 1 := by
  have hA : (Dm - 1) * G = G * (D₀ - 1) := by rw [sub_mul, mul_sub, one_mul, mul_one, hD]
  have hB : (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • Dm) * G = G * (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • D₀) := by
    rw [add_mul, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, hD, one_mul, mul_one]
  have hDD : Dm * Dm * G = G * (D₀ * D₀) := by rw [mul_assoc, hD, ← mul_assoc, hD, mul_assoc]
  have hC : (Dm * Dm - τ • Dm + 1) * G = G * (D₀ * D₀ - τ • D₀ + 1) := by
    rw [add_mul, sub_mul, mul_add, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hD, hDD, one_mul, mul_one]
  have cancel : ∀ X : Matrix (Fin 3) (Fin 3) K, Gi * (G * X) = X := fun X => by rw [← mul_assoc, hG, one_mul]
  constructor
  · calc Gi * T * G * (D₀ - 1) = Gi * (T * (Dm - 1)) * G := by
          simp only [mul_assoc]; rw [← hA]
      _ = Gi * (((re • (1 : Matrix (Fin 3) (Fin 3) K) + im • Dm) * G) * (D₀ - 1)) + 0 := by
          rw [h1, mul_assoc (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • Dm), add_zero, mul_assoc Gi, mul_assoc _ (Dm - 1), hA]
      _ = _ := by rw [hB, add_zero, mul_assoc G, cancel]
  · calc Gi * T * G * (D₀ * D₀ - τ • D₀ + 1) = Gi * (T * (Dm * Dm - τ • Dm + 1)) * G := by
          simp only [mul_assoc]; rw [← hC]
      _ = _ := by rw [h2, mul_assoc Gi, hC, cancel]

end Lin

section Proj

variable {K : Type} [Field K] {Δ s τ : K}

private theorem pm_smul (hs : s * s = Δ) (x : K) (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) :
    (proj hs).mapMatrix (algebraMap K (Lsq K Δ) x • M) = x • (proj hs).mapMatrix M := by
  ext i j
  simp [proj]
  ring

private theorem pm_coe (hs : s * s = Δ) (g : U3 Δ) :
    (proj hs).mapMatrix (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = (eU hs g : Matrix (Fin 3) (Fin 3) K) := rfl

variable {c : K} {d m : EL Δ τ} {δ : U3 Δ} {ι : (Etau K τ)ˣ →* U3 Δ} {Q : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)}

private theorem id1K (hs : s * s = Δ) (hd : IsDat c d m) (h : Models c d m δ ι Q) (t : (Etau K τ)ˣ) :
    (eU hs (ι t) : Matrix (Fin 3) (Fin 3) K) * ((eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) - 1) =
      ((quo t).re • (1 : Matrix (Fin 3) (Fin 3) K) + (quo t).im • (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K)) *
      ((eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) - 1) := by
  have h1 := congrArg (proj hs).mapMatrix (id1 hd h t)
  rw [map_mul, map_mul, map_sub, map_add, pm_smul, pm_smul, map_one, pm_coe, pm_coe] at h1
  exact h1

private theorem id2K (hs : s * s = Δ) (hd : IsDat c d m) (h : Models c d m δ ι Q) (t : (Etau K τ)ˣ) :
    (eU hs (ι t) : Matrix (Fin 3) (Fin 3) K) * ((eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) * (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) -
        τ • (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) + 1) =
      (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) * (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) -
        τ • (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) + 1 := by
  have h1 := congrArg (proj hs).mapMatrix (id2 hd h t)
  rw [map_mul, map_add, map_sub, map_mul, pm_smul, map_one, pm_coe, pm_coe] at h1
  exact h1

end Proj

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem dg_val (x y z : kˣ) :
    ((dg ![x, y, z] : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal ![(x : k), (y : k), (z : k)] := by
  rw [val_diagT]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem conj_form {g₀ : GL (Fin 3) k} {T Dm : Matrix (Fin 3) (Fin 3) k} {a b r r' : kˣ} {re im τ : k}
    (hD : Dm * (g₀ : Matrix (Fin 3) (Fin 3) k) = (g₀ : Matrix (Fin 3) (Fin 3) k) * diagonal ![(a : k), 1, (b : k)])
    (ha : (a : k) ≠ 1) (hb : (b : k) ≠ 1) (ht : 2 - τ ≠ 0)
    (hA : (a : k) * a - τ * a + 1 = 0) (hB : (b : k) * b - τ * b + 1 = 0)
    (h1 : T * (Dm - 1) = (re • (1 : Matrix (Fin 3) (Fin 3) k) + im • Dm) * (Dm - 1))
    (h2 : T * (Dm * Dm - τ • Dm + 1) = Dm * Dm - τ • Dm + 1)
    (hr : re + im * a = r) (hr' : re + im * b = r') :
    T = ((g₀ * dg ![r, 1, r'] * g₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  have hGi : ((g₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (g₀ : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul]; simp
  have hGG : (g₀ : Matrix (Fin 3) (Fin 3) k) * ((g₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul]; simp
  obtain ⟨c1, c2⟩ := conj_ids hGi hD h1 h2
  have hT := diag_of ha hb ht hA hB c1 c2
  rw [hr, hr'] at hT
  rw [Units.val_mul, Units.val_mul, dg_val, Units.val_one, ← hT]
  simp only [mul_assoc]
  rw [hGG, mul_one, ← mul_assoc, hGG, one_mul]

end Loc

theorem modelG : ModelG := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0
  obtain ⟨-, hth, -, htau⟩ := eU_facts k O hO h2 Δ s hs hs0
  refine ⟨fun τ c d m δ ι Q hd hm => ⟨hasTau_of hd hm, fun t => ?_⟩, ?_⟩
  · rw [mul_assoc, comm_U hm t, ← mul_assoc, inv_mul_cancel, one_mul]
  intro a ha c d m δ ι Q hd hm
  have hab : (a : k) * ((a⁻¹ : kˣ) : k) = 1 := by simp
  have hcp := (htau δ _).1 (hasTau_of hd hm)
  have hcp' : ((eU hs δ * th k 3 (eU hs δ) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly =
      (X - C 1) * (X - C (a : k)) * (X - C ((a⁻¹ : kˣ) : k)) := by
    have e : (C (a : k) : k[X]) * C ((a⁻¹ : kˣ) : k) = 1 := by rw [← C_mul, hab, C_1]
    rw [hcp]
    simp only [C_add, C_1]
    linear_combination (-(X - 1 : k[X])) * e
  obtain ⟨g₀, x, y, z, hδ, hxz⟩ := (normalG k).2 _ a ha hcp'
  have hN := (normalG k).1 g₀ x y z
  rw [← hδ, hxz, show z / x = a⁻¹ by rw [← hxz, inv_div]] at hN
  refine ⟨g₀, x, y, z, hδ, hxz, fun t => ?_⟩
  have hDm : eU hs (δ * theta Δ δ) = g₀ * dg ![a, 1, a⁻¹] * g₀⁻¹ := by rw [map_mul, hth, hN]
  have hDG : ((eU hs (δ * theta Δ δ) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (g₀ : Matrix (Fin 3) (Fin 3) k) =
      (g₀ : Matrix (Fin 3) (Fin 3) k) * diagonal ![(a : k), 1, ((a⁻¹ : kˣ) : k)] := by
    have e : eU hs (δ * theta Δ δ) * g₀ = g₀ * dg ![a, 1, a⁻¹] := by rw [hDm, inv_mul_cancel_right]
    have e' := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k)) e
    simp only [Units.val_mul] at e'
    rw [e', dg_val, Units.val_one]
  have ha1 : (a : k) ≠ 1 := fun e => by simp [e] at ha
  have hb1 : ((a⁻¹ : kˣ) : k) ≠ 1 := fun e => ha1 (by rw [e, mul_one] at hab; exact hab)
  have ht : 2 - ((a : k) + (a⁻¹ : kˣ)) ≠ 0 := fun e => hd.reg (by
    have e' : (a : k) + (a⁻¹ : kˣ) = 2 := by linear_combination -e
    rw [e']; norm_num)
  obtain ⟨-, -, hr⟩ := roots k O hO a ha
  obtain ⟨r1, r2⟩ := hr t
  have r1' : (quo t).re + (quo t).im * (a : k) = (((evU (root_left a) / evU (root_right a)) t : kˣ) : k) := by
    rw [MonoidHom.div_apply, ← r1, mul_comm (quo t).im]; rfl
  have r2' : (quo t).re + (quo t).im * ((a⁻¹ : kˣ) : k) = ((((evU (root_left a) / evU (root_right a)) t)⁻¹ : kˣ) : k) := by
    rw [MonoidHom.div_apply, inv_div, ← r2, mul_comm (quo t).im]; rfl
  apply Units.ext
  exact conj_form hDG ha1 hb1 ht (by linear_combination -hab) (by linear_combination -hab)
    (id1K hs hd hm t) (id2K hs hd hm t) r1' r2'

end UpperTheory.V.Z.Sym.Sig
end
