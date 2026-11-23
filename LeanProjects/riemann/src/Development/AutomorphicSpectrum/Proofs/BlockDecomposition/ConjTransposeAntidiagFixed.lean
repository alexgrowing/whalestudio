import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct Matrix

namespace GlobalTheory.CompanionTheory.SwapRoot

variable {L : Type} [Field L] {n : ℕ}

def cI (n a : ℕ) (h : 2 * (a + 2) ≤ n) (p : Fin 2) : Fin n := ⟨a + p, by omega⟩

def cJ (n a : ℕ) (h : 2 * (a + 2) ≤ n) (p : Fin 2) : Fin n := ⟨n - 2 - a + p, by omega⟩

def cM (L : Type) [Field L] (c : Fin 2 → Fin n) : Matrix (Fin n) (Fin 2) L := fun b p => if b = c p then 1 else 0

theorem cM_tr_mul (c c' : Fin 2 → Fin n) :
    (cM L c)ᵀ * cM L c' = fun p r => if c p = c' r then 1 else 0 := by
  ext p r
  simp [Matrix.mul_apply, cM, Matrix.transpose_apply, eq_comm]

def w2 (L : Type) [Field L] : Matrix (Fin 2) (Fin 2) L := !![0, 1; 1, 0]

theorem weyl_mul_weyl : w2 L * w2 L = 1 := by
  ext p r; fin_cases p <;> fin_cases r <;> simp [w2, Matrix.mul_apply, Fin.sum_univ_two]

theorem antiJ_mul_cI (a : ℕ) (h : 2 * (a + 2) ≤ n) :
    antiJ L n * cM L (cI n a h) = cM L (cJ n a h) * w2 L := by
  ext b p
  have hL : (antiJ L n * cM L (cI n a h)) b p = if (b : ℕ) + (cI n a h p : ℕ) + 1 = n then 1 else 0 := by
    simp [Matrix.mul_apply, cM, antiJ]
  rw [hL]
  fin_cases p <;> simp [Matrix.mul_apply, cM, w2, Fin.sum_univ_two, cI, cJ, Fin.ext_iff] <;>
    exact if_congr (by omega) rfl rfl

theorem antiJ_mul_cJ (a : ℕ) (h : 2 * (a + 2) ≤ n) :
    antiJ L n * cM L (cJ n a h) = cM L (cI n a h) * w2 L := by
  ext b p
  have hL : (antiJ L n * cM L (cJ n a h)) b p = if (b : ℕ) + (cJ n a h p : ℕ) + 1 = n then 1 else 0 := by
    simp [Matrix.mul_apply, cM, antiJ]
  rw [hL]
  fin_cases p <;> simp [Matrix.mul_apply, cM, w2, Fin.sum_univ_two, cI, cJ, Fin.ext_iff] <;>
    exact if_congr (by omega) rfl rfl

theorem cI_tr_cI (a : ℕ) (h : 2 * (a + 2) ≤ n) : (cM L (cI n a h))ᵀ * cM L (cI n a h) = 1 := by
  rw [cM_tr_mul]
  ext p r
  simp only [cI, Fin.ext_iff, Matrix.one_apply]
  fin_cases p <;> fin_cases r <;> simp

theorem cJ_tr_cJ (a : ℕ) (h : 2 * (a + 2) ≤ n) : (cM L (cJ n a h))ᵀ * cM L (cJ n a h) = 1 := by
  rw [cM_tr_mul]
  ext p r
  simp only [cJ, Fin.ext_iff, Matrix.one_apply]
  fin_cases p <;> fin_cases r <;> simp

theorem cI_tr_cJ (a : ℕ) (h : 2 * (a + 2) ≤ n) : (cM L (cI n a h))ᵀ * cM L (cJ n a h) = 0 := by
  rw [cM_tr_mul]
  ext p r
  have := p.2
  have := r.2
  simp only [cI, cJ, Fin.ext_iff, Matrix.zero_apply]
  rw [if_neg (by omega)]

theorem cJ_tr_cI (a : ℕ) (h : 2 * (a + 2) ≤ n) : (cM L (cJ n a h))ᵀ * cM L (cI n a h) = 0 := by
  rw [cM_tr_mul]
  ext p r
  have := p.2
  have := r.2
  simp only [cI, cJ, Fin.ext_iff, Matrix.zero_apply]
  rw [if_neg (by omega)]

def blockM (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y : Matrix (Fin 2) (Fin 2) L) : Matrix (Fin n) (Fin n) L :=
  1 + cM L (cI n a h) * (X - 1) * (cM L (cI n a h))ᵀ + cM L (cJ n a h) * (Y - 1) * (cM L (cJ n a h))ᵀ

theorem blockM_one (a : ℕ) (h : 2 * (a + 2) ≤ n) : blockM (L := L) a h 1 1 = 1 := by
  simp [blockM]

theorem units_mul_relation_rearrange_commRing {R : Type} [Ring R] (A B A' B' : R) (h1 : A * B' = 0) (h2 : B * A' = 0) :
    (1 + A + B) * (1 + A' + B') = 1 + (A + A' + A * A') + (B + B' + B * B') := by
  simp only [add_mul, mul_add, one_mul, mul_one, h1, h2]
  abel

theorem blockM_mul (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y X' Y' : Matrix (Fin 2) (Fin 2) L) :
    blockM a h X Y * blockM a h X' Y' = blockM a h (X * X') (Y * Y') := by
  have h1 : (cM L (cI n a h))ᵀ * cM L (cI n a h) = 1 := cI_tr_cI a h
  have h2 : (cM L (cJ n a h))ᵀ * cM L (cJ n a h) = 1 := cJ_tr_cJ a h
  have h3 : (cM L (cI n a h))ᵀ * cM L (cJ n a h) = 0 := cI_tr_cJ a h
  have h4 : (cM L (cJ n a h))ᵀ * cM L (cI n a h) = 0 := cJ_tr_cI a h
  simp only [blockM]
  generalize cM L (cI n a h) = C at *
  generalize cM L (cJ n a h) = D at *
  have e1 : ∀ P Q : Matrix (Fin 2) (Fin 2) L, (C * P * Cᵀ) * (C * Q * Cᵀ) = C * (P * Q) * Cᵀ := fun P Q => by
    calc _ = C * P * (Cᵀ * C) * Q * Cᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  have e2 : ∀ P Q : Matrix (Fin 2) (Fin 2) L, (D * P * Dᵀ) * (D * Q * Dᵀ) = D * (P * Q) * Dᵀ := fun P Q => by
    calc _ = D * P * (Dᵀ * D) * Q * Dᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  have e3 : ∀ P Q : Matrix (Fin 2) (Fin 2) L, (C * P * Cᵀ) * (D * Q * Dᵀ) = 0 := fun P Q => by
    calc _ = C * P * (Cᵀ * D) * Q * Dᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3]; simp
  have e4 : ∀ P Q : Matrix (Fin 2) (Fin 2) L, (D * P * Dᵀ) * (C * Q * Cᵀ) = 0 := fun P Q => by
    calc _ = D * P * (Dᵀ * C) * Q * Cᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h4]; simp
  have f : ∀ (E : Matrix (Fin n) (Fin 2) L) (P Q : Matrix (Fin 2) (Fin 2) L), E * (P * Q - 1) * Eᵀ =
      E * (P - 1) * Eᵀ + E * (Q - 1) * Eᵀ + E * ((P - 1) * (Q - 1)) * Eᵀ := fun E P Q => by
    rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add]
    congr 2
    noncomm_ring
  rw [units_mul_relation_rearrange_commRing _ _ _ _ (e3 _ _) (e4 _ _), e1, e2, f C X X', f D Y Y']

def partner (σ : L →+* L) (h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L :=
  w2 L * cT σ ((h⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * w2 L

theorem partner_one (σ : L →+* L) : partner σ 1 = 1 := by
  simp [partner, cT_one, weyl_mul_weyl]

theorem partner_mul (σ : L →+* L) (g h : GL (Fin 2) L) : partner σ (g * h) = partner σ g * partner σ h := by
  simp only [partner]
  rw [_root_.mul_inv_rev, Units.val_mul, cT_mul]
  generalize cT σ ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = P
  generalize cT σ ((h⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = Q
  calc w2 L * (P * Q) * w2 L = w2 L * P * 1 * Q * w2 L := by simp [Matrix.mul_assoc]
    _ = _ := by rw [← weyl_mul_weyl (L := L)]; simp only [Matrix.mul_assoc]

def rootGL (σ : L →+* L) (a : ℕ) (h : 2 * (a + 2) ≤ n) : GL (Fin 2) L →* GL (Fin n) L :=
  MonoidHom.toHomUnits
    { toFun := fun g => blockM a h (g : Matrix (Fin 2) (Fin 2) L) (partner σ g)
      map_one' := by simp [partner_one, blockM_one]
      map_mul' := fun g g' => by simp [partner_mul, blockM_mul] }

theorem rootGL_val (σ : L →+* L) (a : ℕ) (h : 2 * (a + 2) ≤ n) (g : GL (Fin 2) L) :
    ((rootGL σ a h g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      blockM a h (g : Matrix (Fin 2) (Fin 2) L) (partner σ g) := rfl

theorem cT_blockM (σ : L →+* L) (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y : Matrix (Fin 2) (Fin 2) L) :
    cT σ (blockM a h X Y) = blockM a h (cT σ X) (cT σ Y) := by
  have hc : ∀ c : Fin 2 → Fin n, (cM L c).map σ = cM L c := fun c => by
    ext b p; simp only [cM, Matrix.map_apply]; split_ifs <;> simp
  have e : ∀ (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L),
      cT σ (cM L c * P * (cM L c)ᵀ) = cM L c * cT σ P * (cM L c)ᵀ := fun c P => by
    simp only [cT_mul]
    have h1 : cT σ (cM L c) = (cM L c)ᵀ := by simp [cT, hc]
    have h2 : cT σ (cM L c)ᵀ = cM L c := by
      simp only [cT, ← Matrix.transpose_map, hc, Matrix.transpose_transpose]
    rw [h1, h2, Matrix.mul_assoc]
  have hadd : ∀ P Q : Matrix (Fin n) (Fin n) L, cT σ (P + Q) = cT σ P + cT σ Q := fun P Q => by
    ext b p; simp [cT]
  have hsub : ∀ P Q : Matrix (Fin 2) (Fin 2) L, cT σ (P - Q) = cT σ P - cT σ Q := fun P Q => by
    ext b p; simp [cT]
  simp only [blockM, hadd, e, cT_one, hsub]

theorem blockM_unitary (σ : L →+* L) (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y : Matrix (Fin 2) (Fin 2) L)
    (h1 : cT σ X * w2 L * Y = w2 L) (h2 : cT σ Y * w2 L * X = w2 L) :
    cT σ (blockM a h X Y) * antiJ L n * blockM a h X Y = antiJ L n := by
  have hJC := antiJ_mul_cI (L := L) a h
  have hJD := antiJ_mul_cJ (L := L) a h
  have hCC := cI_tr_cI (L := L) a h
  have hDD := cJ_tr_cJ (L := L) a h
  have hCD := cI_tr_cJ (L := L) a h
  have hDC := cJ_tr_cI (L := L) a h
  have hJt : (antiJ L n)ᵀ = antiJ L n := by
    ext b d; simp only [antiJ, Matrix.transpose_apply]; exact if_congr (by omega) rfl rfl
  have hwt : (w2 L)ᵀ = w2 L := by
    ext p r; fin_cases p <;> fin_cases r <;> simp [w2]
  have hCJ : (cM L (cI n a h))ᵀ * antiJ L n = w2 L * (cM L (cJ n a h))ᵀ := by
    have := congrArg Matrix.transpose hJC
    simpa only [Matrix.transpose_mul, hJt, hwt] using this
  have hDJ : (cM L (cJ n a h))ᵀ * antiJ L n = w2 L * (cM L (cI n a h))ᵀ := by
    have := congrArg Matrix.transpose hJD
    simpa only [Matrix.transpose_mul, hJt, hwt] using this
  have hsub : ∀ P Q : Matrix (Fin 2) (Fin 2) L, cT σ (P - Q) = cT σ P - cT σ Q := fun P Q => by
    ext b p; simp [cT]
  rw [cT_blockM]
  simp only [blockM]
  generalize cM L (cI n a h) = C at *
  generalize cM L (cJ n a h) = D at *
  generalize antiJ L n = J at *
  generalize hA : cT σ X = A at *
  generalize hB : cT σ Y = B at *
  have s1 : (1 + C * (A - 1) * Cᵀ + D * (B - 1) * Dᵀ) * J =
      J + C * ((A - 1) * w2 L) * Dᵀ + D * ((B - 1) * w2 L) * Cᵀ := by
    simp only [Matrix.add_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc (C * (A - 1)), hCJ, Matrix.mul_assoc (D * (B - 1)), hDJ]
    simp only [Matrix.mul_assoc]
  have s2 : ∀ P Q U W : Matrix (Fin 2) (Fin 2) L, (J + C * P * Dᵀ + D * Q * Cᵀ) * (1 + C * U * Cᵀ + D * W * Dᵀ) =
      J + D * (w2 L * U + Q + Q * U) * Cᵀ + C * (w2 L * W + P + P * W) * Dᵀ := fun P Q U W => by
    have t1 : J * (C * U * Cᵀ) = D * (w2 L * U) * Cᵀ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJC, Matrix.mul_assoc D]
    have t2 : J * (D * W * Dᵀ) = C * (w2 L * W) * Dᵀ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJD, Matrix.mul_assoc C]
    have t3 : (C * P * Dᵀ) * (C * U * Cᵀ) = 0 := by
      calc _ = C * P * (Dᵀ * C) * U * Cᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hDC]; simp
    have t4 : (C * P * Dᵀ) * (D * W * Dᵀ) = C * (P * W) * Dᵀ := by
      calc _ = C * P * (Dᵀ * D) * W * Dᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hDD]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    have t5 : (D * Q * Cᵀ) * (C * U * Cᵀ) = D * (Q * U) * Cᵀ := by
      calc _ = D * Q * (Cᵀ * C) * U * Cᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hCC]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    have t6 : (D * Q * Cᵀ) * (D * W * Dᵀ) = 0 := by
      calc _ = D * Q * (Cᵀ * D) * W * Dᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hCD]; simp
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, t1, t2, t3, t4, t5, t6]
    abel
  rw [s1, s2]
  have z1 : w2 L * (Y - 1) + (A - 1) * w2 L + (A - 1) * w2 L * (Y - 1) = 0 := by
    have : w2 L * (Y - 1) + (A - 1) * w2 L + (A - 1) * w2 L * (Y - 1) = A * w2 L * Y - w2 L := by noncomm_ring
    rw [this, h1, sub_self]
  have z2 : w2 L * (X - 1) + (B - 1) * w2 L + (B - 1) * w2 L * (X - 1) = 0 := by
    have : w2 L * (X - 1) + (B - 1) * w2 L + (B - 1) * w2 L * (X - 1) = B * w2 L * X - w2 L := by noncomm_ring
    rw [this, h2, sub_self]
  rw [z1, z2]
  simp

theorem conj_transpose_antidiag_fixed (σ : L →+* L) : cT σ (w2 L) = w2 L := by
  ext p r; fin_cases p <;> fin_cases r <;> simp [w2, cT]

theorem cT_cT (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (X : Matrix (Fin 2) (Fin 2) L) : cT σ (cT σ X) = X := by
  ext p r; simp [cT, hσ]

theorem rootGL_mem (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (g : GL (Fin 2) L) :
    rootGL σ a h g ∈ GU σ n := by
  show cT σ ((rootGL σ a h g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n * _ = antiJ L n
  rw [rootGL_val]
  have hw := weyl_mul_weyl (L := L)
  have hg1 : ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg2 : (g : Matrix (Fin 2) (Fin 2) L) * ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine blockM_unitary σ a h _ _ ?_ ?_
  · simp only [partner]
    calc _ = cT σ (g : Matrix (Fin 2) (Fin 2) L) * (w2 L * w2 L) * cT σ ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * w2 L := by
          simp only [Matrix.mul_assoc]
      _ = cT σ (((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L)) * w2 L := by
          rw [hw, cT_mul]; simp
      _ = _ := by rw [hg1, cT_one, Matrix.one_mul]
  · simp only [partner, cT_mul, conj_transpose_antidiag_fixed, cT_cT σ hσ]
    calc _ = w2 L * ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (w2 L * w2 L) * (g : Matrix (Fin 2) (Fin 2) L) := by
          simp only [Matrix.mul_assoc]
      _ = w2 L * (((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L)) := by
          rw [hw]; simp [Matrix.mul_assoc]
      _ = _ := by rw [hg1, Matrix.mul_one]

def rootHom (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) : GL (Fin 2) L →* GU σ n :=
  (rootGL σ a h).codRestrict (GU σ n) (rootGL_mem σ hσ a h)

theorem rootHom_val (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (g : GL (Fin 2) L) :
    (((rootHom σ hσ a h g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      blockM a h (g : Matrix (Fin 2) (Fin 2) L) (partner σ g) := rfl

def nU (x : L) : GL (Fin 2) L where
  val := !![1, x; 0, 1]
  inv := !![1, -x; 0, 1]
  val_inv := by ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def wU (L : Type) [Field L] : GL (Fin 2) L where
  val := w2 L
  inv := w2 L
  val_inv := weyl_mul_weyl
  inv_val := weyl_mul_weyl

theorem nU_add (x y : L) : nU (x + y) = nU x * nU y := by
  ext p r; fin_cases p <;> fin_cases r <;> simp [nU, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem wU_mul_wU : wU L * wU L = 1 := Units.ext weyl_mul_weyl

def uR (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) : GU σ n :=
  rootHom σ hσ a h (nU x)

def sR (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) : GU σ n :=
  rootHom σ hσ a h (wU L)

theorem uR_add (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x y : L) :
    uR σ hσ a h (x + y) = uR σ hσ a h x * uR σ hσ a h y := by
  simp only [uR, nU_add, map_mul]

theorem sR_mul_sR (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) :
    sR σ hσ a h * sR σ hσ a h = 1 := by
  simp only [sR, ← map_mul, wU_mul_wU, map_one]

theorem cM_conj_apply (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L) (b d : Fin n) :
    (cM L c * P * (cM L c)ᵀ) b d = ∑ p, ∑ r, if b = c p ∧ d = c r then P p r else 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cM, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  by_cases h1 : b = c p <;> by_cases h2 : d = c r <;> simp [h1, h2]

theorem cI_injective (a : ℕ) (h : 2 * (a + 2) ≤ n) : Function.Injective (cI n a h) := fun p r e => by
  have := congrArg Fin.val e
  simp only [cI] at this
  exact Fin.ext (by omega)

theorem cJ_injective (a : ℕ) (h : 2 * (a + 2) ≤ n) : Function.Injective (cJ n a h) := fun p r e => by
  have := congrArg Fin.val e
  simp only [cJ] at this
  exact Fin.ext (by omega)

theorem cM_conj_same {c : Fin 2 → Fin n} (hc : Function.Injective c) (P : Matrix (Fin 2) (Fin 2) L) (p r : Fin 2) :
    (cM L c * P * (cM L c)ᵀ) (c p) (c r) = P p r := by
  rw [cM_conj_apply]
  simp [hc.eq_iff, ite_and]

theorem cM_conj_out {c : Fin 2 → Fin n} (P : Matrix (Fin 2) (Fin 2) L) {b d : Fin n}
    (h : (∀ p, b ≠ c p) ∨ ∀ p, d ≠ c p) : (cM L c * P * (cM L c)ᵀ) b d = 0 := by
  rw [cM_conj_apply]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun r _ => if_neg ?_
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · exact h p h1
  · exact h r h2

theorem cI_ne_cJ (a : ℕ) (h : 2 * (a + 2) ≤ n) (p r : Fin 2) : cI n a h p ≠ cJ n a h r := fun e => by
  have := congrArg Fin.val e
  have := p.2
  have := r.2
  simp only [cI, cJ] at *
  omega

theorem blockM_cI (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y : Matrix (Fin 2) (Fin 2) L) (p r : Fin 2) :
    blockM a h X Y (cI n a h p) (cI n a h r) = X p r := by
  simp only [blockM, Matrix.add_apply]
  rw [cM_conj_same (cI_injective a h), cM_conj_out _ (Or.inl fun t => cI_ne_cJ a h p t)]
  have : (1 : Matrix (Fin n) (Fin n) L) (cI n a h p) (cI n a h r) = (1 : Matrix (Fin 2) (Fin 2) L) p r := by
    simp [Matrix.one_apply, (cI_injective a h).eq_iff]
  simp [this]

theorem blockM_cJ (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y : Matrix (Fin 2) (Fin 2) L) (p r : Fin 2) :
    blockM a h X Y (cJ n a h p) (cJ n a h r) = Y p r := by
  simp only [blockM, Matrix.add_apply]
  rw [cM_conj_same (cJ_injective a h), cM_conj_out _ (Or.inl fun t => (cI_ne_cJ a h t p).symm)]
  have : (1 : Matrix (Fin n) (Fin n) L) (cJ n a h p) (cJ n a h r) = (1 : Matrix (Fin 2) (Fin 2) L) p r := by
    simp [Matrix.one_apply, (cJ_injective a h).eq_iff]
  simp [this]

theorem blockM_out (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y : Matrix (Fin 2) (Fin 2) L) {b d : Fin n}
    (h1 : (∀ p, b ≠ cI n a h p) ∨ ∀ p, d ≠ cI n a h p) (h2 : (∀ p, b ≠ cJ n a h p) ∨ ∀ p, d ≠ cJ n a h p) :
    blockM a h X Y b d = (1 : Matrix (Fin n) (Fin n) L) b d := by
  simp only [blockM, Matrix.add_apply]
  rw [cM_conj_out _ h1, cM_conj_out _ h2]
  simp

variable [Valued L (WithZero (Multiplicative ℤ))]

def IsAdm (w : ℂ) (F : L → ℂ) : Prop :=
  IsLocallyConstant F ∧ ∃ (R : ℤ) (C : ℂ), ∀ x : L, x ≠ 0 → ordL x ≤ R → F x = C * w ^ (-ordL x)

def sphFn (w : ℂ) (x : L) : ℂ := if Valued.v x ≤ 1 then 1 else w ^ (-ordL x)

section Main
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem v_eq_exp' {x : L} (hx : x ≠ 0) : Valued.v x = WithZero.exp (-ordL x) := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  unfold ordL
  rw [dif_neg h0, neg_neg]
  conv_lhs => rw [← WithZero.coe_unzero h0]
  rfl

theorem ordL_inv' {x : L} (hx : x ≠ 0) : ordL x⁻¹ = -ordL x := by
  have h1 := v_eq_exp' (inv_ne_zero hx)
  rw [map_inv₀, v_eq_exp' hx, ← WithZero.exp_neg] at h1
  have := WithZero.exp_injective h1
  omega

theorem chi_unip (χ : Fin (n / 2) → ℂ) (u : GU σ n) (hu : IsUnipU u) : chiDeltaU q χ u = 1 := by
  have h1 : ordL (1 : L) = 0 := by simp [ordL]; rfl
  unfold chiDeltaU
  refine Finset.prod_eq_one fun k _ => ?_
  split_ifs with hk
  · rw [hu.2, h1]; simp
  · rfl

theorem chi_borel_mul (hq : (q : ℂ) ≠ 0) (χ : Fin (n / 2) → ℂˣ) (b c : GU σ n) (hb : IsBorelU b) (hc : IsBorelU c) :
    chiDeltaU q (fun k => (χ k : ℂ)) (b * c) = chiDeltaU q (fun k => (χ k : ℂ)) b * chiDeltaU q (fun k => (χ k : ℂ)) c :=
  P.fIwasawa_chi_mul σ q _ (fun i => (χ i).ne_zero) hq b c ((P.spherical_upper_iff _).1 hb) ((P.spherical_upper_iff _).1 hc)

theorem borel_mul (b c : GU σ n) (hb : IsBorelU b) (hc : IsBorelU c) : IsBorelU (b * c) := by
  refine (P.spherical_upper_iff _).2 ?_
  rw [Subgroup.coe_mul]
  exact P.spherical_upper_mul _ _ ((P.spherical_upper_iff _).1 hb) ((P.spherical_upper_iff _).1 hc)

end Main

end GlobalTheory.CompanionTheory.SwapRoot

end
