import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

noncomputable section

namespace GlobalTheory.LevNorm.PlaceSys

theorem gU_intM_mul {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O) : ∀ i j, (M * N) i j ∈ O := fun i j => by
  rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (hM i k) (hN k j)

theorem gU_glO {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (M N : Matrix (Fin n) (Fin n) K)
    (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O) (h : M * N = 1) :
    ∃ y : GL (Fin n) O, ((bc O.subtype y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = M := by
  have h' : N * M = 1 := mul_eq_one_comm.1 h
  have inj : Function.Injective fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype :=
    Matrix.map_injective fun x y hxy => Subtype.ext hxy
  refine ⟨⟨Matrix.of fun i j => ⟨M i j, hM i j⟩, Matrix.of fun i j => ⟨N i j, hN i j⟩, inj ?_, inj ?_⟩, rfl⟩
  · show Matrix.map _ O.subtype = Matrix.map _ O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact h
  · show Matrix.map _ O.subtype = Matrix.map _ O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact h'

theorem gU_val_inv {R : Type} [CommRing R] {n : ℕ} (g : GL (Fin n) R) (L : Matrix (Fin n) (Fin n) R)
    (h : L * (g : Matrix (Fin n) (Fin n) R) = 1) : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = L := by
  calc ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
      = L * (g : Matrix (Fin n) (Fin n) R) * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
        rw [h, Matrix.one_mul]
    _ = L := by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem gU_cT_smul {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (w : A) (M : Matrix (Fin n) (Fin n) A) :
    cT σ (w • M) = σ w • cT σ M := by
  ext i j; simp [cT]

theorem gU_mapMatrix_smul {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (w : A)
    (M : Matrix (Fin n) (Fin n) A) : φ.mapMatrix (w • M) = φ w • φ.mapMatrix M := by
  ext i j; simp

variable {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q}
  (Z : PlaceSys A S P k r) {σ : A →+* A}

theorem gU_inv_comp {Q Q' : P} {s : Z.K Q →+* Z.K Q'} (hs : ∀ a, s (Z.p Q a) = Z.p Q' (σ a))
    (hsO : ∀ x ∈ Z.O Q, s x ∈ Z.O Q') {n : ℕ} (G : GL (Fin n) S) (u : GL (Fin n) A)
    (hu : u ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (d : Z.K Q) (W : Matrix (Fin n) (Fin n) (Z.K Q)) (hW : ∀ i j, W i j ∈ Z.O Q)
    (h : (Z.p Q).mapMatrix (u : Matrix (Fin n) (Fin n) A) = d • W) :
    ∃ I : Matrix (Fin n) (Fin n) (Z.K Q'), (∀ i j, I i j ∈ Z.O Q') ∧
      (Z.p Q').mapMatrix ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = s d • I := by
  set Gm : Matrix (Fin n) (Fin n) A := ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) with hGm
  set Gi : Matrix (Fin n) (Fin n) A := ((bc S.subtype G⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) with hGi
  have hu' : cT σ (u : Matrix (Fin n) (Fin n) A) * Gm * u = Gm := hu
  have hGG : Gi * Gm = 1 := by
    rw [hGi, hGm, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have key : ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = Gi * cT σ (u : Matrix (Fin n) (Fin n) A) * Gm := by
    apply gU_val_inv
    calc Gi * cT σ (u : Matrix (Fin n) (Fin n) A) * Gm * u = Gi * (cT σ (u : Matrix (Fin n) (Fin n) A) * Gm * u) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu', hGG]
  have hcT : (Z.p Q').mapMatrix (cT σ (u : Matrix (Fin n) (Fin n) A)) = s d • (W.map s)ᵀ := by
    ext i j
    have := congrFun (congrFun h j) i
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
    simp only [cT, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← hs, this, map_mul]
  refine ⟨(Z.p Q').mapMatrix Gi * (W.map s)ᵀ * (Z.p Q').mapMatrix Gm, ?_, ?_⟩
  · have hG1 : ∀ (g : GL (Fin n) S) i j,
        (Z.p Q').mapMatrix ((bc S.subtype g : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j ∈ Z.O Q' :=
      fun g i j => (Z.int _).1 ((g : Matrix (Fin n) (Fin n) S) i j).2 Q'
    exact gU_intM_mul _ (gU_intM_mul _ (hG1 _) fun i j => hsO _ (hW j i)) (hG1 _)
  · rw [key, map_mul, map_mul, hcT, Matrix.mul_smul, Matrix.smul_mul]

theorem gU_scal_conj {Q Q' : P} {s : Z.K Q →+* Z.K Q'} (hs : ∀ a, s (Z.p Q a) = Z.p Q' (σ a))
    (hsO : ∀ x ∈ Z.O Q, s x ∈ Z.O Q') {n : ℕ} (G : GL (Fin n) S) (m : GL (Fin n) A)
    (hm : m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) (c : (Z.K Q)ˣ)
    (x : GL (Fin n) (Z.O Q))
    (hc : (Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A) =
      (c : Z.K Q) • ((bc (Z.O Q).subtype x : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q))) :
    ∃ y : GL (Fin n) (Z.O Q'), (Z.p Q').mapMatrix (m : Matrix (Fin n) (Fin n) A) =
      (s c)⁻¹ • ((bc (Z.O Q').subtype y : GL (Fin n) (Z.K Q')) : Matrix (Fin n) (Fin n) (Z.K Q')) := by
  set X := ((bc (Z.O Q).subtype x : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hX
  set Xi := ((bc (Z.O Q).subtype x⁻¹ : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hXi
  have hXint : ∀ i j, X i j ∈ Z.O Q := fun i j => ((x : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hXiint : ∀ i j, Xi i j ∈ Z.O Q := fun i j => (((x⁻¹ : GL (Fin n) (Z.O Q)) : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hXX : Xi * X = 1 := by rw [hXi, hX, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hinv : (Z.p Q).mapMatrix ((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = (c : Z.K Q)⁻¹ • Xi := by
    show ((bc (Z.p Q) m⁻¹ : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) = _
    rw [map_inv]
    apply gU_val_inv
    show _ * (Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A) = 1
    rw [hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul, hXX]
  obtain ⟨I1, hI1, e1⟩ := gU_inv_comp Z hs hsO G m hm c X hXint hc
  obtain ⟨I2, hI2, e2⟩ := gU_inv_comp Z hs hsO G m⁻¹ (inv_mem hm) ((c : Z.K Q)⁻¹) Xi hXiint hinv
  rw [inv_inv, map_inv₀] at e2
  have hsc : s c ≠ 0 := (map_ne_zero s).2 c.ne_zero
  have h2 : I2 = s c • (Z.p Q').mapMatrix (m : Matrix (Fin n) (Fin n) A) := by
    rw [e2, smul_smul, mul_inv_cancel₀ hsc, one_smul]
  have h1 : I1 = (s c)⁻¹ • (Z.p Q').mapMatrix ((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
    rw [e1, smul_smul, inv_mul_cancel₀ hsc, one_smul]
  have hprod : I2 * I1 = 1 := by
    rw [h1, h2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hsc, one_smul, ← map_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  obtain ⟨y, hy⟩ := gU_glO _ I2 I1 hI2 hI1 hprod
  exact ⟨y, by rw [hy]; exact e2⟩

end GlobalTheory.LevNorm.PlaceSys

namespace GlobalTheory.LevNorm.PlaceSys

variable {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q}
  (Z : PlaceSys A S P k r) {σ : A →+* A}

theorem gU_good_self (hS : ∀ a ∈ S, σ a ∈ S) {Q : P} (hQ : σ (Z.e Q) = Z.e Q) {n : ℕ} (G : GL (Fin n) S)
    (m : GL (Fin n) A) (hm : m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (h : IsScal (Z.O Q) (bc (Z.p Q) m)) :
    ∃ y : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y = bc (Z.p Q) m := by
  obtain ⟨s, hs, hsO⟩ := Z.exists_conj hS hQ
  obtain ⟨c, x, hc⟩ := h
  have hc' : (Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A) =
      (c : Z.K Q) • ((bc (Z.O Q).subtype x : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) := hc
  obtain ⟨y, hy⟩ := gU_scal_conj Z hs hsO G m hm c x hc'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact ⟨1, Subsingleton.elim _ _⟩
  set X := ((bc (Z.O Q).subtype x : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hX
  set Xi := ((bc (Z.O Q).subtype x⁻¹ : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hXi
  set Y := ((bc (Z.O Q).subtype y : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hY
  set Yi := ((bc (Z.O Q).subtype y⁻¹ : GL (Fin n) (Z.K Q)) : Matrix (Fin n) (Fin n) (Z.K Q)) with hYi
  have hXint : ∀ i j, X i j ∈ Z.O Q := fun i j => ((x : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hXiint : ∀ i j, Xi i j ∈ Z.O Q := fun i j => (((x⁻¹ : GL (Fin n) (Z.O Q)) : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hYint : ∀ i j, Y i j ∈ Z.O Q := fun i j => ((y : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hYiint : ∀ i j, Yi i j ∈ Z.O Q := fun i j => (((y⁻¹ : GL (Fin n) (Z.O Q)) : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have hXXi : X * Xi = 1 := by rw [hXi, hX, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hYYi : Y * Yi = 1 := by rw [hYi, hY, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hsc : s c ≠ 0 := (map_ne_zero s).2 c.ne_zero
  set t : Z.K Q := (c : Z.K Q) * s c with ht
  have ht0 : t ≠ 0 := mul_ne_zero c.ne_zero hsc
  have hYX : t • X = Y := by
    have e : (c : Z.K Q) • X = (s c)⁻¹ • Y := hc'.symm.trans hy
    calc t • X = s c • ((c : Z.K Q) • X) := by rw [smul_smul, ht, mul_comm]
      _ = s c • ((s c)⁻¹ • Y) := by rw [e]
      _ = Y := by rw [smul_smul, mul_inv_cancel₀ hsc, one_smul]
  have hXY : t⁻¹ • Y = X := by rw [← hYX, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  let i0 : Fin n := ⟨0, hn⟩
  have htO : t ∈ Z.O Q := by
    have e : (Y * Xi) i0 i0 = t := by
      rw [← hYX, Matrix.smul_mul, hXXi, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [← e]; exact gU_intM_mul _ hYint hXiint i0 i0
  have htiO : t⁻¹ ∈ Z.O Q := by
    have e : (X * Yi) i0 i0 = t⁻¹ := by
      rw [← hXY, Matrix.smul_mul, hYYi, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [← e]; exact gU_intM_mul _ hXint hYiint i0 i0
  have hcO : (c : Z.K Q) ∈ Z.O Q ∧ (c : Z.K Q)⁻¹ ∈ Z.O Q := by
    rcases (Z.O Q).mem_or_inv_mem (c : Z.K Q) with h1 | h1
    · refine ⟨h1, ?_⟩
      have e : (c : Z.K Q)⁻¹ = s c * t⁻¹ := by
        rw [ht, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hsc, one_mul]
      rw [e]; exact mul_mem (hsO _ h1) htiO
    · refine ⟨?_, h1⟩
      have e : (c : Z.K Q) = t * (s c)⁻¹ := by rw [ht, mul_assoc, mul_inv_cancel₀ hsc, mul_one]
      have h2 : (s c)⁻¹ ∈ Z.O Q := by rw [← map_inv₀]; exact hsO _ h1
      rw [e]; exact mul_mem htO h2
  obtain ⟨y', hy'⟩ := gU_glO _ ((c : Z.K Q) • X) ((c : Z.K Q)⁻¹ • Xi) (fun i j => mul_mem hcO.1 (hXint i j))
    (fun i j => mul_mem hcO.2 (hXiint i j))
    (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ c.ne_zero, one_smul, hXXi])
  exact ⟨y', Units.ext (hy'.trans hc'.symm)⟩

theorem gU_comp_sigma (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) (Q : P) :
    ∃ R, σ (Z.e R) = Z.e Q ∧ ∃ t : Z.K R →+* Z.K Q, ∀ a, t (Z.p R a) = Z.p Q (σ a) := by
  obtain ⟨R, hR⟩ := Z.exists_bar hσ Q
  have h : σ (Z.e R) = Z.e Q := by rw [← hR, hσ]
  obtain ⟨t, ht, -⟩ := Z.exists_conj hS h
  exact ⟨R, h, t, ht⟩

end GlobalTheory.LevNorm.PlaceSys

namespace GlobalTheory.LevNorm.PlaceSys

variable {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q}
  (Z : PlaceSys A S P k r) {σ : A →+* A}

theorem gU_step (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) {n : ℕ} (G : GL (Fin n) S)
    (m : GL (Fin n) A) (hm : m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (hscal : ∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m)) {a a' : P} (ha : σ (Z.e a) = Z.e a') (hne : a ≠ a') :
    ∃ (z : A) (m₁ : GL (Fin n) A), z * σ z = 1 ∧
      (m : Matrix (Fin n) (Fin n) A) = z • (m₁ : Matrix (Fin n) (Fin n) A) ∧
      m₁ ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧
      (∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m₁)) ∧ (∀ Q, Q ≠ a → Q ≠ a' → bc (Z.p Q) m₁ = bc (Z.p Q) m) ∧
      (∃ y : GL (Fin n) (Z.O a), bc (Z.O a).subtype y = bc (Z.p a) m₁) ∧
      (∃ y : GL (Fin n) (Z.O a'), bc (Z.O a').subtype y = bc (Z.p a') m₁) := by
  obtain ⟨s, hs, hsO⟩ := Z.exists_conj hS ha
  obtain ⟨c, x, hc⟩ := hscal a
  have hc' : (Z.p a).mapMatrix (m : Matrix (Fin n) (Fin n) A) =
      (c : Z.K a) • ((bc (Z.O a).subtype x : GL (Fin n) (Z.K a)) : Matrix (Fin n) (Fin n) (Z.K a)) := hc
  obtain ⟨y, hy⟩ := gU_scal_conj Z hs hsO G m hm c x hc'
  have hsc : s c ≠ 0 := (map_ne_zero s).2 c.ne_zero
  obtain ⟨α, hα1, hα2⟩ := Z.exists_single a ((c : Z.K a) - 1)
  obtain ⟨β, hβ1, hβ2⟩ := Z.exists_single a' ((s c)⁻¹ - 1)
  set z : A := 1 + α + β with hz
  have pa : Z.p a z = c := by rw [hz, map_add, map_add, map_one, hα1, hβ2 a hne]; ring
  have pa' : Z.p a' z = (s c)⁻¹ := by rw [hz, map_add, map_add, map_one, hα2 a' (Ne.symm hne), hβ1]; ring
  have po : ∀ Q, Q ≠ a → Q ≠ a' → Z.p Q z = 1 := fun Q h1 h2 => by
    rw [hz, map_add, map_add, map_one, hα2 Q h1, hβ2 Q h2]; ring
  have σinj : ∀ u v, σ u = σ v → u = v := fun u v h => by rw [← hσ u, h, hσ]
  have einj := Z.e_injective
  have hzz : z * σ z = 1 := by
    refine Z.ext' fun Q => ?_
    obtain ⟨R, hR, t, ht⟩ := gU_comp_sigma Z hσ hS Q
    rw [map_mul, ← ht, map_one]
    by_cases hQa : Q = a
    · subst hQa
      have hRa' : R = a' := einj (σinj _ _ (by rw [hR, ← ha, hσ]))
      subst hRa'
      obtain ⟨w, hw⟩ := Z.surj Q c
      have e : t (s c) = c := by rw [← hw, hs, ht, hσ]
      rw [pa, pa', map_inv₀, e, mul_inv_cancel₀ c.ne_zero]
    · by_cases hQa' : Q = a'
      · subst hQa'
        have hRa : R = a := einj (σinj _ _ (by rw [hR, ha]))
        subst hRa
        obtain ⟨w, hw⟩ := Z.surj R c
        have e : t c = s c := by rw [← hw, hs, ht]
        rw [pa', pa, e, inv_mul_cancel₀ hsc]
      · have hR1 : R ≠ a := fun h => hQa' (einj (by rw [← hR, h, ha]))
        have hR2 : R ≠ a' := fun h => hQa (einj (by rw [← hR, h, ← ha, hσ]))
        rw [po Q hQa hQa', po R hR1 hR2, map_one, mul_one]
  have hzz' : σ z * z = 1 := by rw [mul_comm]; exact hzz
  let m₁ : GL (Fin n) A := ⟨σ z • (m : Matrix (Fin n) (Fin n) A), z • ((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A),
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hzz', one_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hzz, one_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one]⟩
  have hm₁ : (m₁ : Matrix (Fin n) (Fin n) A) = σ z • (m : Matrix (Fin n) (Fin n) A) := rfl
  have pm : ∀ Q, (Z.p Q).mapMatrix (m₁ : Matrix (Fin n) (Fin n) A) =
      Z.p Q (σ z) • (Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A) := fun Q => by
    rw [hm₁]; exact gU_mapMatrix_smul _ _ _
  have pσ : ∀ Q, Z.p Q z * Z.p Q (σ z) = 1 := fun Q => by rw [← map_mul, hzz, map_one]
  refine ⟨z, m₁, hzz, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm₁, smul_smul, hzz, one_smul]
  · show cT σ (m₁ : Matrix (Fin n) (Fin n) A) * _ * (m₁ : Matrix (Fin n) (Fin n) A) = _
    have hm' : cT σ (m : Matrix (Fin n) (Fin n) A) * ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *
        (m : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := hm
    rw [hm₁, gU_cT_smul, hσ, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hzz, one_smul, hm']
  · intro Q
    obtain ⟨cQ, xQ, hQ⟩ := hscal Q
    have h0 : Z.p Q (σ z) ≠ 0 := right_ne_zero_of_mul_eq_one (pσ Q)
    refine ⟨Units.mk0 _ h0 * cQ, xQ, ?_⟩
    show (Z.p Q).mapMatrix (m₁ : Matrix (Fin n) (Fin n) A) = _
    rw [pm, Units.val_mul, Units.val_mk0, ← smul_smul]
    exact congrArg _ hQ
  · intro Q h1 h2
    apply Units.ext
    show (Z.p Q).mapMatrix (m₁ : Matrix (Fin n) (Fin n) A) = (Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A)
    have e : Z.p Q (σ z) = 1 := by have := pσ Q; rwa [po Q h1 h2, one_mul] at this
    rw [pm, e, one_smul]
  · refine ⟨x, Units.ext ?_⟩
    show _ = (Z.p a).mapMatrix (m₁ : Matrix (Fin n) (Fin n) A)
    have e : Z.p a (σ z) = (c : Z.K a)⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← pa]; exact pσ a)).symm
    rw [pm, e, hc', smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]
  · refine ⟨y, Units.ext ?_⟩
    show _ = (Z.p a').mapMatrix (m₁ : Matrix (Fin n) (Fin n) A)
    have e : Z.p a' (σ z) = s c :=
      (inv_eq_of_mul_eq_one_right (by rw [← pa']; exact pσ a')).symm.trans (inv_inv _)
    rw [pm, e, hy, smul_smul, mul_inv_cancel₀ hsc, one_smul]

theorem gU_ind (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) {n : ℕ} (G : GL (Fin n) S) (T : Finset P) :
    ∀ (m : GL (Fin n) A), m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) →
      (∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m)) →
      (∀ Q, Q ∉ T → ∃ y : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y = bc (Z.p Q) m) →
      ∃ (z : A) (x : GL (Fin n) S), z * σ z = 1 ∧
        (m : Matrix (Fin n) (Fin n) A) = z • ((bc S.subtype x : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro m _ _ hg
    obtain ⟨x, hx⟩ := Z.gl_int (fun Q => hg Q (by simp))
    exact ⟨1, x, by rw [map_one, mul_one], by rw [hx, one_smul]⟩
  | @insert a T haT ih =>
    intro m hm hscal hg
    by_cases ha : ∃ y : GL (Fin n) (Z.O a), bc (Z.O a).subtype y = bc (Z.p a) m
    · exact ih m hm hscal fun Q hQ => by
        by_cases h : Q = a
        · subst h; exact ha
        · exact hg Q (by simp [h, hQ])
    · obtain ⟨a', ha'⟩ := Z.exists_bar hσ a
      by_cases hne : a = a'
      · exact absurd (gU_good_self Z hS (by rw [ha', ← hne]) G m hm (hscal a)) ha
      · obtain ⟨z, m₁, hzz, hmz, hm₁, hs₁, heq, hga, hga'⟩ := gU_step Z hσ hS G m hm hscal ha' hne
        obtain ⟨z₂, x, hz₂, hx⟩ := ih m₁ hm₁ hs₁ fun Q hQ => by
          by_cases h1 : Q = a
          · subst h1; exact hga
          by_cases h2 : Q = a'
          · subst h2; exact hga'
          rw [heq Q h1 h2]; exact hg Q (by simp [h1, hQ])
        refine ⟨z * z₂, x, ?_, ?_⟩
        · rw [map_mul, mul_mul_mul_comm, hzz, hz₂, one_mul]
        · rw [hmz, hx, smul_smul]

end GlobalTheory.LevNorm.PlaceSys

namespace GlobalTheory.LevNorm.PlaceSys

theorem unitary_locScal_glue : ∀ {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A), (∀ a, σ (σ a) = a) → (∀ a ∈ S, σ a ∈ S) → ∀ (n : ℕ) (G : GL (Fin n) S) (m : GL (Fin n) A), m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) → (∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m) ∨ ∃ Q', σ (Z.e Q') = Z.e Q ∧ IsScal (Z.O Q') (bc (Z.p Q') m)) → ∃ (z : A) (x : GL (Fin n) S), z * σ z = 1 ∧ (m : Matrix (Fin n) (Fin n) A) = z • ((bc S.subtype x : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  intro A _ S P k _ r Z σ hσ hS n G m hm hloc
  have hscal : ∀ Q, IsScal (Z.O Q) (bc (Z.p Q) m) := fun Q => by
    rcases hloc Q with h | ⟨Q', hQ', h⟩
    · exact h
    · obtain ⟨s, hs, hsO⟩ := Z.exists_conj hS hQ'
      obtain ⟨c, x, hc⟩ := h
      obtain ⟨y, hy⟩ := gU_scal_conj Z hs hsO G m hm c x hc
      have hsc : s c ≠ 0 := (map_ne_zero s).2 c.ne_zero
      exact ⟨(Units.mk0 _ hsc)⁻¹, y, by rw [Units.val_inv_eq_inv_val, Units.val_mk0]; exact hy⟩
  have hfin : {Q | ¬ ∃ y : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y = bc (Z.p Q) m}.Finite := by
    refine (Set.finite_iUnion (fun ij : Fin n × Fin n => (Z.fin ((m : Matrix (Fin n) (Fin n) A) ij.1 ij.2)).union
      (Z.fin (((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ij.1 ij.2)))).subset ?_
    intro Q hQ
    by_contra hc
    apply hQ
    have h1 : ∀ i j, Z.p Q ((m : Matrix (Fin n) (Fin n) A) i j) ∈ Z.O Q := fun i j =>
      by_contra fun h => hc (Set.mem_iUnion.2 ⟨(i, j), Or.inl h⟩)
    have h2 : ∀ i j, Z.p Q (((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) ∈ Z.O Q := fun i j =>
      by_contra fun h => hc (Set.mem_iUnion.2 ⟨(i, j), Or.inr h⟩)
    obtain ⟨y, hy⟩ := gU_glO _ ((Z.p Q).mapMatrix (m : Matrix (Fin n) (Fin n) A))
      ((Z.p Q).mapMatrix ((m⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) h1 h2
      (by rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
    exact ⟨y, Units.ext hy⟩
  exact gU_ind Z hσ hS G hfin.toFinset m hm hscal fun Q hQ => by
    by_contra h
    exact hQ (hfin.mem_toFinset.2 h)

end GlobalTheory.LevNorm.PlaceSys
