import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
import Formalism.LocalRingCardinality.ConjSqrtMinusD

noncomputable section

namespace GlobalTheory.InertIwasawa

section Algebra

open Matrix Formalism.UG GlobalTheory.Doubling

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

section Ring

variable {O : Type} [CommRing O] {s : O →+* O}

omit [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] in
theorem cT_cT (hs : ∀ x, s (s x) = x) (M : Matrix n ι O) : cT s (cT s M) = M := by
  ext i j; exact hs _

theorem exists_dual_isotropic (hs : ∀ x, s (s x) = x) {τ : O} (hτ : τ + s τ = 1) {Q : Matrix ι ι O} (hQ : cT s Q = Q)
    (hu : IsUnit Q) {Y : Matrix ι n O} {U : Matrix n ι O} (hU : U * Y = 1) (hY : cT s Y * Q * Y = 0) :
    ∃ Z : Matrix ι n O, cT s Y * Q * Z = 1 ∧ cT s Z * Q * Y = 1 ∧ cT s Z * Q * Z = 0 := by
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix ι n O, cT s Y * Q * Z = 1 :=
    ⟨(hu.unit⁻¹).1 * cT s U, by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hu.mul_val_inv, Matrix.one_mul, ← cT_mul, hU, cT_one]⟩
  have key : ∀ X X' : Matrix ι n O, cT s (cT s X * Q * X') = cT s X' * Q * X := fun X X' => by
    rw [cT_mul, cT_mul, cT_cT hs, hQ, Matrix.mul_assoc]
  have hZ' : cT s Z * Q * Y = 1 := by rw [← key, hZ, cT_one]
  set H := cT s Z * Q * Z with hH
  have h1 : cT s Y * Q * (Z - τ • (Y * H)) = 1 := by
    rw [Matrix.mul_sub, hZ, Matrix.mul_smul, ← Matrix.mul_assoc, hY, Matrix.zero_mul, smul_zero, sub_zero]
  refine ⟨Z - τ • (Y * H), h1, by rw [← key, h1, cT_one], ?_⟩
  have e : cT s (Z - τ • (Y * H)) = cT s Z - s τ • (H * cT s Y) := by
    have : H * cT s Y = cT s (Y * H) := by rw [cT_mul, hH, key]
    rw [this]
    generalize Y * H = X
    ext i j
    simp [cT]
  rw [e, Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc H, Matrix.mul_assoc H, h1,
    Matrix.mul_sub, ← hH, Matrix.mul_smul, ← Matrix.mul_assoc, hZ', Matrix.one_mul, Matrix.mul_one, sub_sub, ← add_smul,
    hτ, one_smul, sub_self]

theorem exists_hyperbolic (e : n ⊕ n ≃ ι) (hs : ∀ x, s (s x) = x) {τ : O} (hτ : τ + s τ = 1) {Q : Matrix ι ι O}
    (hQ : cT s Q = Q) (hu : IsUnit Q) {Y : Matrix ι n O} {U : Matrix n ι O} (hU : U * Y = 1)
    (hY : cT s Y * Q * Y = 0) :
    ∃ (T : Matrix ι (n ⊕ n) O) (S : Matrix (n ⊕ n) ι O), S * T = 1 ∧ T * S = 1 ∧
      cT s T * Q * T = fromBlocks 0 1 1 0 ∧ T * (fromRows 1 0 : Matrix (n ⊕ n) n O) = Y := by
  obtain ⟨Z, h1, h2, h3⟩ := exists_dual_isotropic hs hτ hQ hu hU hY
  have hT : cT s (fromCols Y Z) * Q * fromCols Y Z = fromBlocks 0 1 1 0 := by
    have : cT s (fromCols Y Z) = fromRows (cT s Y) (cT s Z) := by
      ext (i | i) j <;> rfl
    rw [this, fromRows_mul, fromRows_mul_fromCols, hY, h1, h2, h3]
  have hS : (fromBlocks 0 1 1 0 : Matrix (n ⊕ n) (n ⊕ n) O) * (cT s (fromCols Y Z) * Q) * fromCols Y Z =
      (1 : Matrix (n ⊕ n) (n ⊕ n) O) := by
    rw [Matrix.mul_assoc, hT, fromBlocks_multiply]
    simp
  exact ⟨_, _, hS, (mul_eq_one_comm_of_equiv e).1 hS, hT, by simp [fromCols_mul_fromRows]⟩

theorem exists_isometry (e : n ⊕ n ≃ ι) (hs : ∀ x, s (s x) = x) {τ : O} (hτ : τ + s τ = 1) {Q : Matrix ι ι O}
    (hQ : cT s Q = Q) (hu : IsUnit Q) {Y Y' : Matrix ι n O} {U U' : Matrix n ι O} (hU : U * Y = 1)
    (hY : cT s Y * Q * Y = 0) (hU' : U' * Y' = 1) (hY' : cT s Y' * Q * Y' = 0) :
    ∃ k ∈ UJ s Q, k.1 * Y' = Y := by
  obtain ⟨T, S, h1, h2, h3, h4⟩ := exists_hyperbolic e hs hτ hQ hu hU hY
  obtain ⟨T', S', h1', h2', h3', h4'⟩ := exists_hyperbolic e hs hτ hQ hu hU' hY'
  refine ⟨⟨T * S', T' * S, ?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S', h1', Matrix.one_mul, h2]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, h1, Matrix.one_mul, h2']
  · change cT s (T * S') * Q * (T * S') = Q
    calc cT s (T * S') * Q * (T * S') = cT s S' * (cT s T * Q * T) * S' := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT s (T' * S') * Q * (T' * S') := by
          rw [h3, ← h3', cT_mul]; simp only [Matrix.mul_assoc]
      _ = Q := by rw [h2', cT_one, Matrix.one_mul, Matrix.mul_one]
  · change T * S' * Y' = Y
    rw [← h4', Matrix.mul_assoc, ← Matrix.mul_assoc S', h1', Matrix.one_mul, h4]

end Ring

variable {A : Type} [CommRing A]

variable (A) in

def dCol (e : n ⊕ n ≃ ι) : Matrix ι n A := (fromRows 1 1 : Matrix (n ⊕ n) n A).submatrix e.symm id

variable (A) in

def fCol (e : n ⊕ n ≃ ι) : Matrix ι n A := (fromRows 1 0 : Matrix (n ⊕ n) n A).submatrix e.symm id

variable (e : n ⊕ n ≃ ι)

omit [Fintype ι] [DecidableEq ι] in
theorem dCol_mulVec (x : n → A) : dCol A e *ᵥ x = pairVec e x x := by
  funext j
  obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [dCol, mulVec, dotProduct, one_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem fCol_mulVec (x : n → A) : fCol A e *ᵥ x = pairVec e x 0 := by
  funext j
  obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [fCol, mulVec, dotProduct, one_apply]

omit [DecidableEq ι] in
theorem transpose_fCol_mul (M : Matrix (n ⊕ n) n A) : (fCol A e)ᵀ * M.submatrix e.symm id = M.toRows₁ := by
  ext i j
  simp [fCol, mul_apply, ← e.sum_comp, one_apply, toRows₁]

omit [Fintype n] [Fintype ι] [DecidableEq ι] in
theorem dCol_map {B : Type} [CommRing B] (f : A →+* B) : (dCol A e).map f = dCol B e := by
  ext j k
  obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [dCol, one_apply, apply_ite f]

omit [Fintype n] [Fintype ι] [DecidableEq ι] in
theorem fCol_map {B : Type} [CommRing B] (f : A →+* B) : (fCol A e).map f = fCol B e := by
  ext j k
  obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [fCol, one_apply, apply_ite f]

omit [DecidableEq ι] in
theorem dCol_isotropic (σ : A →+* A) (J : Matrix n n A) : cT σ (dCol A e) * dblGram e J * dCol A e = 0 := by
  rw [cT, dCol_map]
  ext i j
  simp [dCol, dblGram, blkMat, mul_apply, ← e.sum_comp, one_apply]

theorem keepsDiag_of_dCol {M : Matrix ι ι A} {c : Matrix n n A} (h : M * dCol A e = dCol A e * c) : KeepsDiag e M :=
  keepsDiag_of_mulVec fun w hw => by
    obtain ⟨x, rfl⟩ := (mem_diagSub e).1 hw
    rw [← dCol_mulVec, mulVec_mulVec, h, ← mulVec_mulVec, dCol_mulVec]
    exact (pairVec_mem_diagSub e).2 rfl

def HasFrames (O : Subring A) : Prop :=
  ∀ g : GL ι A, ∃ (k : GL ι O) (c : GL n A), g.1 * fCol A e = k.1.map O.subtype * fCol A e * c.1

theorem exists_std (O : Subring A) (hO : HasFrames e O) {σ : A →+* A} {s : O →+* O} (hσ : ∀ x : O, (s x : A) = σ x)
    (hs : ∀ x, s (s x) = x) {τ : O} (hτ : τ + s τ = 1) {J : Matrix n n O} (hJ : cT s J = J) (hu : IsUnit J)
    {h : GL ι A} (hh : h ∈ UJ σ (dblGram e (J.map O.subtype))) :
    ∃ k ∈ UJ s (dblGram e J), ∃ c : Matrix n n A, h.1 * dCol A e = k.1.map O.subtype * dCol A e * c := by
  have hc : ∀ {a b : Type} (M : Matrix a b O), cT σ (M.map O.subtype) = (cT s M).map O.subtype := fun M => by
    ext i j; exact (hσ _).symm
  have hd : dblGram e (J.map O.subtype) = (dblGram e J).map O.subtype := by
    rw [dblGram, dblGram, blkMat_map e _ (map_zero _), Matrix.map_neg _ (map_neg _)]
  let W : GL ι A := ⟨(fromBlocks 1 0 1 1 : Matrix (n ⊕ n) (n ⊕ n) A).submatrix e.symm e.symm,
    (fromBlocks 1 0 (-1) 1 : Matrix (n ⊕ n) (n ⊕ n) A).submatrix e.symm e.symm,
    by simp [submatrix_mul_equiv, fromBlocks_multiply], by simp [submatrix_mul_equiv, fromBlocks_multiply]⟩
  have hW : W.1 * fCol A e = dCol A e := by
    simp [W, fCol, dCol, submatrix_mul_equiv, fromBlocks_mul_fromRows]
  obtain ⟨k, c, hk⟩ := hO (h * W)
  rw [Units.val_mul, Matrix.mul_assoc, hW, ← fCol_map e O.subtype, ← Matrix.map_mul] at hk
  have h0 : cT s (k.1 * fCol O e) * dblGram e J * (k.1 * fCol O e) = 0 := by
    have h1 : (k.1 * fCol O e).map O.subtype = h.1 * (dCol A e * (c⁻¹).1) := by
      rw [← Matrix.mul_assoc, hk, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    apply Matrix.map_injective O.subtype_injective
    change Matrix.map _ O.subtype = Matrix.map _ O.subtype
    rw [Matrix.map_mul, Matrix.map_mul, ← hc, ← hd, h1, Matrix.map_zero _ (map_zero _)]
    calc _ = cT σ (c⁻¹).1 * (cT σ (dCol A e) * (cT σ h.1 * dblGram e (J.map O.subtype) * h.1) * dCol A e) * (c⁻¹).1 := by
          rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hh, dCol_isotropic, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨κ, h1, h2⟩ := exists_isometry e hs hτ (Q := dblGram e J)
    (by rw [dblGram, cT_blkMat, hJ, show cT s (-J) = -cT s J from by ext i j; simp [cT], hJ])
    (by rw [isUnit_iff_isUnit_det, dblGram, det_blkMat, ← det_mul, ← isUnit_iff_isUnit_det]; exact hu.mul hu.neg)
    (U := (fCol O e)ᵀ * (k⁻¹).1) (Y' := dCol O e) (U' := (fCol O e)ᵀ)
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (k⁻¹).1, Units.inv_mul, Matrix.one_mul]
        exact (transpose_fCol_mul e _).trans (by simp)) h0
    ((transpose_fCol_mul e _).trans (by simp)) (dCol_isotropic e s J)
  exact ⟨κ, h1, c.1, by rw [hk, ← h2, Matrix.map_mul, dCol_map]⟩

omit [Fintype n] [DecidableEq n] in
theorem mulVec_mem_iff (O : Subring A) (k : GL ι O) (y : ι → A) :
    (∀ i, y i ∈ O) ↔ ∀ i, (k.1.map O.subtype *ᵥ y) i ∈ O := by
  have key : ∀ (M : Matrix ι ι O) (y : ι → A), (∀ i, y i ∈ O) → ∀ i, (M.map O.subtype *ᵥ y) i ∈ O := fun M y hy i =>
    sum_mem fun j _ => mul_mem (M i j).2 (hy j)
  refine ⟨key _ y, fun h => ?_⟩
  have := key (k⁻¹).1 _ h
  rwa [mulVec_mulVec, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), one_mulVec] at this

omit [DecidableEq n] in
theorem hform_mulVec (σ : A →+* A) (M a : Matrix n n A) (x y : n → A) :
    hform σ M (a *ᵥ x) (a *ᵥ y) = (σ ∘ x) ⬝ᵥ ((cT σ a * M * a) *ᵥ y) := by
  have e : ∀ x y, hform σ M x y = (σ ∘ x) ⬝ᵥ (M *ᵥ y) := fun x y => by
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e' : σ ∘ (a *ᵥ x) = (σ ∘ x) ᵥ* cT σ a := by
    rw [cT, Matrix.vecMul_transpose]
    exact funext fun i => RingHom.map_mulVec σ a x i
  rw [e, e', ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem exists_gram (O : Subring A) {σ : A →+* A} (hσ : ∀ x ∈ O, σ x ∈ O) {J : Matrix n n A} (hu : IsUnit J)
    {Λ : Submodule O (n → A)} (hΛ : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, hform σ J x y ∈ O) {a : GL n A}
    (ha : ∀ y, (∀ i, y i ∈ O) ↔ a.1 *ᵥ y ∈ Λ) :
    ∃ B : Matrix n n O, IsUnit B ∧ B.map O.subtype = cT σ a.1 * J * a.1 := by
  set B := cT σ a.1 * J * a.1 with hB
  have hu' : IsUnit B := by
    refine (IsUnit.mul (IsUnit.of_mul_eq_one (cT σ (a⁻¹).1) ?_) hu).mul a.isUnit
    rw [← cT_mul, Units.inv_mul, cT_one]
  have hs : ∀ j i : n, (Pi.single j 1 : n → A) i ∈ O := fun j i => by
    by_cases e : i = j
    · subst e; simp
    · simp [e]
  have h1 : ∀ i j, B i j ∈ O := fun i j => by
    have := (hΛ _).1 ((ha _).1 (hs j)) _ ((ha _).1 (hs i))
    rw [hform_mulVec, ← hB, show σ ∘ Pi.single i 1 = Pi.single i 1 from funext fun k => by
      by_cases e : k = i
      · subst e; simp
      · simp [e]] at this
    simpa using this
  have h2 : ∀ i j, (hu'.unit⁻¹).1 i j ∈ O := fun i j => by
    have := (ha ((hu'.unit⁻¹).1 *ᵥ Pi.single j 1)).2 ((hΛ _).2 fun x hx => by
      have e : a.1 *ᵥ ((a⁻¹).1 *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have h1 := (ha _).2 (e.symm ▸ hx) j
      rw [← e, hform_mulVec, ← hB, Matrix.mulVec_mulVec, hu'.mul_val_inv, Matrix.one_mulVec, dotProduct_single, mul_one]
      exact hσ _ h1) i
    simpa using this
  refine ⟨Matrix.of fun i j => ⟨_, h1 i j⟩, IsUnit.of_mul_eq_one (Matrix.of fun i j => ⟨_, h2 i j⟩) ?_, rfl⟩
  apply Matrix.map_injective O.subtype_injective
  change Matrix.map _ O.subtype = Matrix.map _ O.subtype
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  exact hu'.mul_val_inv

theorem exists_stab (O : Subring A) (hO : HasFrames e O) {σ : A →+* A} (hσ : ∀ x ∈ O, σ x ∈ O)
    (hs : ∀ x, σ (σ x) = x) {τ : A} (hτO : τ ∈ O) (hτ : τ + σ τ = 1) {J : Matrix n n A} (hJ : cT σ J = J)
    (hu : IsUnit J) {Λ : Submodule O (n → A)} (hΛ : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, hform σ J x y ∈ O) {a : GL n A}
    (ha : ∀ y, (∀ i, y i ∈ O) ↔ a.1 *ᵥ y ∈ Λ) {g : GL ι A} (hg : g ∈ UJ σ (dblGram e J)) :
    ∃ k ∈ UJ σ (dblGram e J), k ∈ stabGL (sumLat e Λ Λ) ∧ g * k ∈ stabGL (diagSub A e) := by
  obtain ⟨B, hB, eB⟩ := exists_gram O hσ hu hΛ ha
  let s : O →+* O := σ.restrict O O hσ
  have hc : ∀ {a b : Type} (M : Matrix a b O), cT σ (M.map O.subtype) = (cT s M).map O.subtype := fun M => rfl
  have hd : dblGram e (B.map O.subtype) = (dblGram e B).map O.subtype := by
    rw [dblGram, dblGram, blkMat_map e _ (map_zero _), Matrix.map_neg _ (map_neg _)]
  set b := blkGL e (a, a) with hb
  have hQ : dblGram e (B.map O.subtype) = cT σ b.1 * dblGram e J * b.1 := by
    rw [eB, hb, val_blkGL, cT_blkMat, dblGram, dblGram, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul]
  have hconj : ∀ x : GL ι A, x ∈ UJ σ (dblGram e (B.map O.subtype)) ↔ b * x * b⁻¹ ∈ UJ σ (dblGram e J) := fun x => by
    have hub : IsUnit (cT σ b.1) := IsUnit.of_mul_eq_one (cT σ (b⁻¹).1) (by rw [← cT_mul, Units.inv_mul, cT_one])
    change cT σ x.1 * _ * x.1 = _ ↔ cT σ (b * x * b⁻¹).1 * _ * (b * x * b⁻¹).1 = _
    rw [hQ, ← hub.mul_right_inj (b := cT σ (b * x * b⁻¹).1 * _ * _), ← b.isUnit.mul_left_inj (b := cT σ b.1 * (_ * _))]
    refine Eq.congr ?_ rfl
    have : (b * x * b⁻¹).1 * b.1 = b.1 * x.1 := by rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
    calc _ = cT σ (b.1 * x.1) * dblGram e J * (b.1 * x.1) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [← this, cT_mul]; simp only [Matrix.mul_assoc]
  obtain ⟨k, hk, c, hkc⟩ := exists_std e O hO (σ := σ) (s := s) (fun _ => rfl) (fun x => Subtype.ext (hs x))
    (τ := ⟨τ, hτO⟩) (Subtype.ext hτ) (J := B) (by
      apply Matrix.map_injective O.subtype_injective
      change Matrix.map _ O.subtype = Matrix.map _ O.subtype
      rw [← hc, eB, cT_mul, cT_mul, cT_cT hs, hJ, Matrix.mul_assoc]) hB (h := b⁻¹ * g⁻¹ * b)
    ((hconj _).2 (by simpa [mul_assoc] using inv_mem hg))
  have hL : ∀ w : ι → A, (∀ i, w i ∈ O) ↔ b.1 *ᵥ w ∈ sumLat e Λ Λ := fun w => by
    rw [← pairVec_eta e w, hb, val_blkGL, blkMat_mulVec, pairVec_mem_sumLat, ← ha, ← ha, pairVec_eta]
    exact ⟨fun h => ⟨fun i => h _, fun i => h _⟩, fun h j => by
      obtain ⟨i | i, rfl⟩ := e.surjective j
      exacts [h.1 i, h.2 i]⟩
  have hbd : ∀ x : GL n A, (blkGL e (x, x)).1 * dCol A e = dCol A e * x.1 := fun x =>
    Matrix.ext_of_mulVec_single fun j => by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dCol_mulVec, dCol_mulVec, val_blkGL, blkMat_mulVec]
  refine ⟨b * bc O.subtype k * b⁻¹, (hconj _).1 ?_, fun w => ?_, ?_⟩
  · change cT σ (k.1.map O.subtype) * _ * k.1.map O.subtype = _
    rw [hc, hd, ← Matrix.map_mul, ← Matrix.map_mul, hk]
  · obtain ⟨w, rfl⟩ : ∃ w', w = b.1 *ᵥ w' := ⟨(b⁻¹).1 *ᵥ w, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← mulVec_mulVec, ← hL, ← hL]
    exact mulVec_mem_iff O k w
  · have hbP : b ∈ stabGL (diagSub A e) := mem_stabGL_diagSub.2 (keepsDiag_of_dCol e (hbd a))
    have : (bc O.subtype k)⁻¹ * (b⁻¹ * g⁻¹ * b) ∈ stabGL (diagSub A e) := by
      refine mem_stabGL_diagSub.2 (keepsDiag_of_dCol e (c := c) ?_)
      rw [Units.val_mul, Matrix.mul_assoc, hkc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      rw [show k.1.map O.subtype = (bc O.subtype k).1 from rfl, Units.inv_mul, Matrix.one_mul]
    convert mul_mem (mul_mem hbP (inv_mem this)) (inv_mem hbP) using 1
    group

theorem hasFrames_of_equiv {m : ℕ} (O : Subring A) {K : Type} [Field K] (V : ValuationSubring K) (φ : A ≃+* K)
    (hφ : ∀ y, y ∈ O ↔ φ y ∈ V) : HasFrames (finSumFinEquiv : Fin m ⊕ Fin m ≃ _) O := fun g => by
  obtain ⟨k, b, hb, hg⟩ := GlobalTheory.ValIwasawa.iwasawa V K (m + m) (bc φ.toRingHom g)
  let ψ : V →+* O := (φ.symm.toRingHom.comp V.subtype).codRestrict O fun x => (hφ _).2 (by simp)
  let b' := bc φ.symm.toRingHom b
  have h0 : (b'.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j
    change φ.symm (b.1 _ _) = 0
    rw [hb (by simp [Fin.lt_def]; omega), map_zero]
  have hu : IsUnit (b'.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ := by
    have := (isUnit_iff_isUnit_det _).1 b'.isUnit
    rw [← det_submatrix_equiv_self finSumFinEquiv, ← fromBlocks_toBlocks (b'.1.submatrix _ _), h0,
      det_fromBlocks_zero₂₁] at this
    exact (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left this)
  have h1 : g.1 = (bc ψ k).1.map O.subtype * b'.1 := by
    have := congrArg (fun x : GL (Fin (m + m)) K => x.1.map φ.symm.toRingHom) hg
    simp only [Units.val_mul, Matrix.map_mul] at this
    refine Eq.trans ?_ this
    ext i j
    exact (φ.symm_apply_apply _).symm
  refine ⟨bc ψ k, hu.unit, ?_⟩
  rw [h1, Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, fCol_mulVec, fCol_mulVec, mulVec_pairVec, h0]
  simp only [mulVec_zero, zero_mulVec, add_zero]
  rfl

end Algebra

section Place

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.LFun

theorem hasIwasawa_of_inert {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {c : 𝓞 E} (hc : (c : E) + σ c = 1) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hL : IsSelfDualAt σ J L v) : HasIwasawa σ Q (KFin σ Q L v) := fun g => by
  have h := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have eQ : JR (F := F) (Fv F v) Q = dblGram finSumFinEquiv (JR (Fv F v) J) := hQ ▸ JR_dblGram _ J
  obtain ⟨k, h1, h2, h3⟩ := exists_stab finSumFinEquiv (intLoc F E v)
    (hasFrames_of_equiv _ (w.adicCompletionIntegers E) (InertChart.complEquiv hw h) (InertChart.mem_intLoc_iff hw h))
    (σ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (fun _ => sigR_mem_intLoc σ) (sigR_invol hσ)
    (tmul_mem_intLoc (one_mem _) c)
    (by change (1 : Fv F v) ⊗ₜ[F] (c : E) + 1 ⊗ₜ[F] σ c = 1
        rw [← TensorProduct.tmul_add, hc]; rfl)
    (J := JR (Fv F v) J) (by ext i j; exact congrArg (fun x => (1 : Fv F v) ⊗ₜ[F] x) (hJ.1 i j))
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_JR hJ.2)) (Λ := latLoc F L v)
    (fun y => Submodule.ext_iff.1 hL y) (ha v) (g := matHom _ σ Q g) (eQ ▸ g.2)
  let κ : GLoc σ Q v := ⟨k, (eQ ▸ h1 : k ∈ Formalism.UG.UJ _ (JR (Fv F v) Q))⟩
  have hκ : κ ∈ KFin σ Q L v := by
    change k ∈ Formalism.UG.stabGL _
    rwa [latLoc_sumLat]
  exact ⟨⟨g * κ, h3⟩, κ⁻¹, inv_mem hκ, (mul_inv_cancel_right g κ).symm⟩

end Place

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hasIwasawa_inert : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v : FinPl D,
    ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v →
      HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
  intro D A L hL v hv
  haveI := hL.1
  have := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have hw : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPv.over.symm
  have hi := GlobalTheory.LPositivity.split_or_inert D w
  rw [hw] at hi
  obtain ⟨c, hc⟩ := D.host.exists_trace_one
  rw [← show D.sp.cm.sig (c : D.host.E) = D.host.conj c from D.host.φ₀.injective
    (((isCMExt_host D).2.2.2 _ _).trans (Formalism.HC.HostAx.conjE_apply _ _ _).symm)] at hc
  exact hasIwasawa_of_inert (GlobalTheory.LFun.InertChart.conj_conj (isCMExt_host D)) (c := c) hc (GlobalTheory.Doubling.isHermND_gram A)
    (gram_hdbl A) (hi.resolve_left hv)
    ((SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (GlobalTheory.Doubling.isHermND_gram A).2 hL.1).2 (fun y => hL.2 y) v)

end GlobalTheory.InertIwasawa

end
