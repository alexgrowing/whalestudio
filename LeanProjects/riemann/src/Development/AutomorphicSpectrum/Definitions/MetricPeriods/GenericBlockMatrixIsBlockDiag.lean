import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

section Minors

variable {R : Type} [CommRing R] {N : ℕ}

def minorIJ (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) : R :=
  if e : I.card = J.card then (h.submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl)).det else 0

def omIdx (N j : ℕ) : Finset (Fin N) := Finset.univ.filter fun a => (a : ℕ) < N - j

def wIdx (N j : ℕ) : Finset (Fin N) := Finset.univ.filter fun a => N - j ≤ (a : ℕ)

def IsBlockDiag (j : ℕ) (h : Matrix (Fin N) (Fin N) R) : Prop :=
  ∀ a b : Fin N, ¬ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) → h a b = 0

def IsProperStep (N j : ℕ) (i : Fin N) : Prop := (i : ℕ) + 1 ≠ j ∧ (i : ℕ) + 1 ≠ N

def stepCols (N j : ℕ) (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun a =>
    if (i : ℕ) + 1 ≤ j then N - j ≤ (a : ℕ) ∧ (a : ℕ) < N - j + ((i : ℕ) + 1) else (a : ℕ) < (i : ℕ) + 1 - j

def IsStepRows (N j : ℕ) (i : Fin N) (I : Finset (Fin N)) : Prop :=
  I.card = (stepCols N j i).card ∧ I ⊆ if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j

def detFac (j : ℕ) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) : R :=
  (if j ≤ (i : ℕ) + 1 then minorIJ T (wIdx N j) (wIdx N j) else 1) *
    if (i : ℕ) + 1 = N then minorIJ T (omIdx N j) (omIdx N j) else 1

open Classical in

def blockPot (j : ℕ) (i : Fin N) (G h : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (1 / 2) * Real.log (detFac j i G).re +
    if IsProperStep N j i then (1 / 2) * Real.log (minorIJ (hᴴ * G * h) (stepCols N j i) (stepCols N j i)).re else 0

def IsPeriodGram (j : ℕ) (Pi G : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  InFlagDomain N j Pi ∧ ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ k : ℕ,
    ‖(gramHead (sigForm N j) k (Pi * h)).det‖ =
      ‖((hᴴ * G * h).submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).det‖

end Minors

section Generic

variable {R : Type} [CommRing R] {N : ℕ} {Ψ : Type}

def IsLowerUni (L : Matrix (Fin N) (Fin N) R) : Prop :=
  (∀ a, L a a = 1) ∧ ∀ a b, a < b → L a b = 0

abbrev inertBlockIndex (Ψ : Type) (N j : ℕ) : Type :=
  {q : Ψ × Fin N × Fin N // ((q.2.1 : ℕ) < N - j ↔ (q.2.2 : ℕ) < N - j)}

abbrev LowIdx (Ψ : Type) (N j : ℕ) : Type :=
  {q : Ψ × Fin N × Fin N // q.2.2 < q.2.1 ∧ ((q.2.1 : ℕ) < N - j ↔ (q.2.2 : ℕ) < N - j)}

abbrev UpIdx (Ψ : Type) (N j : ℕ) : Type :=
  {q : Ψ × Fin N × Fin N // q.2.1 ≤ q.2.2 ∧ ((q.2.1 : ℕ) < N - j ↔ (q.2.2 : ℕ) < N - j)}

def IsGenericFlag (Ω : Type) [CommRing Ω] [Algebra Ω R] (j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) R) : Prop :=
  ∃ B : Ψ → Matrix (Fin N) (Fin N) R,
    (∀ τ, IsBlockDiag j (B τ) ∧ (B τ).BlockTriangular id ∧ IsLowerUni (g τ * B τ)) ∧
      AlgebraicIndependent Ω fun q : LowIdx Ψ N j => (g q.1.1 * B q.1.1) q.1.2.1 q.1.2.2

def genericBlockMatrix (R : Type) [CommRing R] (N j : ℕ) (τ : Ψ) : Matrix (Fin N) (Fin N) (MvPolynomial (inertBlockIndex Ψ N j) R) :=
  fun a b => if h : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then X ⟨(τ, a, b), h⟩ else 0

def genLow (R : Type) [CommRing R] (N j : ℕ) (τ : Ψ) : Matrix (Fin N) (Fin N) (MvPolynomial (LowIdx Ψ N j) R) :=
  fun a b => if h : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then X ⟨(τ, a, b), h⟩ else if a = b then 1 else 0

def genUp (R : Type) [CommRing R] (N j : ℕ) (τ : Ψ) : Matrix (Fin N) (Fin N) (MvPolynomial (UpIdx Ψ N j) R) :=
  fun a b => if h : a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then X ⟨(τ, a, b), h⟩ else 0

variable {j : ℕ} {S : Type} [CommRing S]

theorem isBlockDiag_one : IsBlockDiag j (1 : Matrix (Fin N) (Fin N) R) := fun a b h =>
  Matrix.one_apply_ne fun e => h (by rw [e])

theorem IsBlockDiag.mul {A B : Matrix (Fin N) (Fin N) R} (hA : IsBlockDiag j A) (hB : IsBlockDiag j B) :
    IsBlockDiag j (A * B) := fun a b h => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases e : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)
  · rw [hB c b fun e' => h (e.trans e'), mul_zero]
  · rw [hA a c e, zero_mul]

theorem IsBlockDiag.map {A : Matrix (Fin N) (Fin N) R} (hA : IsBlockDiag j A) (f : R →+* S) :
    IsBlockDiag j (A.map f) := fun a b h => by rw [Matrix.map_apply, hA a b h, map_zero]

theorem IsBlockDiag.inv {A : Matrix (Fin N) (Fin N) R} (hA : IsBlockDiag j A) (hd : IsUnit A.det) :
    IsBlockDiag j A⁻¹ := by
  letI := Matrix.invertibleOfIsUnitDet A hd
  let f : Fin N → ℕ := fun a => if (a : ℕ) < N - j then 0 else 1
  have h1 : A.BlockTriangular f := fun a b h => hA a b fun e => by
    simp only [f, e] at h; exact lt_irrefl _ h
  have h2 : A.BlockTriangular (OrderDual.toDual ∘ f) := fun a b h => hA a b fun e => by
    simp only [f, Function.comp, e] at h; exact lt_irrefl _ h
  intro a b h
  by_cases ha : (a : ℕ) < N - j
  · have hb : ¬ (b : ℕ) < N - j := fun hb => h (iff_of_true ha hb)
    exact blockTriangular_inv_of_blockTriangular h2 (show f a < f b by simp [f, ha, hb])
  · have hb : (b : ℕ) < N - j := by by_contra hb; exact h (iff_of_false ha hb)
    exact blockTriangular_inv_of_blockTriangular h1 (by simp [f, ha, hb])

theorem isLowerUni_one : IsLowerUni (1 : Matrix (Fin N) (Fin N) R) :=
  ⟨fun a => Matrix.one_apply_eq a, fun _ _ h => Matrix.one_apply_ne h.ne⟩

theorem IsLowerUni.map {L : Matrix (Fin N) (Fin N) R} (h : IsLowerUni L) (f : R →+* S) : IsLowerUni (L.map f) :=
  ⟨fun a => by rw [Matrix.map_apply, h.1, map_one], fun a b e => by rw [Matrix.map_apply, h.2 a b e, map_zero]⟩

theorem IsLowerUni.det_submatrix {L : Matrix (Fin N) (Fin N) R} (h : IsLowerUni L) (P : Fin N → Prop)
    [DecidablePred P] : (L.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det = 1 := by
  rw [det_of_lowerTriangular (L.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val) fun a b e => h.2 _ _ e]
  exact Finset.prod_eq_one fun a _ => h.1 _

theorem IsLowerUni.det {L : Matrix (Fin N) (Fin N) R} (h : IsLowerUni L) : L.det = 1 := by
  rw [det_of_lowerTriangular _ fun a b e => h.2 _ _ e]
  exact Finset.prod_eq_one fun a _ => h.1 _

theorem IsLowerUni.eq_one {L U : Matrix (Fin N) (Fin N) R} (h : IsLowerUni L) (hU : U.BlockTriangular id)
    (h' : IsLowerUni (L * U)) : U = 1 := by
  have hd : IsUnit L.det := by rw [h.det]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet L hd
  have h1 : L.BlockTriangular OrderDual.toDual := fun a b e => h.2 _ _ e
  have h2 : (L * U).BlockTriangular OrderDual.toDual := fun a b e => h'.2 _ _ e
  have h3 : U.BlockTriangular OrderDual.toDual := by
    have := (blockTriangular_inv_of_blockTriangular h1).mul h2
    rwa [Matrix.nonsing_inv_mul_cancel_left _ _ hd] at this
  have h4 : ∀ a b, a ≠ b → U a b = 0 := fun a b e => by
    rcases lt_or_gt_of_ne e with e | e
    · exact h3 e
    · exact hU e
  ext a b
  by_cases e : a = b
  · subst e
    have := h'.1 a
    rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [h4 c a hc, mul_zero]) (by simp), h.1,
      one_mul] at this
    rw [this, Matrix.one_apply_eq]
  · rw [h4 a b e, Matrix.one_apply_ne e]

theorem IsBlockDiag.exists_upper {G : Matrix (Fin N) (Fin N) R} (hG : IsBlockDiag j G)
    (hu : ∀ b : Fin N, IsUnit (G.submatrix
      (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det) :
    ∃ B, IsBlockDiag j B ∧ B.BlockTriangular id ∧ IsLowerUni (G * B) := by
  let P : Fin N → Fin N → Prop := fun b a => a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  let v : ∀ b, {a // P b a} → R := fun b c =>
    (G.submatrix (Subtype.val : {a // P b a} → Fin N) Subtype.val)⁻¹ c (⟨b, le_rfl, Iff.rfl⟩ : {a // P b a})
  let B : Matrix (Fin N) (Fin N) R := fun c b => if h : P b c then v b ⟨c, h⟩ else 0
  have key : ∀ a b, (G * B) a b = ∑ c : {c // P b c}, G a c * v b c := fun a b => by
    rw [Matrix.mul_apply, ← Finset.sum_filter_add_sum_filter_not Finset.univ (P b),
      Finset.sum_eq_zero (s := Finset.univ.filter fun c => ¬ P b c) (fun c hc => by
        rw [show B c b = 0 from dif_neg (Finset.mem_filter.1 hc).2, mul_zero]), add_zero,
      Finset.sum_subtype (p := P b) _ (by simp)]
    exact Finset.sum_congr rfl fun c _ => by rw [show B c b = v b c from dif_pos c.2]
  have key2 : ∀ a b (h : P b a), (G * B) a b = if a = b then 1 else 0 := fun a b h => by
    have := congrFun (congrFun (Matrix.mul_nonsing_inv _ (hu b)) ⟨a, h⟩) ⟨b, le_rfl, Iff.rfl⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [key]
    refine this.trans ?_
    simp [Subtype.ext_iff]
  refine ⟨B, fun a b h => dif_neg fun e => h e.2, fun a b h => dif_neg fun e => absurd e.1 (not_le.2 h),
    fun a => by rw [key2 a a ⟨le_rfl, Iff.rfl⟩, if_pos rfl], fun a b h => ?_⟩
  by_cases e : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · rw [key2 a b ⟨h.le, e⟩, if_neg h.ne]
  · rw [key]
    exact Finset.sum_eq_zero fun c _ => by rw [hG a c fun e' => e (e'.trans c.2.2), zero_mul]

theorem generic_block_matrix_isBlockDiag (τ : Ψ) : IsBlockDiag j (genericBlockMatrix R N j τ) := fun _ _ h => dif_neg h

theorem genLow_blockDiag (τ : Ψ) : IsBlockDiag j (genLow R N j τ) := fun a b h =>
  (dif_neg fun e => h e.2).trans (if_neg fun e => h (by rw [e]))

theorem genLow_lowerUni (τ : Ψ) : IsLowerUni (genLow R N j τ) :=
  ⟨fun _ => (dif_neg fun e => lt_irrefl _ e.1).trans (if_pos rfl),
    fun _ _ h => (dif_neg fun e => lt_asymm h e.1).trans (if_neg h.ne)⟩

theorem genLow_apply (q : LowIdx Ψ N j) : genLow R N j q.1.1 q.1.2.1 q.1.2.2 = X q := dif_pos q.2

theorem generic_block_matrix_apply (q : inertBlockIndex Ψ N j) : genericBlockMatrix R N j q.1.1 q.1.2.1 q.1.2.2 = X q := dif_pos q.2

theorem genUp_apply (q : UpIdx Ψ N j) : genUp R N j q.1.1 q.1.2.1 q.1.2.2 = X q := dif_pos q.2

theorem genUp_blockDiag (τ : Ψ) : IsBlockDiag j (genUp R N j τ) := fun _ _ h => dif_neg fun e => h e.2

theorem genUp_upper (τ : Ψ) : (genUp R N j τ).BlockTriangular id := fun _ _ h =>
  dif_neg fun e => absurd e.1 (not_le.2 h)

theorem generic_block_matrix_map (f : MvPolynomial (inertBlockIndex Ψ N j) R →+* S) {H : Ψ → Matrix (Fin N) (Fin N) S}
    (hH : ∀ τ, IsBlockDiag j (H τ)) (hf : ∀ q, f (X q) = H q.1.1 q.1.2.1 q.1.2.2) (τ : Ψ) :
    (genericBlockMatrix R N j τ).map f = H τ := by
  ext a b
  rw [Matrix.map_apply, genericBlockMatrix]
  split_ifs with h
  · exact hf _
  · rw [map_zero, hH τ a b h]

theorem genLow_map (f : MvPolynomial (LowIdx Ψ N j) R →+* S) {H : Ψ → Matrix (Fin N) (Fin N) S}
    (hH : ∀ τ, IsBlockDiag j (H τ) ∧ IsLowerUni (H τ)) (hf : ∀ q, f (X q) = H q.1.1 q.1.2.1 q.1.2.2) (τ : Ψ) :
    (genLow R N j τ).map f = H τ := by
  ext a b
  rw [Matrix.map_apply, genLow]
  split_ifs with h e
  · exact hf _
  · rw [map_one, e, (hH τ).2.1]
  · rw [map_zero]
    rcases lt_or_gt_of_ne e with e | e
    · exact ((hH τ).2.2 a b e).symm
    · exact ((hH τ).1 a b fun e' => h ⟨e, e'⟩).symm

theorem genUp_map (f : MvPolynomial (UpIdx Ψ N j) R →+* S) {H : Ψ → Matrix (Fin N) (Fin N) S}
    (hH : ∀ τ, IsBlockDiag j (H τ) ∧ (H τ).BlockTriangular id) (hf : ∀ q, f (X q) = H q.1.1 q.1.2.1 q.1.2.2)
    (τ : Ψ) : (genUp R N j τ).map f = H τ := by
  ext a b
  rw [Matrix.map_apply, genUp]
  split_ifs with h
  · exact hf _
  · rw [map_zero]
    by_cases e : a ≤ b
    · exact ((hH τ).1 a b fun e' => h ⟨e, e'⟩).symm
    · exact ((hH τ).2 (not_le.1 e)).symm

theorem IsGenericFlag.of_lowerUni {Ω : Type} [CommRing Ω] [Algebra Ω R] {g : Ψ → Matrix (Fin N) (Fin N) R}
    (hg : ∀ τ, IsLowerUni (g τ)) (h : AlgebraicIndependent Ω fun q : LowIdx Ψ N j => g q.1.1 q.1.2.1 q.1.2.2) :
    IsGenericFlag Ω j g :=
  ⟨fun _ => 1, fun τ => ⟨isBlockDiag_one, blockTriangular_one, by rw [mul_one]; exact hg τ⟩,
    by simpa only [mul_one] using h⟩

theorem IsGenericFlag.isUnit_det {Ω : Type} [CommRing Ω] [Algebra Ω R] {g : Ψ → Matrix (Fin N) (Fin N) R}
    (h : IsGenericFlag Ω j g) (τ : Ψ) : IsUnit (g τ).det := by
  obtain ⟨B, hB, -⟩ := h
  exact IsUnit.of_mul_eq_one (B τ).det (by rw [← det_mul, (hB τ).2.2.det])

theorem exists_univ_decomp (Ω : Type) [Field Ω] (Ψ : Type) (N j : ℕ) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra Ω T) (i : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] T)
      (ψ : T →ₐ[Ω] MvPolynomial (LowIdx Ψ N j) Ω) (B : Ψ → Matrix (Fin N) (Fin N) T), Function.Injective i ∧
      (∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (ev : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] Φ), Function.Injective ev →
        ∃ e : T →ₐ[Ω] Φ, Function.Injective e ∧ ∀ a, e (i a) = ev a) ∧
      ∀ τ, IsBlockDiag j (B τ) ∧ (B τ).BlockTriangular id ∧ IsLowerUni ((genericBlockMatrix Ω N j τ).map i.toRingHom * B τ) ∧
        ((genericBlockMatrix Ω N j τ).map i.toRingHom * B τ).map ψ.toRingHom = genLow Ω N j τ := by
  let A := MvPolynomial (inertBlockIndex Ψ N j) Ω
  let ψ₀ : A →ₐ[Ω] MvPolynomial (LowIdx Ψ N j) Ω := aeval fun q => genLow Ω N j q.1.1 q.1.2.1 q.1.2.2
  have h₀ : ∀ τ, (genericBlockMatrix Ω N j τ).map ψ₀.toRingHom = genLow Ω N j τ :=
    generic_block_matrix_map _ genLow_blockDiag fun q => aeval_X _ q
  let M : Submonoid A := (IsUnit.submonoid _).comap ψ₀
  have hM : ∀ m : M, (m : A) ≠ 0 := fun m e => by
    have : IsUnit (ψ₀ m) := m.2
    rw [e, map_zero] at this
    exact not_isUnit_zero this
  let T := Localization M
  let i : A →ₐ[Ω] T := IsScalarTower.toAlgHom Ω A T
  let ψ : T →ₐ[Ω] MvPolynomial (LowIdx Ψ N j) Ω := IsLocalization.liftAlgHom (M := M) (f := ψ₀) fun m => m.2
  have hψ : ∀ a, ψ (i a) = ψ₀ a := fun a => IsLocalization.lift_eq _ a
  have hi : Function.Injective i :=
    IsLocalization.injective T (M := M) fun m hm => mem_nonZeroDivisors_of_ne_zero (hM ⟨m, hm⟩)
  have hB : ∀ τ : Ψ, ∃ B, IsBlockDiag j B ∧ B.BlockTriangular id ∧
      IsLowerUni ((genericBlockMatrix Ω N j τ).map i.toRingHom * B) := fun τ => by
    refine ((generic_block_matrix_isBlockDiag τ).map _).exists_upper fun b => ?_
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine IsLocalization.map_units T (M := M) ⟨_, ?_⟩
    show IsUnit (ψ₀.toRingHom (Matrix.det _))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, h₀, (genLow_lowerUni τ).det_submatrix]
    exact isUnit_one
  choose B hB using hB
  refine ⟨T, inferInstance, inferInstance, i, ψ, B, hi, fun Φ _ _ ev hev => ?_,
    fun τ => ⟨(hB τ).1, (hB τ).2.1, (hB τ).2.2, ?_⟩⟩
  · have hu : ∀ m : M, IsUnit (ev m) := fun m => ((map_ne_zero_iff ev hev).2 (hM m)).isUnit
    refine ⟨IsLocalization.liftAlgHom (M := M) (f := ev) hu, ?_, fun a => IsLocalization.lift_eq _ a⟩
    exact (IsLocalization.lift_injective_iff (g := ev.toRingHom) hu).2 fun x y =>
      ⟨fun h => congrArg ev (hi h), fun h => congrArg i (hev h)⟩
  · have e : ((genericBlockMatrix Ω N j τ).map i.toRingHom).map ψ.toRingHom = genLow Ω N j τ := by
      rw [← h₀]; ext1 a b; exact hψ _
    have h1 := (hB τ).2.2.map ψ.toRingHom
    rw [Matrix.map_mul, e] at h1 ⊢
    rw [(genLow_lowerUni τ).eq_one ((hB τ).2.1.map _) h1, mul_one]

theorem IsGenericFlag.of_indep {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] {g : Ψ → Matrix (Fin N) (Fin N) Φ}
    (hg : ∀ τ, IsBlockDiag j (g τ))
    (h : AlgebraicIndependent Ω fun q : inertBlockIndex Ψ N j => g q.1.1 q.1.2.1 q.1.2.2) : IsGenericFlag Ω j g := by
  obtain ⟨T, _, _, i, ψ, B, -, he, hB⟩ := exists_univ_decomp Ω Ψ N j
  obtain ⟨e, he, hei⟩ := he Φ _ h
  have h1 : ∀ τ, g τ * (B τ).map e.toRingHom = ((genericBlockMatrix Ω N j τ).map i.toRingHom * B τ).map e.toRingHom := fun τ => by
    rw [Matrix.map_mul, ← generic_block_matrix_map (e.toRingHom.comp i.toRingHom) hg (fun q => (hei _).trans (aeval_X _ q)) τ]
    rfl
  refine ⟨fun τ => (B τ).map e.toRingHom, fun τ => ⟨(hB τ).1.map _, (hB τ).2.1.map _, ?_⟩, ?_⟩
  · rw [h1]; exact (hB τ).2.2.1.map _
  · simp only [h1]
    refine AlgebraicIndependent.map' (f := e)
      (x := fun q : LowIdx Ψ N j => ((genericBlockMatrix Ω N j q.1.1).map i.toRingHom * B q.1.1) q.1.2.1 q.1.2.2) ?_ he
    refine AlgebraicIndependent.of_comp ψ ?_
    convert MvPolynomial.algebraicIndependent_X (LowIdx Ψ N j) Ω using 1
    funext q
    exact (congrFun (congrFun (hB q.1.1).2.2.2 _) _).trans (genLow_apply q)

theorem IsGenericFlag.indep_mul_genUp {Ω Φ : Type} [Field Ω] [CommRing Φ] [Algebra Ω Φ]
    {g : Ψ → Matrix (Fin N) (Fin N) Φ} (hg : ∀ τ, IsBlockDiag j (g τ)) (h : IsGenericFlag Ω j g) :
    AlgebraicIndependent Ω fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2 := by
  obtain ⟨T, _, _, i, ψ', B', hi, -, hB'⟩ := exists_univ_decomp Ω Ψ N j
  obtain ⟨B, hB, h⟩ := h
  let A := MvPolynomial (LowIdx Ψ N j) Ω
  let θ : MvPolynomial (UpIdx Ψ N j) Φ →ₐ[Φ] MvPolynomial (UpIdx Ψ N j) Φ :=
    aeval fun q => ((B q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2
  have hθ : ∀ τ, (genUp Φ N j τ).map θ.toRingHom = (B τ).map C * genUp Φ N j τ :=
    genUp_map _ (fun τ => ⟨((hB τ).1.map _).mul (genUp_blockDiag τ), ((hB τ).2.1.map _).mul (genUp_upper τ)⟩)
      fun q => aeval_X _ q
  let ev : A →ₐ[Ω] Φ := aeval fun q => (g q.1.1 * B q.1.1) q.1.2.1 q.1.2.2
  have hev : ∀ τ, (genLow Ω N j τ).map ev.toRingHom = g τ * B τ :=
    genLow_map _ (fun τ => ⟨(hg τ).mul (hB τ).1, (hB τ).2.2⟩) fun q => aeval_X _ q
  let μ : MvPolynomial (UpIdx Ψ N j) A →ₐ[Ω] MvPolynomial (UpIdx Ψ N j) Φ := MvPolynomial.mapAlgHom ev
  have hμ : Function.Injective μ := MvPolynomial.map_injective ev.toRingHom h
  have hd : ∀ τ, IsUnit (B' τ).det := fun τ =>
    IsUnit.of_mul_eq_one_right _ (by rw [← det_mul, (hB' τ).2.2.1.det])
  let lo : A →ₐ[Ω] T := aeval fun q => ((genericBlockMatrix Ω N j q.1.1).map i.toRingHom * B' q.1.1) q.1.2.1 q.1.2.2
  have hlo : ∀ τ, (genLow Ω N j τ).map lo.toRingHom = (genericBlockMatrix Ω N j τ).map i.toRingHom * B' τ :=
    genLow_map _ (fun τ => ⟨((generic_block_matrix_isBlockDiag τ).map _).mul (hB' τ).1, (hB' τ).2.2.1⟩) fun q => aeval_X _ q
  let ν : MvPolynomial (UpIdx Ψ N j) A →ₐ[Ω] T := aevalTower lo fun q => (B' q.1.1)⁻¹ q.1.2.1 q.1.2.2
  have hν : ∀ τ, (genUp A N j τ).map ν.toRingHom = (B' τ)⁻¹ :=
    genUp_map _ (fun τ => ⟨(hB' τ).1.inv (hd τ), by
      letI := Matrix.invertibleOfIsUnitDet _ (hd τ)
      exact blockTriangular_inv_of_blockTriangular (hB' τ).2.1⟩) fun q => aevalTower_X _ _ q
  let Z : Ψ → Matrix (Fin N) (Fin N) (MvPolynomial (UpIdx Ψ N j) A) := fun τ =>
    (genLow Ω N j τ).map (C : A →+* _) * genUp A N j τ
  have h1 : AlgebraicIndependent Ω fun q : inertBlockIndex Ψ N j => Z q.1.1 q.1.2.1 q.1.2.2 := by
    refine AlgebraicIndependent.of_comp ν ?_
    convert (MvPolynomial.algebraicIndependent_X (inertBlockIndex Ψ N j) Ω).map' (f := i) hi using 1
    funext q
    have : (Z q.1.1).map ν.toRingHom = (genericBlockMatrix Ω N j q.1.1).map i.toRingHom := by
      rw [Matrix.map_mul, hν, show ((genLow Ω N j q.1.1).map (C : A →+* _)).map ν.toRingHom =
        (genLow Ω N j q.1.1).map lo.toRingHom from Matrix.ext fun a b => aevalTower_C _ _ _, hlo,
        Matrix.mul_nonsing_inv_cancel_right _ _ (hd _)]
    exact (congrFun (congrFun this _) _).trans (congrArg i (generic_block_matrix_apply q))
  refine AlgebraicIndependent.of_comp (θ.restrictScalars Ω) ?_
  convert h1.map' (f := μ) hμ using 1
  funext q
  have : ((g q.1.1).map C * genUp Φ N j q.1.1).map θ.toRingHom = (Z q.1.1).map μ.toRingHom := by
    rw [Matrix.map_mul, Matrix.map_mul, hθ, ← Matrix.mul_assoc,
      genUp_map μ.toRingHom (H := genUp Φ N j) (fun τ => ⟨genUp_blockDiag τ, genUp_upper τ⟩)
        (fun q => (map_X _ q).trans (genUp_apply q).symm),
      show ((g q.1.1).map C).map θ.toRingHom = (g q.1.1).map C from Matrix.ext fun a b => aeval_C _ _,
      ← Matrix.map_mul, ← hev]
    congr 1
    exact Matrix.ext fun a b => (MvPolynomial.map_C ev.toRingHom (genLow Ω N j q.1.1 a b)).symm
  exact congrFun (congrFun this _) _

end Generic

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def RegAt {Ω : Type} [Field Ω] (x : (Σ k, ι k) → Ω) (Q : Ideal (MRing ι)) (s : Ω) : Prop :=
  ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ h ∉ Q ∧ aeval x g = s * aeval x h

abbrev NonPluckerBlocks {σ : Type} (blk : σ → Option K) : Type := {k : K // ∀ p, blk p ≠ some k}

instance {σ : Type} (blk : σ → Option K) : Fintype (NonPluckerBlocks blk) := Fintype.ofFinite _

abbrev baseIdx (ι : K → Type) {σ : Type} (blk : σ → Option K) : NonPluckerBlocks blk → Type := fun k => ι k.1

def basePart {σ F : Type} (blk : σ → Option K) (z : (Σ k, ι k) → F) : (Σ k, baseIdx ι blk k) → F :=
  fun q => z ⟨q.1.1, q.2⟩

structure FrameData (ι : K → Type) (Ψ : Type) (N : ℕ) (Ω : Type) (blk : Ψ × Fin N → Option K) where

  c : ∀ k, baseIdx ι blk k

  T : Ψ → Matrix (Fin N) (Fin N) Ω

  u : (Σ k, ι k) → Finset (Fin N) → Ω

  u' : Finset (Fin N) → (Σ k, ι k) → Ω

  υ : Ψ × Fin N → Ω

structure FlagModel {Φ : Type} [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) where
  j_le : j ≤ N

  Ω : Type
  [fieldΩ : Field Ω]
  [charΩ : CharZero Ω]
  [alg : Algebra Ω Φ]

  blk : Ψ × Fin N → Option K
  blk_none : ∀ p, blk p = none ↔ ¬ IsProperStep N j p.2
  blk_inj : ∀ p p' k, blk p = some k → blk p' = some k → p = p'

  x : (Σ k, baseIdx ι blk k) → Ω

  x_ne : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0
  y_base : ∀ q, basePart blk y q = algebraMap Ω Φ (x q)

  g : Ψ → Matrix (Fin N) (Fin N) Φ
  g_block : ∀ τ, IsBlockDiag j (g τ)

  g_indep : IsGenericFlag Ω j g

  coef : (Σ k, ι k) → Finset (Fin N) → Ω
  y_step : ∀ p k, blk p = some k → ∀ m : ι k,
    y ⟨k, m⟩ = ∑ I, algebraMap Ω Φ (coef ⟨k, m⟩ I) * minorIJ (g p.1) I (stepCols N j p.2)

  b : Ψ × Fin N → NonPluckerBlocks blk → ℤ

  lam : Ψ × Fin N → Ω
  frames : ∀ Q : Ideal (MRing (baseIdx ι blk)), Q.IsPrime → IsRelevant Q → mCoordIdeal x ≤ Q →
    ∃ F : FrameData ι Ψ N Ω blk,
      ((∀ τ, IsBlockDiag j (F.T τ) ∧ (F.T τ).det ≠ 0) ∧
      (∀ p k, blk p = some k → ∀ (m : ι k) (h : Matrix (Fin N) (Fin N) Ω), IsBlockDiag j h →
        detFac j p.2 (F.T p.1) * ∑ I, coef ⟨k, m⟩ I * minorIJ (F.T p.1 * h) I (stepCols N j p.2) =
          (∏ k', x ⟨k', F.c k'⟩ ^ b p k') * ∑ I, F.u ⟨k, m⟩ I * minorIJ h I (stepCols N j p.2)) ∧
      (∀ p k, blk p = some k → ∀ I I', IsStepRows N j p.2 I → IsStepRows N j p.2 I' →
        ∑ m : ι k, F.u' I ⟨k, m⟩ * F.u ⟨k, m⟩ I' = if I = I' then 1 else 0) ∧
      ∀ p, blk p = none → detFac j p.2 (F.T p.1) * lam p = (∏ k', x ⟨k', F.c k'⟩ ^ b p k') * F.υ p) ∧
      ((∀ k, (X ⟨k, F.c k⟩ : MRing (baseIdx ι blk)) ∉ Q) ∧ (∀ q I, RegAt x Q (F.u q I) ∧ RegAt x Q (F.u' I q)) ∧
        ∀ p, blk p = none → F.υ p ≠ 0 ∧ RegAt x Q (F.υ p) ∧ RegAt x Q (F.υ p)⁻¹)

attribute [instance] FlagModel.fieldΩ FlagModel.charΩ FlagModel.alg

namespace FlagModel

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)

def IsFrame (F : FrameData ι Ψ N M.Ω M.blk) : Prop :=
  (∀ τ, IsBlockDiag j (F.T τ) ∧ (F.T τ).det ≠ 0) ∧
  (∀ p k, M.blk p = some k → ∀ (m : ι k) (h : Matrix (Fin N) (Fin N) M.Ω), IsBlockDiag j h →
    detFac j p.2 (F.T p.1) * ∑ I, M.coef ⟨k, m⟩ I * minorIJ (F.T p.1 * h) I (stepCols N j p.2) =
      (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, F.u ⟨k, m⟩ I * minorIJ h I (stepCols N j p.2)) ∧
  (∀ p k, M.blk p = some k → ∀ I I', IsStepRows N j p.2 I → IsStepRows N j p.2 I' →
    ∑ m : ι k, F.u' I ⟨k, m⟩ * F.u ⟨k, m⟩ I' = if I = I' then 1 else 0) ∧
  ∀ p, M.blk p = none → detFac j p.2 (F.T p.1) * M.lam p = (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * F.υ p

def GoodAt (F : FrameData ι Ψ N M.Ω M.blk) (Q : Ideal (MRing (baseIdx ι M.blk))) : Prop :=
  (∀ k, (X ⟨k, F.c k⟩ : MRing (baseIdx ι M.blk)) ∉ Q) ∧ (∀ q I, RegAt M.x Q (F.u q I) ∧ RegAt M.x Q (F.u' I q)) ∧
    ∀ p, M.blk p = none → F.υ p ≠ 0 ∧ RegAt M.x Q (F.υ p) ∧ RegAt M.x Q (F.υ p)⁻¹

open Classical in

def dy (p : Ψ × Fin N) : K → ℤ := fun k =>
  if h : ∀ p', M.blk p' ≠ some k then -M.b p ⟨k, h⟩ else if M.blk p = some k then 1 else 0

def IsFlagOf (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) ∧ (∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) ∧
    ∀ p k, M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k,
      z ⟨k, m⟩ = a * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z) * minorIJ (h p.1) I (stepCols N j p.2)

def IsInducedAt (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (p : Ψ × Fin N)
    (G : Matrix (Fin N) (Fin N) ℂ) (A : HermLine ι) : Prop :=
  ∀ z ∈ mcPts (mCoordIdeal y), SameOrbit (basePart M.blk z) zb → (∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) →
    ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → h.det ≠ 0 →
      (∀ k, M.blk p = some k → (∀ m : ι k, z ⟨k, m⟩ =
          ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z) * minorIJ h I (stepCols N j p.2)) →
        Real.log (A.h z) = blockPot j p.2 G h) ∧
      (M.blk p = none → Real.log (A.h z) = blockPot j p.2 G h - Real.log ‖valAt M.x (F.υ p) (basePart M.blk z)‖)

def OnStep (p : Ψ × Fin N) (A : HermLine ι) : Prop :=
  ∀ z z' : (Σ k, ι k) → ℂ, basePart M.blk z = basePart M.blk z' →
    (∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = z' ⟨k, m⟩) → A.h z = A.h z'

def wCo (p : Ψ × Fin N) (k₀ : K) (a a' : Fin N) (t : RatFunc Φ) :
    (Σ o : Option K, ι (o.getD k₀)) → RatFunc Φ
  | ⟨some k, m⟩ => algebraMap Φ (RatFunc Φ) (y ⟨k, m⟩)
  | ⟨none, m⟩ => ∑ I, algebraMap Φ (RatFunc Φ) (algebraMap M.Ω Φ (M.coef ⟨k₀, m⟩ I)) *
      minorIJ ((M.g p.1).map (algebraMap Φ (RatFunc Φ)) * (1 + Matrix.single a' a t)) I (stepCols N j p.2)

theorem isRelevant_alt : IsRelevant (mCoordIdeal M.x) := fun k => by
  obtain ⟨i, hi⟩ := M.x_ne k
  refine ⟨i, fun h => hi ?_⟩
  have h' : mConeMap M.x (X ⟨k, i⟩) = 0 := h
  rw [mConeMap, aeval_X] at h'
  exact C_eq_zero.1 ((mul_eq_zero.1 h').resolve_right (X_ne_zero _))

theorem isPrime_alt : (mCoordIdeal M.x).IsPrime := RingHom.ker_isPrime _

theorem exists_frame : ∃ F : FrameData ι Ψ N M.Ω M.blk, M.IsFrame F ∧ M.GoodAt F (mCoordIdeal M.x) :=
  M.frames _ M.isPrime_alt M.isRelevant_alt le_rfl

theorem x_chart_ne {F : FrameData ι Ψ N M.Ω M.blk} {Q : Ideal (MRing (baseIdx ι M.blk))} (hQ : mCoordIdeal M.x ≤ Q)
    (hF : M.GoodAt F Q) (k : NonPluckerBlocks M.blk) : M.x ⟨k, F.c k⟩ ≠ 0 := fun h => hF.1 k (hQ (by
  show mConeMap M.x (X ⟨k, F.c k⟩) = 0
  rw [mConeMap, aeval_X, h, map_zero, zero_mul]))

theorem lam_ne_zero (p : Ψ × Fin N) (hp : M.blk p = none) : M.lam p ≠ 0 := by
  obtain ⟨F, hF, hG⟩ := M.exists_frame
  intro h0
  have h := hF.2.2.2 p hp
  rw [h0, mul_zero] at h
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (M.x_chart_ne le_rfl hG k))
    (hG.2.2 p hp).1 h.symm

theorem isUnit_det_g (τ : Ψ) : IsUnit (M.g τ).det := M.g_indep.isUnit_det τ

end FlagModel

def lastCol (N j : ℕ) (i : Fin N) : ℕ := if (i : ℕ) + 1 ≤ j then N - j + i else (i : ℕ) - j

namespace FlagEx

abbrev ιH : Bool → Type := fun _ => Fin 3

def blkH : Unit × Fin 2 → Option Bool := fun p => if p.2 = 0 then some true else none

theorem blkH_some {p : Unit × Fin 2} {k : Bool} (h : blkH p = some k) : p = ((), 0) ∧ k = true := by
  obtain ⟨⟨⟩, i⟩ := p
  fin_cases i
  · exact ⟨rfl, (Option.some_injective _ h).symm⟩
  · exact absurd h (by simp [blkH])

theorem blkH_none {p : Unit × Fin 2} (h : blkH p = none) : p = ((), 1) := by
  obtain ⟨⟨⟩, i⟩ := p
  fin_cases i
  · exact absurd h (by simp [blkH])
  · rfl

def bb : NonPluckerBlocks blkH := ⟨false, fun p h => by simpa using (blkH_some h).2⟩

instance : Unique (NonPluckerBlocks blkH) where
  default := bb
  uniq k := Subtype.ext (by
    rcases hk : k.1
    · rfl
    · exact absurd hk fun e => k.2 ((), 0) (by rw [e]; rfl))

variable (Ω : Type) [Field Ω] [CharZero Ω]

abbrev ΦH : Type := FractionRing (MvPolynomial (LowIdx Unit 2 2) Ω)

def gH : Unit → Matrix (Fin 2) (Fin 2) (ΦH Ω) := fun τ =>
  (genLow Ω 2 2 τ).map (algebraMap (MvPolynomial (LowIdx Unit 2 2) Ω) (ΦH Ω))

def coefH (x : Fin 3 → Ω) : (Σ k, ιH k) → Finset (Fin 2) → Ω := fun q I =>
  if q.1 then (if q.2 = 2 then (if I = {1} then 1 else 0) else if I = {0} then x q.2 else 0) else 0

def yH (x : Fin 3 → Ω) : (Σ k, ιH k) → ΦH Ω := fun q =>
  if q.1 then ∑ I, algebraMap Ω (ΦH Ω) (coefH Ω x q I) * minorIJ (gH Ω ()) I (stepCols 2 2 0)
  else algebraMap Ω (ΦH Ω) (x q.2)

theorem minor_single {R : Type} [CommRing R] (h : Matrix (Fin 2) (Fin 2) R) (a b : Fin 2) :
    minorIJ h {a} {b} = h a b := by
  unfold minorIJ
  rw [dif_pos (by simp)]
  haveI : Unique (Fin ({b} : Finset (Fin 2)).card) := inferInstanceAs (Unique (Fin 1))
  rw [det_unique]
  show h _ _ = _
  congr 1
  · exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)
  · exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)

theorem cols0 : stepCols 2 2 0 = {0} := by decide

theorem sum_minor {R : Type} [CommRing R] (u : Finset (Fin 2) → R) (h : Matrix (Fin 2) (Fin 2) R) :
    ∑ I, u I * minorIJ h I {0} = u {0} * h 0 0 + u {1} * h 1 0 := by
  have : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [this, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide),
    minor_single, minor_single]
  have e1 : minorIJ h ∅ {0} = 0 := dif_neg (by decide)
  have e2 : minorIJ h {0, 1} {0} = 0 := dif_neg (by decide)
  rw [e1, e2]; ring

theorem detFac0 {R : Type} [CommRing R] (T : Matrix (Fin 2) (Fin 2) R) : detFac 2 0 T = 1 := by
  simp [detFac]

theorem detFac1 {R : Type} [CommRing R] (T : Matrix (Fin 2) (Fin 2) R) : detFac 2 1 T = T.det := by
  have e1 : wIdx 2 2 = Finset.univ := by decide
  have e2 : omIdx 2 2 = ∅ := by decide
  have h1 : minorIJ T Finset.univ Finset.univ = T.det := by
    unfold minorIJ
    rw [dif_pos rfl]
    exact det_submatrix_equiv_self (Equiv.ofBijective (Finset.univ.orderEmbOfFin rfl)
      ⟨(Finset.univ.orderEmbOfFin rfl).injective, fun a => by
        have := Finset.range_orderEmbOfFin (Finset.univ : Finset (Fin 2)) rfl
        exact (Set.range_eq_univ.1 (by simpa using this)) a⟩) T
  have h2 : minorIJ T ∅ ∅ = 1 := by
    unfold minorIJ
    rw [dif_pos rfl]
    haveI : IsEmpty (Fin (∅ : Finset (Fin 2)).card) := inferInstanceAs (IsEmpty (Fin 0))
    exact det_isEmpty
  simp [detFac, e1, e2, h1, h2]

theorem blockDiag2 {R : Type} [CommRing R] (T : Matrix (Fin 2) (Fin 2) R) : IsBlockDiag 2 T :=
  fun a b h => absurd (by simp) h

variable {Ω}

theorem isMultiHomog_X' {k : NonPluckerBlocks blkH} (i : Fin 3) :
    IsMultiHomog (X ⟨k, i⟩ : MRing (baseIdx ιH blkH)) fun _ => 1 := by
  classical
  intro m hm k'
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain rfl : k' = k := Subsingleton.elim _ _
  simp [Finsupp.single_apply]

theorem isMultiHomog_C' (n : ℤ) : IsMultiHomog (C n : MRing (baseIdx ιH blkH)) fun _ => 0 := by
  classical
  intro m hm k
  rw [support_C] at hm
  split_ifs at hm
  · simp at hm
  · rw [Finset.mem_singleton] at hm
    subst hm
    simp

theorem regAt_int (x : (Σ k, baseIdx ιH blkH k) → Ω) {Q : Ideal (MRing (baseIdx ιH blkH))} (hQ : Q.IsPrime)
    (n : ℤ) : RegAt x Q (n : Ω) :=
  ⟨fun _ => 0, C n, C 1, isMultiHomog_C' n, isMultiHomog_C' 1,
    fun h => hQ.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h)), by simp⟩

def FH (x : Fin 3 → Ω) (c : Fin 3) : FrameData ιH Unit 2 Ω blkH where
  c _ := c
  T _ := Matrix.diagonal ![1, x c]
  u q I := if q.1 then (if q.2 = 2 then (if I = {1} then 1 else 0) else if I = {0} then x q.2 / x c else 0) else 0
  u' I q := if q.1 ∧ ((I = {0} ∧ q.2 = c) ∨ (I = {1} ∧ q.2 = 2)) then 1 else 0
  υ _ := 1

def MH (x : Fin 3 → Ω) (hx2 : x 2 = 0) (hx : x 0 ≠ 0 ∨ x 1 ≠ 0) : FlagModel (yH Ω x) Unit 2 2 where
  j_le := le_rfl
  Ω := Ω
  blk := blkH
  blk_none := by
    rintro ⟨⟨⟩, i⟩
    fin_cases i <;> simp [blkH, IsProperStep]
  blk_inj p p' k h h' := by rw [(blkH_some h).1, (blkH_some h').1]
  x q := x q.2
  x_ne k := hx.elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
  y_base q := by
    obtain ⟨⟨k, hk⟩, i⟩ := q
    cases k
    · rfl
    · exact absurd rfl (hk ((), 0))
  g := gH Ω
  g_block _ := blockDiag2 _
  g_indep := by
    refine IsGenericFlag.of_lowerUni (fun τ => (genLow_lowerUni τ).map _) ?_
    have e : (fun q : LowIdx Unit 2 2 => gH Ω q.1.1 q.1.2.1 q.1.2.2) =
        fun q => algebraMap (MvPolynomial (LowIdx Unit 2 2) Ω) (ΦH Ω) (X q) :=
      funext fun q => congrArg (algebraMap (MvPolynomial (LowIdx Unit 2 2) Ω) (ΦH Ω)) (genLow_apply (R := Ω) q)
    rw [e]
    exact (MvPolynomial.algebraicIndependent_X (LowIdx Unit 2 2) Ω).map'
      (f := IsScalarTower.toAlgHom Ω (MvPolynomial (LowIdx Unit 2 2) Ω) (ΦH Ω)) (IsFractionRing.injective _ _)
  coef := coefH Ω x
  y_step p k hp m := by
    obtain ⟨rfl, rfl⟩ := blkH_some hp
    rfl
  b _ _ := 1
  lam _ := 1
  frames Q hQ hrel hle := by
    obtain ⟨c, hc⟩ := hrel bb
    have hxc : x c ≠ 0 := fun h => hc (hle (by
      show mConeMap _ (X ⟨bb, c⟩) = 0
      rw [mConeMap, aeval_X]
      show C (x c) * X bb = 0
      rw [h, map_zero, zero_mul]))
    have hc2 : c ≠ 2 := fun e => hxc (e ▸ hx2)
    have hprod : ∀ f : NonPluckerBlocks blkH → Ω, ∏ k, f k = f bb := fun f => Fintype.prod_unique f
    refine ⟨FH x c, ⟨⟨fun _ => ⟨blockDiag2 _, by simp [FH, hxc]⟩, fun p k hp m h _ => ?_, fun p k hp I I' hI hI' => ?_,
      fun p hp => ?_⟩, ⟨fun k => by rw [Subsingleton.elim k bb]; exact hc, fun q I => ⟨?_, ?_⟩, fun p _ => ⟨one_ne_zero, ?_, ?_⟩⟩⟩⟩
    · obtain ⟨rfl, rfl⟩ := blkH_some hp
      rw [detFac0, one_mul, hprod, cols0, sum_minor, sum_minor]
      simp only [FH, coefH, diagonal_mul, zpow_one]
      fin_cases m <;> simp [hc2]
      all_goals (rw [← mul_assoc, mul_comm (x c), div_mul_cancel₀ _ hxc])
    · obtain ⟨rfl, rfl⟩ := blkH_some hp
      have a := hI.1
      have b := hI'.1
      rw [cols0, Finset.card_singleton, Finset.card_eq_one] at a b
      obtain ⟨a, rfl⟩ := a
      obtain ⟨b, rfl⟩ := b
      rw [Fin.sum_univ_three]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [FH] at hc2 hxc ⊢ <;> exact hxc
    · obtain rfl := blkH_none hp
      rw [detFac1, hprod]
      simp [FH]
    · simp only [FH]
      split_ifs
      · simpa using regAt_int (fun q => x q.2) hQ 1
      · simpa using regAt_int (fun q => x q.2) hQ 0
      · exact ⟨fun _ => 1, X ⟨bb, q.2⟩, X ⟨bb, c⟩, isMultiHomog_X' _, isMultiHomog_X' _, hc, by
          simp [div_mul_cancel₀ _ hxc]⟩
      · simpa using regAt_int (fun q => x q.2) hQ 0
      · simpa using regAt_int (fun q => x q.2) hQ 0
    · simp only [FH]
      split_ifs
      · simpa using regAt_int (fun q => x q.2) hQ 1
      · simpa using regAt_int (fun q => x q.2) hQ 0
    · simpa [FH] using regAt_int (fun q => x q.2) hQ 1
    · simpa [FH] using regAt_int (fun q => x q.2) hQ 1

example : Nonempty (FlagModel (yH ℚ ![1, 1, 0]) Unit 2 2) := ⟨MH (![1, 1, 0] : Fin 3 → ℚ) rfl (Or.inl one_ne_zero)⟩

example : (MH (![1, 1, 0] : Fin 3 → ℚ) rfl (Or.inl one_ne_zero)).dy ((), 0) = fun k => if k then 1 else -1 := by
  funext k
  cases k
  · exact dif_pos fun p h => by simpa using (blkH_some h).2
  · exact (dif_neg fun h => h ((), 0) rfl).trans (if_pos rfl)

example : (MH (![1, 1, 0] : Fin 3 → ℚ) rfl (Or.inl one_ne_zero)).blk ((), 1) = none ∧
    (MH (![1, 1, 0] : Fin 3 → ℚ) rfl (Or.inl one_ne_zero)).lam ((), 1) = 1 := ⟨rfl, rfl⟩

end FlagEx

end GlobalTheory.CompanionTheory.Ar.PB
