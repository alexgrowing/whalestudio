import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymEdgeStableSubmoduleEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KerReductionLeRangeReductionOfMulEqSmulStatement
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory.ScalInt

theorem exists_normalise {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : M ≠ 0) : ∃ c : Kˣ, (∀ i j, (c : K)⁻¹ * M i j ∈ O) ∧ ∃ i j, (c : K)⁻¹ * M i j = 1 := by
  obtain ⟨i1, j1, h1⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hM (Matrix.ext h)
  obtain ⟨⟨i0, j0⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : Fin n × Fin n => O.valuation (M p.1 p.2)) ⟨(i1, j1), Finset.mem_univ _⟩
  have h0 : M i0 j0 ≠ 0 := by
    intro h
    have := hmax (i1, j1) (Finset.mem_univ _)
    simp only [h, map_zero] at this
    exact h1 ((Valuation.zero_iff _).1 (le_antisymm this zero_le))
  have hv0 : 0 < O.valuation (M i0 j0) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0)
  refine ⟨Units.mk0 _ h0, fun i j => ?_, i0, j0, by simp [h0]⟩
  rw [← ValuationSubring.valuation_le_one_iff, Units.val_mk0, map_mul, map_inv₀]
  exact (inv_mul_le_one₀ hv0).2 (hmax (i, j) (Finset.mem_univ _))

theorem one_add_unit {K : Type} [Field K] (O : ValuationSubring K) {k : Type} [Field k] (r : O →+* k)
    (hr : Function.Surjective r) {n : ℕ} (Y : Matrix (Fin n) (Fin n) O) (hY : ∀ i j, r (Y i j) = 0) :
    ∃ x : GL (Fin n) O, (x : Matrix (Fin n) (Fin n) O) = 1 + Y := by
  have hmax : RingHom.ker r = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r hr)
  have h1 : r.mapMatrix (1 + Y) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [hY]
    · simp [Matrix.one_apply_ne h, hY]
  have hdet : r (1 + Y).det = 1 := by rw [RingHom.map_det, h1, Matrix.det_one]
  have hu : IsUnit (1 + Y).det := by
    by_contra h
    have h2 := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
    rw [← hmax, RingHom.mem_ker, hdet] at h2
    exact one_ne_zero h2
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  exact ⟨u, hu'⟩

theorem gl_of_int {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K)
    (h1 : ∀ i j, (m : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (h2 : ∀ i j, ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O) :
    ∃ x : GL (Fin n) O, bc O.subtype x = m := by
  have inj : Function.Injective fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype :=
    Matrix.map_injective O.subtype_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · show Matrix.map _ O.subtype = Matrix.map _ O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact m.mul_inv
  · show Matrix.map _ O.subtype = Matrix.map _ O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact m.inv_mul

theorem mul_single_mul_apply {n : ℕ} {R : Type} [CommRing R] (A B : Matrix (Fin n) (Fin n) R) (a b i j : Fin n) (c : R) :
    (A * Matrix.single a b c * B) i j = A i a * c * B b j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.mul_single_apply_same]
  · intro x _ hx; rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hx, zero_mul]
  · intro h; exact absurd (Finset.mem_univ b) h

theorem mem_unipSym_of {k : Type} [CommRing k] {n ρ κ : ℕ} (g : GL (Fin n) k)
    (h1 : ∀ p q : Fin n, q.val < p.val → (g : Matrix (Fin n) (Fin n) k) p q = 0)
    (h2 : ∀ p, (g : Matrix (Fin n) (Fin n) k) p p = 1)
    (h3 : ∀ p q : Fin n, ρ ≤ p.val → p.val < ρ + κ → q.val = ρ + κ → (g : Matrix (Fin n) (Fin n) k) p q = 0) :
    g ∈ unipSym k n ρ κ := ⟨⟨fun p q h => h1 p q h, h2⟩, h3⟩

theorem isScal_of_normalises (K : Type) [Field K] (O : ValuationSubring K) (k : Type) [Field k] (r : O →+* k)
    (hr : Function.Surjective r) (n ρ κ : ℕ) (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (a : Fin n → Fin n → k) (ha : ∀ i j, symEdge ρ κ i j → a i j ≠ 0) (m : GL (Fin n) K)
    (H1 : ∀ x : GL (Fin n) O, bc r x ∈ unipSym k n ρ κ → ∃ x' : GL (Fin n) O,
      bc O.subtype x' = m * bc O.subtype x * m⁻¹ ∧ ψ (edgeVal ρ κ a (bc r x')) = ψ (edgeVal ρ κ a (bc r x)))
    (H2 : ∀ x : GL (Fin n) O, bc r x ∈ unipSym k n ρ κ → ∃ x' : GL (Fin n) O,
      bc O.subtype x' = m⁻¹ * bc O.subtype x * m) : IsScal O m := by
  have hmax : RingHom.ker r = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r hr)
  have hunit : ∀ t : O, r t ≠ 0 → IsUnit t := fun t ht => by
    by_contra hc
    have h2 := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hc)
    rw [← hmax, RingHom.mem_ker] at h2
    exact ht h2
  have inj : ∀ A B : Matrix (Fin n) (Fin n) O, A.map O.subtype = B.map O.subtype → A = B :=
    fun A B h => Matrix.map_injective O.subtype_injective h
  set mm := (m : Matrix (Fin n) (Fin n) K) with hmm
  set mi := ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hmi
  haveI : NeZero n := ⟨by omega⟩
  have hm0 : mm ≠ 0 := fun h => by
    have := m.mul_inv
    rw [← hmm, h, zero_mul] at this
    exact zero_ne_one this
  obtain ⟨c₁, hc₁, i₁, j₁, h₁⟩ := exists_normalise O mm hm0
  set M₁ : Matrix (Fin n) (Fin n) K := (c₁ : K)⁻¹ • mm with hM₁
  set P₁ : Matrix (Fin n) (Fin n) K := (c₁ : K) • mi with hP₁
  have hc : (c₁ : K)⁻¹ * c₁ = 1 := inv_mul_cancel₀ c₁.ne_zero
  have hc' : (c₁ : K) * (c₁ : K)⁻¹ = 1 := mul_inv_cancel₀ c₁.ne_zero
  have hMP : M₁ * P₁ = 1 := by
    rw [hM₁, hP₁, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, one_smul]; exact m.mul_inv
  have hPM : P₁ * M₁ = 1 := by
    rw [hM₁, hP₁, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc', one_smul]; exact m.inv_mul
  have hconj : ∀ X, mm * X * mi = M₁ * X * P₁ := fun X => by
    rw [hM₁, hP₁, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, one_smul]
  have hconj' : ∀ X, mi * X * mm = P₁ * X * M₁ := fun X => by
    rw [hM₁, hP₁, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc', one_smul]
  have e1 : ∀ i j, M₁ i j ∈ O := fun i j => by
    rw [hM₁, Matrix.smul_apply, smul_eq_mul]; exact hc₁ i j
  have hP0 : P₁ ≠ 0 := fun h => by
    rw [h, zero_mul] at hPM
    exact zero_ne_one hPM
  obtain ⟨c₂, hc₂, i₂, j₂, h₂⟩ := exists_normalise O P₁ hP0
  let m₁ : GL (Fin n) K := ⟨M₁, P₁, hMP, hPM⟩
  by_cases hc2O : (c₂ : K) ∈ O
  · have e2 : ∀ i j, P₁ i j ∈ O := fun i j => by
      have : P₁ i j = c₂ * ((c₂ : K)⁻¹ * P₁ i j) := by rw [← mul_assoc, mul_inv_cancel₀ c₂.ne_zero, one_mul]
      rw [this]; exact mul_mem hc2O (hc₂ i j)
    obtain ⟨x, hx⟩ := gl_of_int O m₁ e1 e2
    refine ⟨c₁, x, ?_⟩
    rw [hx]
    show mm = (c₁ : K) • ((c₁ : K)⁻¹ • mm)
    rw [smul_smul, hc', one_smul]
  exfalso

  set π : K := (c₂ : K)⁻¹ with hπdef
  have hπO : π ∈ O := (O.mem_or_inv_mem c₂).resolve_left hc2O
  set πo : O := ⟨π, hπO⟩ with hπo
  have hπ0 : πo ≠ 0 := fun h => inv_ne_zero c₂.ne_zero (congrArg Subtype.val h)
  have hπr : r πo = 0 := by
    by_contra h
    obtain ⟨u, hu⟩ := hunit _ h
    apply hc2O
    have h3 : (((u⁻¹ : Oˣ) : O) : K) * π = 1 := by
      have := congrArg Subtype.val u.inv_mul
      rw [hu] at this
      exact this
    have h4 : (((u⁻¹ : Oˣ) : O) : K) = c₂ := (mul_inv_eq_one₀ c₂.ne_zero).1 h3
    rw [← h4]; exact ((u⁻¹ : Oˣ) : O).2
  have e3 : ∀ i j, π * P₁ i j ∈ O := hc₂
  set Mo : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨M₁ i j, e1 i j⟩ with hMo
  set No : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨π * P₁ i j, e3 i j⟩ with hNo
  have hMoK : Mo.map O.subtype = M₁ := Matrix.ext fun _ _ => rfl
  have hNoK : No.map O.subtype = π • P₁ := Matrix.ext fun _ _ => rfl
  have hsc : ∀ (t : O) (A : Matrix (Fin n) (Fin n) O), (t • A).map O.subtype = (t : K) • A.map O.subtype :=
    fun t A => Matrix.ext fun _ _ => rfl
  have h1K : (1 : Matrix (Fin n) (Fin n) O).map O.subtype = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hMN : Mo * No = πo • 1 := inj _ _ (by rw [Matrix.map_mul, hMoK, hNoK, hsc, h1K, Matrix.mul_smul, hMP])
  have hNM : No * Mo = πo • 1 := inj _ _ (by rw [Matrix.map_mul, hMoK, hNoK, hsc, h1K, Matrix.smul_mul, hPM])
  have hMo1 : Mo i₁ j₁ = 1 := Subtype.ext h₁
  have hNo1 : No i₂ j₂ = 1 := Subtype.ext h₂
  have hsingK : ∀ (i j : Fin n) (t : O), (Matrix.single i j t).map O.subtype = Matrix.single i j (t : K) :=
    fun i j t => by
      ext p q
      rw [Matrix.map_apply, Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
  have hconjO : ∀ x x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹ →
      (x' : Matrix (Fin n) (Fin n) O).map O.subtype = M₁ * (x : Matrix (Fin n) (Fin n) O).map O.subtype * P₁ :=
    fun x x' h => by
      have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h
      simp only [Units.val_mul] at this
      rw [← hconj]; exact this
  have hred1 : ∀ (x : GL (Fin n) O) (Y : Matrix (Fin n) (Fin n) O), (x : Matrix (Fin n) (Fin n) O) = 1 + Y →
      (∀ i j, r (Y i j) = 0) → bc r x = 1 := fun x Y hx hY => Units.ext (by
    show (x : Matrix (Fin n) (Fin n) O).map r = 1
    rw [hx]; ext i j
    by_cases h : i = j
    · subst h; simp [hY]
    · simp [Matrix.one_apply_ne h, hY])
  have hsingr : ∀ (i j : Fin n) (t : O), r t = 0 → ∀ p q, r (Matrix.single i j t p q) = 0 := fun i j t ht p q => by
    rw [Matrix.single_apply]; split_ifs <;> simp [ht]

  have hπdiv : ∀ t : O, r t = 0 → ∃ s, t = πo * s := fun t ht => by
    obtain ⟨x, hx⟩ := one_add_unit O r hr (Matrix.single j₁ i₂ t) (hsingr _ _ _ ht)
    obtain ⟨x', hx', -⟩ := H1 x (hred1 x _ hx (hsingr _ _ _ ht) ▸ Subgroup.one_mem _)
    have h5 := congrFun (congrFun (hconjO x x' hx') i₁) j₂
    rw [hx, Matrix.map_add _ (map_add _), h1K, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hMP, Matrix.add_apply, hsingK,
      mul_single_mul_apply, ← h1K] at h5
    have hP : P₁ i₂ j₂ = c₂ := ((inv_mul_eq_one₀ c₂.ne_zero).1 h₂).symm
    have hM : M₁ i₁ j₁ = 1 := h₁
    rw [hP, hM, one_mul] at h5
    have hmem : (t : K) * c₂ ∈ O := by
      have : (t : K) * c₂ = ((x' : Matrix (Fin n) (Fin n) O) i₁ j₂ : K) - ((1 : Matrix (Fin n) (Fin n) O) i₁ j₂ : K) := by
        have h5' : (((x' : Matrix (Fin n) (Fin n) O) i₁ j₂ : O) : K) = ((1 : Matrix (Fin n) (Fin n) O) i₁ j₂ : K) + t * c₂ := h5
        rw [h5']; ring
      rw [this]; exact sub_mem (Subtype.mem _) (Subtype.mem _)
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    show (t : K) = π * ((t : K) * c₂)
    rw [hπdef, mul_comm, mul_assoc, mul_inv_cancel₀ c₂.ne_zero, mul_one]

  set Mb := Mo.map r with hMb
  set Nb := No.map r with hNb

  set T : Fin n → Fin n → k := fun a' b' =>
    ∑ i, ∑ j, if symEdge ρ κ i j then a i j * (r (Mo i a') * r (No b' j)) else 0 with hT
  have hT0 : ∀ a' b', T a' b' = 0 := fun a' b' => by
    have key : ∀ s : O, ψ (r s * T a' b') = 1 := fun s => by
      have hsr : r (s * πo) = 0 := by rw [map_mul, hπr, mul_zero]
      obtain ⟨x, hx⟩ := one_add_unit O r hr (Matrix.single a' b' (s * πo)) (hsingr _ _ _ hsr)
      have hxr := hred1 x _ hx (hsingr _ _ _ hsr)
      obtain ⟨x', hx', hψx⟩ := H1 x (hxr ▸ Subgroup.one_mem _)
      have hx'e : ∀ i j, (x' : Matrix (Fin n) (Fin n) O) i j = (1 : Matrix (Fin n) (Fin n) O) i j + s * (Mo i a' * No b' j) :=
        fun i j => by
          apply Subtype.ext
          have h5 := congrFun (congrFun (hconjO x x' hx') i) j
          rw [hx, Matrix.map_add _ (map_add _), h1K, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hMP, Matrix.add_apply,
            hsingK, mul_single_mul_apply, ← h1K] at h5
          have h5' : (((x' : Matrix (Fin n) (Fin n) O) i j : O) : K) =
            ((1 : Matrix (Fin n) (Fin n) O) i j : K) + M₁ i a' * ((s : K) * π) * P₁ b' j := h5
          rw [h5']
          show _ = ((1 : Matrix (Fin n) (Fin n) O) i j : K) + (s : K) * (M₁ i a' * (π * P₁ b' j))
          ring
      have hev : edgeVal ρ κ a (bc r x') = r s * T a' b' := by
        unfold edgeVal
        rw [hT, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with he
        · have hij : i ≠ j := fun e => by unfold symEdge at he; rw [e] at he; omega
          show a i j * r ((x' : Matrix (Fin n) (Fin n) O) i j) = _
          rw [hx'e, Matrix.one_apply_ne hij]
          simp only [map_add, map_mul, map_zero, zero_add]
          ring
        · rw [mul_zero]
      rw [← hev, hψx, hxr, edgeVal_one, AddChar.map_zero_eq_one]
    by_contra h0
    apply hψ
    ext y
    obtain ⟨s, hs⟩ := hr (y / T a' b')
    rw [AddChar.one_apply, ← key s, hs, div_mul_cancel₀ _ h0]

  have hEst : ∀ i j : Fin n, i < j → ¬(ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ) →
      ∃ y : Matrix (Fin n) (Fin n) O, Mo * y = (1 + Matrix.single i j 1) * Mo := fun i j hij hal => by
    have hij' : i.val < j.val := hij
    have hne : j ≠ i := ne_of_gt hij
    have hEE : Matrix.single i j (1 : O) * Matrix.single i j 1 = 0 := Matrix.single_mul_single_of_ne 1 i j i hne 1
    let x : GL (Fin n) O := ⟨1 + Matrix.single i j 1, 1 - Matrix.single i j 1,
      by rw [add_mul, one_mul, mul_sub, mul_one, hEE, sub_zero, sub_add_cancel],
      by rw [sub_mul, one_mul, mul_add, mul_one, hEE, add_zero, add_sub_cancel_right]⟩
    have hxe : ∀ p q, ((bc r x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q =
        r ((1 : Matrix (Fin n) (Fin n) O) p q) + (if i = p ∧ j = q then 1 else 0) := fun p q => by
      show r ((1 + Matrix.single i j (1 : O)) p q) = _
      rw [Matrix.add_apply, map_add, Matrix.single_apply]
      split_ifs <;> simp
    have hxu : bc r x ∈ unipSym k n ρ κ := by
      refine mem_unipSym_of _ (fun p q hpq => ?_) (fun p => ?_) (fun p q h1 h2 h3 => ?_)
      · have hpq' : p ≠ q := fun e => by rw [e] at hpq; omega
        rw [hxe, Matrix.one_apply_ne hpq', map_zero, zero_add, if_neg]
        rintro ⟨rfl, rfl⟩; omega
      · rw [hxe, Matrix.one_apply_eq, map_one, if_neg, add_zero]
        rintro ⟨rfl, e⟩; exact hne e
      · have hpq' : p ≠ q := fun e => by rw [e] at h2; omega
        rw [hxe, Matrix.one_apply_ne hpq', map_zero, zero_add, if_neg]
        rintro ⟨rfl, rfl⟩; exact hal ⟨h1, h2, h3⟩
    obtain ⟨y, hy⟩ := H2 x hxu
    refine ⟨y, inj _ _ ?_⟩
    have h5 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hy
    simp only [Units.val_mul] at h5
    have h6 : (y : Matrix (Fin n) (Fin n) O).map O.subtype = P₁ * (x : Matrix (Fin n) (Fin n) O).map O.subtype * M₁ := by
      rw [← hconj']; exact h5
    rw [Matrix.map_mul, Matrix.map_mul, hMoK, h6, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMP, Matrix.one_mul]

  have hNbMb : Nb * Mb = 0 := by
    rw [hNb, hMb, ← Matrix.map_mul, hNM]
    ext i j
    simp [hπr]
  set A' : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => if symEdge ρ κ i j then a i j else 0 with hA'
  have hz : ∀ w : Fin n → k, (fun j => ∑ i, if symEdge ρ κ i j then a i j * w i else 0) = A'ᵀ *ᵥ w := fun w => by
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA', Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hNAM : Nb * A'ᵀ * Mb = 0 := by
    ext b' l
    rw [Matrix.zero_apply, ← hT0 l b']
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hA', Matrix.of_apply, Finset.sum_mul, hT, hMb, hNb, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  set V := LinearMap.range (Matrix.mulVecLin Mb) with hV
  have hV0 : V ≠ ⊥ := by
    intro h
    have h1 : Mb *ᵥ Pi.single j₁ 1 ∈ V := ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    have h2 := congrFun h1 i₁
    rw [Matrix.mulVec_single_one] at h2
    simp [hMb, hMo1] at h2
  have hAst : ∀ w ∈ V, (fun j => ∑ i, if symEdge ρ κ i j then a i j * w i else 0) ∈ V := by
    rintro w ⟨u, rfl⟩
    rw [hz]
    obtain ⟨u', hu'⟩ := GlobalTheory.T.ker_reduction_le_range_reduction_of_mul_eq_smul r hr Mo No πo hπ0 hπdiv hMN (A'ᵀ *ᵥ (Mb *ᵥ u)) (by
      rw [← hNb, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hNAM, Matrix.zero_mulVec])
    exact ⟨u', hu'.symm⟩
  have hEst' : ∀ i j : Fin n, i < j → ¬(ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ) → ∀ w ∈ V, Pi.single i (w j) ∈ V := by
    rintro i j hij hal w ⟨u, rfl⟩
    obtain ⟨y, hy⟩ := hEst i j hij hal
    have hs1 : (Matrix.single i j (1 : O)).map r = Matrix.single i j 1 := by
      ext p q
      rw [Matrix.map_apply, Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
    have hyb : Mb * y.map r = (1 + Matrix.single i j 1) * Mb := by
      rw [hMb, ← Matrix.map_mul, hy, Matrix.map_mul, Matrix.map_add _ (map_add _), hs1, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨(y.map r - 1) *ᵥ u, ?_⟩
    show Mb *ᵥ ((y.map r - 1) *ᵥ u) = Pi.single i ((Mb *ᵥ u) j)
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, hyb, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, add_sub_cancel_left,
      ← Matrix.mulVec_mulVec]
    ext p
    by_cases h : p = i
    · subst h; simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
    · rw [Pi.single_eq_of_ne h]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [Matrix.single_apply, if_neg (fun e => h e.1.symm), zero_mul]
  have htop := GlobalTheory.T.symEdge_stable_submodule_eq_top k n ρ κ hn hρ a ha V hV0 hAst hEst'
  have hmemv : Pi.single j₂ (1 : k) ∈ V := htop ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := hmemv
  have h6 : Nb *ᵥ Pi.single j₂ 1 = 0 := by
    rw [← hu]
    show Nb *ᵥ (Mb *ᵥ u) = 0
    rw [Matrix.mulVec_mulVec, hNbMb, Matrix.zero_mulVec]
  have h7 := congrFun h6 i₂
  rw [Matrix.mulVec_single_one] at h7
  simp [hNb, hNo1] at h7

end GlobalTheory.ScalInt
