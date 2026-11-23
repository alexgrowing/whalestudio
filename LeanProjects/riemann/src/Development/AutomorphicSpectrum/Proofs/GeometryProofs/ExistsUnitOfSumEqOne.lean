import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DetMulExpand

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

def kMinor {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k ≤ r)
    (I : Fin k → Fin n) : F :=
  (A.submatrix I (Fin.castLE hk)).det

theorem stepMinor_eq_kMinor {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : stepMinor A i J = kMinor A ((i : ℕ) + 1) i.2 J := rfl

def NormAt {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k ≤ r)
    (I : Fin k → Fin n) : Prop :=
  kMinor Y k hk I ≠ 0 ∧ ∀ I' : Fin k → Fin n, kMinor Y k hk I' / kMinor Y k hk I ∈ O

theorem normAt_zero {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F)
    (I : Fin 0 → Fin n) : NormAt O Y 0 (Nat.zero_le r) I := by
  refine ⟨by simp [kMinor], fun I' => ?_⟩
  simpa [kMinor] using O.one_mem

theorem det_mul_expand {F : Type} [CommRing F] {k r : ℕ} (A : Matrix (Fin k) (Fin r) F)
    (B : Matrix (Fin r) (Fin k) F) :
    (A * B).det = ∑ f : Fin k → Fin r, (∏ a, A a (f a)) * (B.submatrix f id).det :=
  _root_.UpperTheory.Reformulated.B.DetMulExpand.det_mul_expand A B

theorem kMinor_mul_expand {F : Type} [CommRing F] {n m r : ℕ} (A : Matrix (Fin n) (Fin m) F)
    (B : Matrix (Fin m) (Fin r) F) (k : ℕ) (hk : k ≤ r) (J : Fin k → Fin n) :
    kMinor (A * B) k hk J = ∑ I : Fin k → Fin m, (∏ a, A (J a) (I a)) * kMinor B k hk I := by
  unfold kMinor
  have : (A * B).submatrix J (Fin.castLE hk) = A.submatrix J id * B.submatrix id (Fin.castLE hk) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [this, det_mul_expand]
  rfl

theorem kMinor_mul_div_mem {F : Type} [Field F] (D : Subring F) {n m r : ℕ} (A : Matrix (Fin n) (Fin m) F)
    (B : Matrix (Fin m) (Fin r) F) (k : ℕ) (hk : k ≤ r) (c : F) (hA : ∀ a b, A a b ∈ D)
    (hB : ∀ I, kMinor B k hk I / c ∈ D) (J : Fin k → Fin n) : kMinor (A * B) k hk J / c ∈ D := by
  rw [kMinor_mul_expand, Finset.sum_div]
  refine D.sum_mem fun I _ => ?_
  rw [mul_div_assoc]
  exact D.mul_mem (D.prod_mem fun a _ => hA _ _) (hB I)

theorem exists_unit_of_sum_eq_one {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {ι : Type}
    (s : Finset ι) (a : ι → F) (ha : ∀ i ∈ s, a i ∈ O) (h1 : ∑ i ∈ s, a i = 1) :
    ∃ i ∈ s, a i ≠ 0 ∧ (a i)⁻¹ ∈ O := by
  classical
  by_contra hcon
  push_neg at hcon
  have key : ∀ t : Finset ι, t ⊆ s → ∃ h : ∑ i ∈ t, a i ∈ O, (⟨_, h⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
    intro t
    induction t using Finset.cons_induction with
    | empty => intro _; exact ⟨by simp, Ideal.zero_mem _⟩
    | cons i t hi ih =>
      intro hts
      rw [Finset.cons_eq_insert, Finset.insert_subset_iff] at hts
      obtain ⟨h2, h3⟩ := ih hts.2
      have h4 : a i ∈ O := ha i hts.1
      have h5 : (⟨a i, h4⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨v, hv⟩ := hu.exists_right_inv
        have hv' : a i * (v : F) = 1 := congrArg Subtype.val hv
        have h0 : a i ≠ 0 := left_ne_zero_of_mul_eq_one hv'
        refine hcon i hts.1 h0 ?_
        rw [eq_comm.1 (eq_inv_of_mul_eq_one_right hv')]
        exact v.2
      rw [Finset.sum_cons]
      refine ⟨O.add_mem h4 h2, ?_⟩
      exact Ideal.add_mem _ h5 h3
  obtain ⟨h, hm⟩ := key s subset_rfl
  have : (⟨∑ i ∈ s, a i, h⟩ : O) = 1 := Subtype.ext h1
  rw [this] at hm
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem kMinor_mul_upper {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F)
    (C : Matrix (Fin r) (Fin r) F) (hC : ∀ l k, k < l → C l k = 0) (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin n) :
    kMinor (A * C) k hk I = kMinor A k hk I * kMinor C k hk (Fin.castLE hk) := by
  unfold kMinor
  rw [← Matrix.det_mul]
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hk) (Fin.castLE_injective hk).injOn (fun _ _ => Finset.mem_univ _)
    (fun j _ hj => ?_) (fun _ _ => rfl)
  have hjk : (Fin.castLE hk b) < j := by
    rw [Fin.lt_def]
    by_contra hlt
    have hjk' : (j : ℕ) < k := by
      have := b.2
      simp only [Fin.val_castLE] at hlt
      omega
    exact hj ⟨⟨j, hjk'⟩, by simp, by ext; simp⟩
  rw [hC _ _ hjk, mul_zero]

theorem kMinor_lower_lead {F : Type} [CommRing F] {r : ℕ} (L : Matrix (Fin r) (Fin r) F)
    (h0 : ∀ l k, l < k → L l k = 0) (h1 : ∀ l, L l l = 1) (k : ℕ) (hk : k ≤ r) :
    kMinor L k hk (Fin.castLE hk) = 1 := by
  unfold kMinor
  rw [Matrix.det_of_lowerTriangular]
  · simp [h1]
  · intro a b hab
    exact h0 _ _ (by simpa using hab)

def lastRow {r : ℕ} (k l : Fin r) : Fin ((k : ℕ) + 1) → Fin r := fun a =>
  if h : (a : ℕ) = k then l else ⟨a, by have := a.2; have := k.2; omega⟩

theorem kMinor_lower_lastRow {F : Type} [CommRing F] {r : ℕ} (L : Matrix (Fin r) (Fin r) F)
    (h0 : ∀ l k, l < k → L l k = 0) (h1 : ∀ l, L l l = 1) (k l : Fin r) (hkl : k < l) :
    kMinor L ((k : ℕ) + 1) k.2 (lastRow k l) = L l k := by
  unfold kMinor
  rw [Matrix.det_of_lowerTriangular, Fin.prod_univ_castSucc]
  · have e1 : ∀ a : Fin (k : ℕ), (L.submatrix (lastRow k l) (Fin.castLE k.2)) a.castSucc a.castSucc = 1 := by
      intro a
      have : lastRow k l a.castSucc = Fin.castLE k.2 a.castSucc := by
        have := a.2
        ext
        simp [lastRow, Nat.ne_of_lt this]
      simp [this, h1]
    have e2 : (L.submatrix (lastRow k l) (Fin.castLE k.2)) (Fin.last _) (Fin.last _) = L l k := by
      have a1 : lastRow k l (Fin.last _) = l := by simp [lastRow]
      have a2 : Fin.castLE k.2 (Fin.last (k : ℕ)) = k := by ext; simp
      simp [a1, a2]
    rw [Finset.prod_congr rfl (fun a _ => e1 a), e2]
    simp
  · intro a b hab
    have hab' : a < b := by simpa using hab
    have hb := b.2
    have ha : (a : ℕ) ≠ k := by
      have : (a : ℕ) < b := hab'
      omega
    simp only [Matrix.submatrix_apply, lastRow, dif_neg ha]
    exact h0 _ _ (by rw [Fin.lt_def]; simpa using hab')

theorem exists_normAt {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) F) (N : Matrix (Fin r) (Fin n) F) (hA : ∀ a b, A a b ∈ O)
    (hN : ∀ a b, N a b ∈ O) (hNA : N * A = 1) (Y : Matrix (Fin r) (Fin r) F) (k : ℕ) (hk : k ≤ r)
    (J : Fin k → Fin n) (hJ : NormAt O (A * Y) k hk J) : ∃ I, NormAt O Y k hk I := by
  obtain ⟨hP, hr⟩ := hJ
  set P := kMinor (A * Y) k hk J with hPdef
  have hY : Y = N * (A * Y) := by rw [← Matrix.mul_assoc, hNA, Matrix.one_mul]
  have hyO : ∀ I, kMinor Y k hk I / P ∈ O := fun I => by
    rw [hY]
    exact kMinor_mul_div_mem O N (A * Y) k hk P hN hr I
  have h1 : ∑ I : Fin k → Fin r, (∏ a, A (J a) (I a)) * (kMinor Y k hk I / P) = 1 := by
    have : P = ∑ I : Fin k → Fin r, (∏ a, A (J a) (I a)) * kMinor Y k hk I := kMinor_mul_expand A Y k hk J
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div, ← this, div_self hP]
  obtain ⟨I, -, hne, hinv⟩ := exists_unit_of_sum_eq_one O Finset.univ _
    (fun I _ => O.mul_mem (O.prod_mem fun a _ => hA _ _) (hyO I)) h1
  have hc : (∏ a, A (J a) (I a)) ≠ 0 := left_ne_zero_of_mul hne
  have hd : kMinor Y k hk I / P ≠ 0 := right_ne_zero_of_mul hne
  have hy : kMinor Y k hk I ≠ 0 := fun h => hd (by rw [h, zero_div])
  refine ⟨I, hy, fun I' => ?_⟩
  have e : kMinor Y k hk I' / kMinor Y k hk I =
      (kMinor Y k hk I' / P) * ((∏ a, A (J a) (I a)) * ((∏ a, A (J a) (I a)) * (kMinor Y k hk I / P))⁻¹) := by
    field_simp
  rw [e]
  exact O.mul_mem (hyO I') (O.mul_mem (O.prod_mem fun a _ => hA _ _) hinv)

theorem kMinor_mem {F : Type} [CommRing F] (D : Subring F) {n r : ℕ} (A : Matrix (Fin n) (Fin r) F)
    (hA : ∀ a b, A a b ∈ D) (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin n) : kMinor A k hk I ∈ D := by
  unfold kMinor
  rw [Matrix.det_apply']
  refine D.sum_mem fun σ _ => D.mul_mem (intCast_mem D _) (D.prod_mem fun a _ => hA _ _)

theorem ratio_eq_kMinor {F : Type} [Field F] {r : ℕ} (Y C V : Matrix (Fin r) (Fin r) F)
    (hC : ∀ l k, k < l → C l k = 0) (hV0 : ∀ l k, l < k → V l k = 0) (hV1 : ∀ l, V l l = 1)
    (h : Y * C = V) (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin r) (h0 : kMinor Y k hk (Fin.castLE hk) ≠ 0) :
    kMinor Y k hk I / kMinor Y k hk (Fin.castLE hk) = kMinor V k hk I := by
  have h1 := kMinor_lower_lead V hV0 hV1 k hk
  rw [← h, kMinor_mul_upper Y C hC] at h1
  rw [← h, kMinor_mul_upper Y C hC, div_eq_iff h0]
  linear_combination (-(kMinor Y k hk I)) * h1

theorem entries_mem {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (Fd : IntermediateField Ω K) {r : ℕ}
    (T' : Matrix (Fin r) (Fin r) Ω) (hT : T'.det ≠ 0) (u C V : Matrix (Fin r) (Fin r) K)
    (hu0 : ∀ l k, l < k → u l k = 0) (hu1 : ∀ l, u l l = 1) (hC : ∀ l k, k < l → C l k = 0)
    (hV0 : ∀ l k, l < k → V l k = 0) (hV1 : ∀ l, V l l = 1)
    (h : T'.map (algebraMap Ω K) * u * C = V) (hF : ∀ l k, V l k ∈ Fd) (l k : Fin r) (hkl : k < l) :
    u l k ∈ Fd := by
  have hdet : IsUnit T'.det := isUnit_iff_ne_zero.2 hT
  have hTi : (T'⁻¹).map (algebraMap Ω K) * T'.map (algebraMap Ω K) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  set Q := (T'⁻¹).map (algebraMap Ω K) * V with hQ
  have hQ' : u * C = Q := by
    rw [hQ, ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
  have hQF : ∀ a b, Q a b ∈ Fd := fun a b => by
    rw [hQ, Matrix.mul_apply]
    exact sum_mem fun j _ => mul_mem (Fd.algebraMap_mem _) (hF _ _)
  have hk : (k : ℕ) + 1 ≤ r := k.2
  have h1 := kMinor_lower_lead V hV0 hV1 _ hk
  rw [← h, kMinor_mul_upper _ C hC] at h1
  have hc : kMinor C _ hk (Fin.castLE hk) ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have h2 := kMinor_mul_upper u C hC _ hk (lastRow k l)
  have h3 := kMinor_mul_upper u C hC _ hk (Fin.castLE hk)
  rw [kMinor_lower_lastRow u hu0 hu1 k l hkl, hQ'] at h2
  rw [kMinor_lower_lead u hu0 hu1, hQ', _root_.one_mul] at h3
  have e : u l k = kMinor Q _ hk (lastRow k l) / kMinor Q _ hk (Fin.castLE hk) := by
    rw [h2, h3, mul_div_assoc, div_self hc, mul_one]
  rw [e]
  exact div_mem (kMinor_mem Fd.toSubalgebra.toSubring Q hQF _ hk _) (kMinor_mem Fd.toSubalgebra.toSubring Q hQF _ hk _)

theorem genU_zero (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (l k : Fin (r s)) (h : l < k) :
    genU Ω r s l k = 0 := by
  unfold genU
  rw [dif_neg (not_lt.2 h.le), if_neg h.ne]

theorem genU_one (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (l : Fin (r s)) :
    genU Ω r s l l = 1 := by
  unfold genU
  simp

theorem genU_gen (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (q : GenIx r) :
    genU Ω r q.1 q.2.1.1 q.2.1.2 = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) := by
  unfold genU
  rw [dif_pos q.2.2]
  rfl

theorem genU_indep (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) :
    AlgebraicIndependent Ω (fun q : GenIx r =>
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
  (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
    (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    (IsFractionRing.injective _ _)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
