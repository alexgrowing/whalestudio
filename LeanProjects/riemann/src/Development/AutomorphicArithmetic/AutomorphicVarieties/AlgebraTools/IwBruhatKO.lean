import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools.BruhatKO

open DoubleCoset

variable {n : ℕ} {k : Type} [Field k]

private lemma mul_pm_apply (M : Matrix (Fin n) (Fin n) k) (σ : Equiv.Perm (Fin n)) (r c : Fin n) :
    (M * (pm k n σ : Matrix (Fin n) (Fin n) k)) r c = M r (σ c) := by
  simp [mul_apply, pm_apply]

private lemma pm_mul_apply (M : Matrix (Fin n) (Fin n) k) (σ : Equiv.Perm (Fin n)) (r c : Fin n) :
    ((pm k n σ : Matrix (Fin n) (Fin n) k) * M) r c = M (σ⁻¹ r) c := by
  rw [mul_apply, Fintype.sum_eq_single (σ⁻¹ r)]
  · simp [pm_apply]
  · intro a ha
    rw [pm_apply, if_neg, zero_mul]
    rintro rfl
    exact ha (by simp)

private lemma borel_diag_ne_zero {b : GL (Fin n) k} (hb : b ∈ borel k (Fin n)) (i : Fin n) :
    (b : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
  have hdet : (b : Matrix (Fin n) (Fin n) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  rw [det_of_isUpperTriangular (fun i j h => (mem_borel _).1 hb i j h)] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)

private lemma exists_borel_of_isUpperTriangular (M : Matrix (Fin n) (Fin n) k)
    (hM : M.IsUpperTriangular) (hd : ∀ i, M i i ≠ 0) :
    ∃ b ∈ borel k (Fin n), (b : Matrix (Fin n) (Fin n) k) = M := by
  have hdet : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, det_of_isUpperTriangular hM, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  obtain ⟨u, hu⟩ := hdet
  refine ⟨u, ?_, hu⟩
  refine (mem_borel _).2 fun i j h => ?_
  rw [hu]
  exact hM h

private lemma mul_one_add_vecMulVec_apply (M : Matrix (Fin n) (Fin n) k) (j : Fin n) (v : Fin n → k)
    (r c : Fin n) :
    (M * (1 + vecMulVec (Pi.single j 1) v)) r c = M r c + M r j * v c := by
  simp [Matrix.mul_add, mul_vecMulVec, vecMulVec_apply]

private lemma one_add_vecMulVec_mul_apply (M : Matrix (Fin n) (Fin n) k) (i : Fin n) (u : Fin n → k)
    (r c : Fin n) :
    ((1 + vecMulVec u (Pi.single i 1)) * M) r c = M r c + u r * M i c := by
  simp [Matrix.add_mul, vecMulVec_mul, vecMulVec_apply]

private lemma perm_eq_one_of_forall_le (π : Equiv.Perm (Fin n)) (h : ∀ x, π x ≤ x) : π = 1 := by
  have hsum : ∑ x, ((π x : Fin n) : ℕ) = ∑ x : Fin n, (x : ℕ) :=
    Equiv.sum_comp π (fun x : Fin n => (x : ℕ))
  have heq := (Finset.sum_eq_sum_iff_of_le
    (fun x _ => Fin.le_iff_val_le_val.mp (h x))).mp hsum
  exact Equiv.ext fun x => by simpa using Fin.ext (heq x (Finset.mem_univ _))

private def RowsReduced (M : Matrix (Fin n) (Fin n) k) (t : ℕ) : Prop :=
  ∃ p : Fin n → Fin n, ∀ i : Fin n, t ≤ i.val →
    M i (p i) ≠ 0 ∧ (∀ c, c ≠ p i → M i c = 0) ∧ (∀ r, r ≠ i → M r (p i) = 0)

private lemma rowsReduced_step (h : GL (Fin n) k) (t : ℕ) (ht : t < n)
    (hred : RowsReduced (h : Matrix (Fin n) (Fin n) k) (t + 1)) :
    ∃ b₁ ∈ borel k (Fin n), ∃ b₂ ∈ borel k (Fin n),
      RowsReduced ((b₁ * h * b₂ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) t := by
  classical
  obtain ⟨p, hp⟩ := hred
  set H : Matrix (Fin n) (Fin n) k := (h : Matrix (Fin n) (Fin n) k) with hH
  set i₀ : Fin n := ⟨t, ht⟩ with hi₀
  have hne : ∀ i : Fin n, t + 1 ≤ i.val → i₀ ≠ i := by
    intro i hi e
    have := congrArg Fin.val e
    simp [i₀] at this
    omega

  have hrow : ∃ c, H i₀ c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
      (Matrix.det_eq_zero_of_row_eq_zero i₀ hcon)

  set s := Finset.univ.filter (fun c => H i₀ c ≠ 0) with hs_def
  have hs : s.Nonempty := let ⟨c, hc⟩ := hrow; ⟨c, by simp [s, hc]⟩
  set j := s.min' hs with hj_def
  have hj : H i₀ j ≠ 0 := (Finset.mem_filter.mp (s.min'_mem hs)).2
  have hjmin : ∀ c, c < j → H i₀ c = 0 := fun c hc => by
    by_contra hc0
    exact absurd (s.min'_le c (by simp [s, hc0])) (not_le.mpr hc)
  have hpS : ∀ i : Fin n, t + 1 ≤ i.val → H i₀ (p i) = 0 :=
    fun i hi => (hp i hi).2.2 i₀ (hne i hi)
  have hjp : ∀ i : Fin n, t + 1 ≤ i.val → p i ≠ j := fun i hi e => hj (e ▸ hpS i hi)
  have hHj : ∀ r : Fin n, t + 1 ≤ r.val → H r j = 0 :=
    fun r hr => (hp r hr).2.1 j (hjp r hr).symm

  set v : Fin n → k := fun c => if j < c then -(H i₀ c / H i₀ j) else 0 with hv
  set E₂ : Matrix (Fin n) (Fin n) k := 1 + vecMulVec (Pi.single j 1) v with hE₂
  have hE₂up : E₂.IsUpperTriangular := by
    intro a c hca
    replace hca : c < a := hca
    simp only [E₂, Matrix.add_apply, one_apply, vecMulVec_apply, Pi.single_apply]
    rw [if_neg (ne_of_lt hca).symm]
    by_cases haj : a = j
    · subst haj
      simp [v, not_lt.mpr hca.le]
    · simp [haj]
  have hE₂d : ∀ a, E₂ a a ≠ 0 := by
    intro a
    simp only [E₂, Matrix.add_apply, one_apply_eq, vecMulVec_apply, Pi.single_apply]
    by_cases haj : a = j
    · subst haj; simp [v]
    · simp [haj]
  obtain ⟨b₂, hb₂, hb₂E⟩ := exists_borel_of_isUpperTriangular E₂ hE₂up hE₂d
  set M₁ : Matrix (Fin n) (Fin n) k := H * E₂ with hM₁_def
  have hM₁ : ∀ r c, M₁ r c = H r c + H r j * v c := fun r c =>
    mul_one_add_vecMulVec_apply H j v r c
  have hM₁i₀ : ∀ c, M₁ i₀ c = if c = j then H i₀ j else 0 := by
    intro c
    rw [hM₁]
    rcases lt_trichotomy c j with hc | rfl | hc
    · simp [v, hjmin c hc, not_lt.mpr hc.le, (ne_of_lt hc)]
    · simp [v]
    · simp only [v, if_pos hc, if_neg (ne_of_lt hc).symm]
      field_simp
      ring
  have hM₁S : ∀ r : Fin n, t + 1 ≤ r.val → ∀ c, M₁ r c = H r c := by
    intro r hr c
    rw [hM₁, hHj r hr, zero_mul, add_zero]
  have hvp : ∀ i : Fin n, t + 1 ≤ i.val → v (p i) = 0 := by
    intro i hi
    simp [v, hpS i hi]

  set u : Fin n → k := fun r => if r < i₀ then -(M₁ r j / H i₀ j) else 0 with hu_def
  set E₁ : Matrix (Fin n) (Fin n) k := 1 + vecMulVec u (Pi.single i₀ 1) with hE₁
  have hE₁up : E₁.IsUpperTriangular := by
    intro a c hca
    replace hca : c < a := hca
    simp only [E₁, Matrix.add_apply, one_apply, vecMulVec_apply, Pi.single_apply]
    rw [if_neg (ne_of_lt hca).symm]
    by_cases hci : c = i₀
    · subst hci
      simp [u, not_lt.mpr hca.le]
    · simp [hci]
  have hE₁d : ∀ a, E₁ a a ≠ 0 := by
    intro a
    simp only [E₁, Matrix.add_apply, one_apply_eq, vecMulVec_apply, Pi.single_apply]
    by_cases hai : a = i₀
    · subst hai; simp [u]
    · simp [hai]
  obtain ⟨b₁, hb₁, hb₁E⟩ := exists_borel_of_isUpperTriangular E₁ hE₁up hE₁d
  set M₂ : Matrix (Fin n) (Fin n) k := E₁ * M₁ with hM₂_def
  have hM₂ : ∀ r c, M₂ r c = M₁ r c + u r * M₁ i₀ c := fun r c =>
    one_add_vecMulVec_mul_apply M₁ i₀ u r c
  have hu0 : ∀ r : Fin n, t ≤ r.val → u r = 0 := by
    intro r hr
    have : ¬ r < i₀ := by
      rw [Fin.lt_def]
      simp [i₀]
      omega
    simp [u, this]
  have hM₂j : ∀ r : Fin n, r.val < t → M₂ r j = 0 := by
    intro r hr
    have hlt : r < i₀ := by
      rw [Fin.lt_def]
      simpa [i₀] using hr
    rw [hM₂, hM₁i₀ j, if_pos rfl]
    simp only [u, if_pos hlt]
    field_simp
    ring
  have hval : ((b₁ * h * b₂ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = M₂ := by
    rw [Units.val_mul, Units.val_mul, hb₁E, hb₂E, mul_assoc]
  refine ⟨b₁, hb₁, b₂, hb₂, ?_⟩
  rw [hval]
  refine ⟨Function.update p i₀ j, fun i hi => ?_⟩
  rcases Nat.eq_or_lt_of_le hi with hti | hti
  ·
    have hii : i = i₀ := Fin.ext (by simp [i₀, hti])
    subst hii
    rw [Function.update_self]
    refine ⟨?_, ?_, ?_⟩
    · rw [hM₂, hu0 _ le_rfl, zero_mul, add_zero, hM₁i₀, if_pos rfl]
      exact hj
    · intro c hc
      rw [hM₂, hu0 _ le_rfl, zero_mul, add_zero, hM₁i₀, if_neg hc]
    · intro r hr
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hr) with hlt | hgt
      · exact hM₂j r (by simpa [i₀] using hlt)
      · have hr' : t + 1 ≤ r.val := by simp [i₀] at hgt; omega
        rw [hM₂, hu0 r (by omega), zero_mul, add_zero, hM₁S r hr', hHj r hr']
  ·
    have hi' : t + 1 ≤ i.val := hti
    rw [Function.update_of_ne (hne i hi').symm]
    obtain ⟨h1, h2, h3⟩ := hp i hi'
    refine ⟨?_, ?_, ?_⟩
    · rw [hM₂, hu0 i hi, zero_mul, add_zero, hM₁S i hi']
      exact h1
    · intro c hc
      rw [hM₂, hu0 i hi, zero_mul, add_zero, hM₁S i hi']
      exact h2 c hc
    · intro r hr
      rw [hM₂, hM₁i₀, if_neg (hjp i hi'), mul_zero, add_zero, hM₁, hvp i hi', mul_zero,
        add_zero]
      exact h3 r hr

private lemma exists_eq_mul_pm_of_rowsReduced (g : GL (Fin n) k)
    (hred : RowsReduced (g : Matrix (Fin n) (Fin n) k) 0) :
    ∃ σ : Equiv.Perm (Fin n), ∃ b ∈ borel k (Fin n), g = b * pm k n σ := by
  classical
  obtain ⟨p, hp⟩ := hred
  have hinj : Function.Injective p := by
    intro i i' e
    by_contra hii
    exact (hp i' (Nat.zero_le _)).1 (e ▸ (hp i (Nat.zero_le _)).2.2 i' (Ne.symm hii))
  set τ : Equiv.Perm (Fin n) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj)
  have hτ : ∀ i, τ i = p i := fun i => rfl
  set d : Fin n → k := fun i => (g : Matrix (Fin n) (Fin n) k) i (p i)
  obtain ⟨b, hb, hbD⟩ := exists_borel_of_isUpperTriangular (diagonal d)
    (blockTriangular_diagonal d) (fun i => by simpa [d] using (hp i (Nat.zero_le _)).1)
  refine ⟨τ⁻¹, b, hb, ?_⟩
  ext r c
  rw [Units.val_mul, mul_pm_apply, hbD, diagonal_apply]
  by_cases hc : c = p r
  · subst hc
    rw [if_pos (by rw [← hτ]; simp)]
  · rw [(hp r (Nat.zero_le _)).2.1 c hc, if_neg]
    intro e
    apply hc
    rw [← hτ, e]
    simp

private theorem exists_mem_doubleCoset_pm (g : GL (Fin n) k) :
    ∃ σ : Equiv.Perm (Fin n), g ∈ doubleCoset (pm k n σ) (borel k (Fin n)) (borel k (Fin n)) := by
  have key : ∀ d, d ≤ n → ∃ b₁ ∈ borel k (Fin n), ∃ b₂ ∈ borel k (Fin n),
      RowsReduced ((b₁ * g * b₂ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (n - d) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨1, (borel k (Fin n)).one_mem, 1, (borel k (Fin n)).one_mem, id, fun i hi => ?_⟩
      have := i.isLt
      omega
    | succ d ih =>
      intro hd
      obtain ⟨b₁, hb₁, b₂, hb₂, hred⟩ := ih (by omega)
      have ht : n - (d + 1) + 1 = n - d := by omega
      rw [← ht] at hred
      obtain ⟨c₁, hc₁, c₂, hc₂, hred'⟩ := rowsReduced_step _ (n - (d + 1)) (by omega) hred
      refine ⟨c₁ * b₁, (borel k (Fin n)).mul_mem hc₁ hb₁, b₂ * c₂, (borel k (Fin n)).mul_mem hb₂ hc₂, ?_⟩
      simpa only [mul_assoc] using hred'
  obtain ⟨b₁, hb₁, b₂, hb₂, hred⟩ := key n le_rfl
  rw [Nat.sub_self] at hred
  obtain ⟨σ, b, hb, hgb⟩ := exists_eq_mul_pm_of_rowsReduced _ hred
  refine ⟨σ, mem_doubleCoset.mpr ⟨b₁⁻¹ * b, (borel k (Fin n)).mul_mem ((borel k (Fin n)).inv_mem hb₁) hb,
    b₂⁻¹, (borel k (Fin n)).inv_mem hb₂, ?_⟩⟩
  rw [mul_assoc b₁⁻¹, ← hgb]
  group

private theorem eq_of_pm_mem_doubleCoset {σ τ : Equiv.Perm (Fin n)}
    (h : pm k n τ ∈ doubleCoset (pm k n σ) (borel k (Fin n)) (borel k (Fin n))) : σ = τ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp h
  have hy' : y⁻¹ ∈ borel k (Fin n) := (borel k (Fin n)).inv_mem hy
  have hmat : (x : Matrix (Fin n) (Fin n) k) * (pm k n σ : Matrix (Fin n) (Fin n) k) =
      (pm k n τ : Matrix (Fin n) (Fin n) k) * ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [← Units.val_mul, ← Units.val_mul, hxy]
    congr 1
    group
  have hle : ∀ a, τ a ≤ σ a := by
    intro a
    have hent := congrFun (congrFun hmat (τ a)) a
    rw [mul_pm_apply, pm_mul_apply] at hent
    by_contra hlt
    push Not at hlt
    have h0 := (mem_borel _).mp hx (τ a) (σ a) hlt
    rw [hent, show τ⁻¹ (τ a) = a from τ.symm_apply_apply a] at h0
    exact borel_diag_ne_zero hy' a h0
  have hπ := perm_eq_one_of_forall_le (τ * σ⁻¹) (fun x => by
    simpa using hle (σ⁻¹ x))
  have := congrArg (· * σ) hπ
  simpa using this.symm

private theorem doubleCoset_pm_injective {σ τ : Equiv.Perm (Fin n)} {g : GL (Fin n) k}
    (hσ : g ∈ doubleCoset (pm k n σ) (borel k (Fin n)) (borel k (Fin n)))
    (hτ : g ∈ doubleCoset (pm k n τ) (borel k (Fin n)) (borel k (Fin n))) : σ = τ := by
  have e : doubleCoset (pm k n σ) (borel k (Fin n)) (borel k (Fin n)) =
      doubleCoset (pm k n τ) (borel k (Fin n)) (borel k (Fin n)) :=
    (doubleCoset_eq_of_mem hσ).symm.trans (doubleCoset_eq_of_mem hτ)
  have hmem := mem_doubleCoset_self (borel k (Fin n)) (borel k (Fin n)) (pm k n τ)
  rw [← e] at hmem
  exact eq_of_pm_mem_doubleCoset hmem

private theorem map_pm {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (w : Equiv.Perm (Fin n)) :
    GeneralLinearGroup.map (n := Fin n) f (pm R n w) = pm S n w := by
  ext i j
  show f ((pm R n w : Matrix (Fin n) (Fin n) R) i j) = _
  rw [pm_apply, pm_apply]
  split_ifs <;> simp

private theorem red_surj {O : Type} [CommRing O] [IsLocalRing O] :
    Function.Surjective (GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue O)) := by
  intro g
  choose s hs using IsLocalRing.residue_surjective (R := O)
  let M : Matrix (Fin n) (Fin n) O := (g : Matrix (Fin n) (Fin n) _).map s
  have hM : (IsLocalRing.residue O).mapMatrix M = g := by
    ext i j
    exact hs _
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hM]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, ?_⟩
  ext i j
  show IsLocalRing.residue O ((u : Matrix (Fin n) (Fin n) O) i j) = _
  rw [hu]
  exact hs _

end UpperTheory.V.AlgebraTools.BruhatKO

open UpperTheory.V.AlgebraTools.BruhatKO in
theorem UpperTheory.V.AlgebraTools.bruhatKO :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), (∀ w : Equiv.Perm (Fin n), pm k n w ∈ KO k (Fin n)) ∧ ∀ g ∈ KO k (Fin n), ∃! w : Equiv.Perm (Fin n), ∃ a ∈ iwahori k (Fin n), ∃ b ∈ iwahori k (Fin n), g = a * pm k n w * b := by
  intro k _ _ _ _ n
  refine ⟨fun w => ⟨pm 𝒪[k] n w, map_pm _ w⟩, ?_⟩
  rintro _ ⟨g, rfl⟩
  set ι := GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) with hι
  set r := GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]) with hr
  have hinj : Function.Injective ι := by
    intro x y h
    ext i j
    exact congrArg (fun z : GL (Fin n) k => (z : Matrix (Fin n) (Fin n) k) i j) h
  have key : ∀ w : Equiv.Perm (Fin n),
      (∃ a ∈ iwahori k (Fin n), ∃ b ∈ iwahori k (Fin n), ι g = a * pm k n w * b) ↔
        r g ∈ DoubleCoset.doubleCoset (pm 𝓀[k] n w) (borel 𝓀[k] (Fin n)) (borel 𝓀[k] (Fin n)) := by
    intro w
    have e1 : ι (pm 𝒪[k] n w) = pm k n w := map_pm _ w
    have e2 : r (pm 𝒪[k] n w) = pm 𝓀[k] n w := map_pm _ w
    rw [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, h⟩
      have h' : g = a * pm 𝒪[k] n w * b := hinj (by rw [map_mul, map_mul, e1]; exact h)
      exact ⟨r a, ha, r b, hb, by rw [h', map_mul, map_mul, e2]⟩
    · rintro ⟨x, hx, y, hy, h⟩
      obtain ⟨b, rfl⟩ := red_surj y
      refine ⟨ι (g * b⁻¹ * (pm 𝒪[k] n w)⁻¹), ⟨_, ?_, rfl⟩, ι b, ⟨b, hy, rfl⟩, ?_⟩
      · show r _ ∈ borel 𝓀[k] (Fin n)
        have : r (g * b⁻¹ * (pm 𝒪[k] n w)⁻¹) = x := by
          rw [map_mul, map_mul, map_inv, map_inv, h, e2]
          exact (by group : x * pm 𝓀[k] n w * r b * (r b)⁻¹ * (pm 𝓀[k] n w)⁻¹ = x)
        rw [this]; exact hx
      · rw [← e1, ← map_mul, ← map_mul]
        congr 1
        group
  obtain ⟨w, hw⟩ := exists_mem_doubleCoset_pm (r g)
  exact ⟨w, (key w).2 hw, fun v hv => doubleCoset_pm_injective ((key v).1 hv) hw⟩
