import Mathlib
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaE
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BigCellLocal

noncomputable section

namespace PositivityTheory.ThKH.Iwas

open Matrix Formalism.UG Formalism.UG.P GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

def ee (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (m + m) := (Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv

theorem antiJ_submatrix (L : Type) [Field L] (m : ℕ) :
    (antiJ L (m + m)).submatrix (ee m) (ee m) = Wm L (Fin m) := by
  ext (i | i) (j | j)
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply,
      finSumFinEquiv_apply_left, Fin.val_castAdd, fromBlocks_apply₁₁, Matrix.zero_apply]
    rw [if_neg (by omega)]
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
      fromBlocks_apply₁₂, Matrix.one_apply, Fin.revPerm_apply, Fin.val_rev, Fin.ext_iff]
    exact if_congr (by omega) rfl rfl
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.refl_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
      fromBlocks_apply₂₁, Matrix.one_apply, Fin.revPerm_apply, Fin.val_rev, Fin.ext_iff]
    exact if_congr (by omega) rfl rfl
  · have := i.2; have := j.2
    simp only [submatrix_apply, antiJ, ee, Wm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
      finSumFinEquiv_apply_right, Fin.val_natAdd, fromBlocks_apply₂₂, Matrix.zero_apply, Fin.revPerm_apply, Fin.val_rev]
    rw [if_neg (by omega)]

theorem Wm_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (β : Type) [DecidableEq β] :
    (Wm A β).map f = Wm B β := by
  ext (i | i) (j | j) <;> simp [Wm, Matrix.one_apply, apply_ite f]

section

variable {L : Type} [Field L] {c : L →+* L} {β : Type} [Fintype β] [DecidableEq β]

theorem iso_iff_cT (hc : ∀ x, c (c x) = x) (M : Matrix (β ⊕ β) (β ⊕ β) L) :
    Iso c (Wm L β) (Wm L β) M ↔ cT c M * Wm L β * M = Wm L β := by
  have hcc : ∀ N : Matrix (β ⊕ β) (β ⊕ β) L, (N.map c).map c = N := fun N => Matrix.ext fun i j => hc _
  constructor
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, Wm_map, hcc] at this
    exact this
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, Wm_map] at this
    rw [cT, transpose_map, hcc] at this
    exact this

theorem inv_eq_of_iso (hc : ∀ x, c (c x) = x) {M N : Matrix (β ⊕ β) (β ⊕ β) L} (h : Iso c (Wm L β) (Wm L β) M)
    (hN : M * N = 1) : N = Wm L β * cT c M * Wm L β := by
  have h1 := (iso_iff_cT hc M).1 h
  have h2 : Wm L β * cT c M * Wm L β * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT c M), h1, Wm_mul_self]
  calc N = (Wm L β * cT c M * Wm L β * M) * N := by rw [h2, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc _ M, hN, Matrix.mul_one]

theorem inv_apply_of_iso (hc : ∀ x, c (c x) = x) {M N : Matrix (β ⊕ β) (β ⊕ β) L} (h : Iso c (Wm L β) (Wm L β) M)
    (hN : M * N = 1) (i j : β ⊕ β) : N i j = c (M j.swap i.swap) := by
  rw [inv_eq_of_iso hc h hN]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Wm, cT, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

end

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}

theorem exists_reduce (hc : ∀ x, c (c x) = x) (hv : ∀ x, Valued.v (c x) = Valued.v x) {m : ℕ}
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) (hM : Iso c (Wm L (Fin m)) (Wm L (Fin m)) M) :
    ∃ k, Iso c (Wm L (Fin m)) (Wm L (Fin m)) k ∧ (∀ i j, Valued.v (k i j) ≤ 1) ∧
      ∀ i j, (k * M) (Sum.inr i) (Sum.inl j) = 0 := by
  have hW : antiJ L (m + m) = (Wm L (Fin m)).submatrix (ee m).symm (ee m).symm := by
    rw [← antiJ_submatrix]; simp
  have h1 : fIwasawaUn c (M.submatrix (ee m).symm (ee m).symm) := by
    unfold fIwasawaUn
    rw [hW]
    change (cT c M).submatrix (ee m).symm (ee m).symm * _ * _ = _
    rw [submatrix_mul_equiv, submatrix_mul_equiv, (iso_iff_cT hc M).1 hM]
  obtain ⟨k, hk, hT⟩ := fIwasawa_upper c hc hv _ h1
  refine ⟨k.submatrix (ee m) (ee m), (iso_iff_cT hc _).2 ?_, fun i j => hk.2 _ _, fun i j => ?_⟩
  · rw [← antiJ_submatrix]
    change (cT c k).submatrix (ee m) (ee m) * _ * _ = _
    rw [submatrix_mul_equiv, submatrix_mul_equiv, hk.1]
  · have e : k.submatrix (ee m) (ee m) * M = (k * M.submatrix (ee m).symm (ee m).symm).submatrix (ee m) (ee m) := by
      rw [← submatrix_mul_equiv k _ (ee m) (ee m) (ee m)]; simp
    rw [e]
    refine hT ?_
    have := j.2
    change (ee m (Sum.inl j)).val < (ee m (Sum.inr i)).val
    simp only [ee, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]
    omega

theorem group_main {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ c q) {m : ℕ} {G : Type} [Group G] (U : Subgroup G)
    (Φ : G →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) (hiso : ∀ g, Iso c (Wm L (Fin m)) (Wm L (Fin m)) (Φ g))
    (inj : ∀ g ∈ U, ∀ g' ∈ U, Φ g = Φ g' → g = g')
    (surj : ∀ M, Iso c (Wm L (Fin m)) (Wm L (Fin m)) M → ∃ g ∈ U, Φ g = M) (K P : Set G)
    (hK : ∀ g, g ∈ K ↔ g ∈ U ∧ (∀ i j, Valued.v (Φ g i j) ≤ 1) ∧ ∀ i j, Valued.v (Φ g⁻¹ i j) ≤ 1)
    (hP : ∀ g ∈ U, (∀ i j, Φ g (Sum.inr i) (Sum.inl j) = 0) → g ∈ P) :
    (∀ h ∈ U, ∃ p ∈ P, ∃ k ∈ K, h = p * k) ∧
    ∀ χ : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, χ (k * k') = χ k * χ k') → (∀ k ∈ K, k ∈ P → χ k = 1) → ∀ k ∈ K, χ k = 1 := by
  obtain ⟨hc, hv, -, -, ⟨x, hx, hx1⟩, -, -⟩ := hU
  have hinv : ∀ g i j, Φ g⁻¹ i j = c (Φ g j.swap i.swap) := fun g =>
    inv_apply_of_iso hc (hiso g) (by rw [← map_mul, mul_inv_cancel, map_one])
  have hK' : ∀ g ∈ U, (∀ i j, Valued.v (Φ g i j) ≤ 1) → g ∈ K := fun g hg h =>
    (hK g).2 ⟨hg, h, fun i j => by rw [hinv, hv]; exact h _ _⟩
  refine ⟨fun h hh => ?_, fun χ hχ h1 k hk => ?_⟩
  · obtain ⟨k, hk1, hk2, hk3⟩ := exists_reduce hc hv _ (hiso h⁻¹)
    obtain ⟨g, hg, rfl⟩ := surj k hk1
    refine ⟨(g * h⁻¹)⁻¹, hP _ (inv_mem (mul_mem hg (inv_mem hh))) fun i j => ?_, g, hK' g hg hk2, by group⟩
    rw [hinv, map_mul]
    exact (congrArg c (hk3 j i)).trans (map_zero c)
  · let A : Subring L := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring.toSubring
    haveI : IsLocalRing A :=
      inferInstanceAs (IsLocalRing (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)
    have hA : ∀ z, z ∈ A ↔ Valued.v z ≤ 1 := fun _ => Iff.rfl
    let σ : A →+* A := c.restrict A A fun z hz => by rw [hA, hv]; exact hz
    have hσσ : ∀ z, σ (σ z) = z := fun z => Subtype.ext (hc z)
    have hx0 : c x - x ≠ 0 := by
      intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
    have hxi : (c x - x)⁻¹ ∈ A := by rw [hA, map_inv₀, hx1, inv_one]
    have hz : IsUnit (σ ⟨x, hx⟩ - σ (σ ⟨x, hx⟩)) := by
      rw [hσσ]
      exact IsUnit.of_mul_eq_one ⟨_, hxi⟩ (Subtype.ext (mul_inv_cancel₀ hx0))
    have hw : σ ⟨x, hx⟩ * ⟨_, hxi⟩ + σ (σ ⟨x, hx⟩ * ⟨_, hxi⟩) = 1 := Subtype.ext (by
      change c x * (c x - x)⁻¹ + c (c x * (c x - x)⁻¹) = 1
      rw [map_mul, map_inv₀, map_sub, hc, ← neg_sub (c x) x, inv_neg]
      field_simp
      ring)
    have hmap : ∀ N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A,
        Iso σ (Wm A (Fin m)) (Wm A (Fin m)) N ↔ Iso c (Wm L (Fin m)) (Wm L (Fin m)) (N.map A.subtype) := fun N => by
      unfold Iso
      rw [← Wm_map A.subtype, ← transpose_map]
      change _ ↔ _ * _ * (N.map σ).map A.subtype = _
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      exact (Matrix.map_injective A.subtype_injective).eq_iff.symm
    have lift : ∀ N, Iso σ (Wm A (Fin m)) (Wm A (Fin m)) N → ∃ g ∈ U, g ∈ K ∧ Φ g = N.map A.subtype := fun N hN => by
      obtain ⟨g, hg, e⟩ := surj _ ((hmap N).1 hN)
      exact ⟨g, hg, hK' g hg fun i j => by rw [e]; exact (N i j).2, e⟩
    obtain ⟨hkU, hk1, -⟩ := (hK k).1 hk
    let H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A := Matrix.of fun i j => ⟨_, hk1 i j⟩
    have eH : H.map A.subtype = Φ k := rfl
    obtain ⟨s, u, t, b, d, i1, i2, i3, -, e⟩ := decomp_split hσσ hw hz ((hmap H).2 (eH ▸ hiso k))
    obtain ⟨g1, u1, k1, e1⟩ := lift _ i1
    obtain ⟨g2, u2, k2, e2⟩ := lift _ i2
    obtain ⟨g3, u3, k3, e3⟩ := lift _ i3
    obtain ⟨w, uw, kw, ew⟩ := lift _ (iso_Wm (σ := σ) (β := Fin m))
    have hmul : ∀ g ∈ K, ∀ g' ∈ K, g * g' ∈ K := fun g hg g' hg' => by
      obtain ⟨a1, a2, -⟩ := (hK g).1 hg
      obtain ⟨b1, b2, -⟩ := (hK g').1 hg'
      refine hK' _ (mul_mem a1 b1) fun i j => ?_
      rw [map_mul, Matrix.mul_apply]
      exact A.sum_mem fun l _ => A.mul_mem (a2 _ _) (b2 _ _)
    have p1 : χ g1 = 1 := h1 _ k1 (hP _ u1 fun i j => by rw [e1]; rfl)
    have p2 : χ g2 = 1 := h1 _ k2 (hP _ u2 fun i j => by rw [e2]; rfl)
    have p3 : χ g3 = 1 := h1 _ k3 (hP _ u3 fun i j => by rw [e3]; rfl)
    have pw : χ w * χ w = 1 := by
      rw [← hχ w kw w kw]
      refine h1 _ (hmul _ kw _ kw) (hP _ (mul_mem uw uw) fun i j => ?_)
      rw [map_mul, ew, ← Matrix.map_mul, Wm_mul_self]
      simp
    have ek : k = g1 * (w * g2 * w) * g3 :=
      inj _ hkU _ (mul_mem (mul_mem u1 (mul_mem (mul_mem uw u2) uw)) u3) (by
        rw [← eH, e]
        simp only [map_mul, Matrix.map_mul, e1, e2, e3, ew])
    rw [ek, hχ _ (hmul _ k1 _ (hmul _ (hmul _ kw _ k2) _ kw)) _ k3, hχ _ k1 _ (hmul _ (hmul _ kw _ k2) _ kw),
      hχ _ (hmul _ kw _ k2) _ kw, hχ _ kw _ k2, p1, p2, p3, mul_one, mul_one, one_mul, pw]

end PositivityTheory.ThKH.Iwas
