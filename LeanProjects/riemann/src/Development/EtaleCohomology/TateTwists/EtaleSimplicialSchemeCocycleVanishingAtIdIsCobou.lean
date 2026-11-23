import Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainExistsFromNaturalSections

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma cob_altsum (k : ℕ) : ∑ i : Fin k, (-1 : ℤ) ^ (i : ℕ) = if k % 2 = 0 then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have : (j + j) % 2 = 0 := by omega
      have h2 : (j + j + 1) % 2 ≠ 0 := by omega
      simp [this, h2, ← two_mul, pow_mul]
    · have : (2 * j + 1) % 2 ≠ 0 := by omega
      have h2 : (2 * j + 1 + 1) % 2 = 0 := by omega
      simp [this, h2, pow_succ, pow_mul]

lemma cob_map_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℤ) (z : Sec F U) :
    Sec.map φ (c • z) = c • Sec.map φ z := by
  simp [Sec.map]

lemma cob_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := by
  simp [Sec.map]

lemma cob_res_zsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℤ) (z : Sec F U) :
    Sec.res g (c • z) = c • Sec.res g z := by
  simp [Sec.res]

end LateralTheory.EtaleFoundations

namespace LateralTheory.EtaleFoundations

noncomputable def cobB {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n : ℤ) (hmn : m + 1 = n)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + m = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U :=
  fun p s h U x => if p % 2 = 1 then ((n.negOnePow : ℤ)) • ev α (p + 1) s (by push_cast; omega) U
    (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) else 0

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etaleSimplicialScheme_cocycle_vanishing_at_id_isCoboundary_of_evaluati (hmk : EtaleSimplicialCochainExistsFromNaturalSections) (hdl : EtaleSimplicialCochainEvaluationDifferentialFormula)
    (hb : EtaleSimplicialCochainEvaluationProperties) : EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary := by
  intro R _ X I m n hmn α h0
  have hεε : (n.negOnePow : ℤ) * (n.negOnePow : ℤ) = 1 := by
    rw [← Units.val_mul, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul]; rfl

  have hnat : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (cobB X I m n hmn α.1 p s h U x) = cobB X I m n hmn α.1 p s h V (x.res g) := by
    intro p s h V U g x
    unfold cobB
    split_ifs
    · rw [cob_res_zsmul]
      exact congrArg (((n.negOnePow : ℤ)) • ·) ((hb R).2.1 α.1 (p + 1) s _ V U g (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)))
    · simp [Sec.res]
  obtain ⟨β, hβ⟩ := hmk R (cobB X I m n hmn α.1) hnat
  refine ⟨β, ?_⟩

  have hα0 : ∀ U (x : Sx (sch.obj X) 0 U), ev α.1 0 n (by simp) U x = 0 := by
    intro U x
    have e : ev α.1 0 n (by simp) U x = Sec.res (x : U ⟶ X) (ev α.1 0 n (by simp) X (𝟙 X)) := by
      rw [(hb R).2.1 α.1 0 n (by simp) U X x (𝟙 X)]; rfl
    rw [e, h0]; simp [Sec.res]

  have hcyc : ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 2 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + n = t) U
      (x : Sx (sch.obj X) (p + 2) U), p % 2 = 0 →
      Sec.map (I.d s t) (ev α.1 (p + 2) s hs U x) = (n.negOnePow : ℤ) • ev α.1 (p + 1) t ht U
        (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) := by
    intro p s t hs ht U x hp
    have e := (hdl R rfl α.1 U).2 (p + 1) s t hs (by push_cast at ht ⊢; omega) x
    rw [Cocycle.δ_eq_zero, ((hb R (E := sch.obj X) (I := I) (n := n + 1)).1 0 0 (p + 1 + 1) t _ U x).2.2.1] at e
    have hsum : ∑ i : Fin (p + 1 + 2), (-1 : ℤ) ^ (i : ℕ) • ev α.1 (p + 1) t (by push_cast at ht ⊢; omega) U (x.face i)
        = (∑ i : Fin (p + 1 + 2), (-1 : ℤ) ^ (i : ℕ)) • ev α.1 (p + 1) t ht U
          (show Sx (sch.obj X) (p + 1) U from (x : U ⟶ X)) := by
      rw [Finset.sum_smul]; rfl
    rw [hsum, cob_altsum, if_neg (by omega), one_smul, Int.negOnePow_succ, Units.smul_def] at e
    rw [eq_comm, add_eq_zero_iff_eq_neg] at e
    rw [e]; simp
  apply (hb R).2.2.1
  intro p s h U x
  cases p with
  | zero =>
    obtain rfl : s = n := by omega
    rw [(hdl R hmn β U).1 x, hβ, hα0]
    simp [cobB, cob_map_zero]
  | succ p =>
    rw [(hdl R hmn β U).2 p (-((p + 1 : ℕ) : ℤ) + m) s rfl h x]
    simp only [hβ]
    have hsum : ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • cobB X I m n hmn α.1 p s (by push_cast at h ⊢; omega) U (x.face i)
        = (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ)) • cobB X I m n hmn α.1 p s (by push_cast at h ⊢; omega) U
          (show Sx (sch.obj X) p U from (x : U ⟶ X)) := by
      rw [Finset.sum_smul]; rfl
    rw [hsum, cob_altsum, Units.smul_def]
    rcases Nat.even_or_odd p with ⟨j, rfl⟩ | ⟨j, rfl⟩
    ·
      have h1 : (j + j + 1) % 2 = 1 := by omega
      have h2 : (j + j + 2) % 2 = 0 := by omega
      simp only [cobB, h1, h2, ↓reduceIte, zero_smul, smul_zero, add_zero]
      rw [cob_map_zsmul]
      have hc := hcyc (j + j) (-((j + j + 1 : ℕ) : ℤ) + m) s (by push_cast; omega) (by push_cast at h ⊢; omega) U x (by omega)
      erw [hc]
      rw [smul_smul, hεε, one_smul]
    · have h1 : (2 * j + 1 + 1) % 2 = 0 := by omega
      have h2 : (2 * j + 1 + 2) % 2 = 1 := by omega
      have h3 : (2 * j + 1) % 2 = 1 := by omega
      simp only [cobB, h1, h2, h3, ↓reduceIte, one_ne_zero, one_smul, smul_smul]
      rw [if_neg (by omega), cob_map_zero, zero_add, one_mul, hεε, one_smul]
