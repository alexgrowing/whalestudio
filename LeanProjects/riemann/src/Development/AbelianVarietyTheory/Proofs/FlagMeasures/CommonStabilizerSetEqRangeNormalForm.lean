import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorphStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructureStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.CommonStab

variable {k r j : ℕ}

theorem mv {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (p i : Fin m) : (M *ᵥ bvec p) i = M i p := by simp [bvec]

theorem bv {m : ℕ} (p i : Fin m) : bvec p i = if i = p then 1 else 0 := by simp [bvec, Pi.single_apply]

theorem bv_ne {m : ℕ} {p i : Fin m} (h : i ≠ p) : bvec p i = 0 := by simp [bv, h]

theorem van_map {m : ℕ} {P Q : Fin m → Prop} (M : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ)
    (hM : ∀ i p, Q i → ¬ P p → M i p = 0) (hv : ∀ p, P p → v p = 0) (i : Fin m) (hi : Q i) : (M *ᵥ v) i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases h : P p
  · rw [hv p h, mul_zero]
  · rw [hM i p hi h, zero_mul]

theorem xst_coord {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ XstJ k r j) (i : Fin (2 * r + k + 1))
    (hi : ∀ b : Fin r, b.val < j → i ≠ esI k r b) : v i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact bv_ne (hi a.1 a.2)
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem es_inj {a b : Fin r} : esI k r a = esI k r b ↔ a = b := by
  simp only [esI, Fin.ext_iff]; omega

theorem e_inj {a b : Fin r} : eI k r a = eI k r b ↔ a = b := by
  simp only [eI, Fin.ext_iff]

theorem w_inj {a b : Fin (k + 1)} : wI k r a = wI k r b ↔ a = b := by
  simp only [wI, Fin.ext_iff]; omega

theorem e_ne_es (a b : Fin r) : eI k r a ≠ esI k r b := by
  simp only [eI, esI, ne_eq, Fin.ext_iff]; omega

theorem e_ne_w (a : Fin r) (b : Fin (k + 1)) : eI k r a ≠ wI k r b := by
  simp only [eI, wI, ne_eq, Fin.ext_iff]; omega

theorem w_ne_es (a : Fin (k + 1)) (b : Fin r) : wI k r a ≠ esI k r b := by
  simp only [wI, esI, ne_eq, Fin.ext_iff]; omega

theorem nf {hj : j ≤ r} {β : Fin r → ℕ} {c : ℂ} {z z' : Fin (2 * r + k + 1) → ℂ} {G : Mat k r}
    (h : IsNormal0 k r hj β c z z' G) :
    (∀ b : Fin r, b.val < j → ∃ a : Fin r, a.val < j ∧ G (esI k r b) (eI k r a) ≠ 0) ∧
    (∀ a : Fin r, a.val < j → ∃ b : Fin r, b.val < j ∧ G (esI k r b) (eI k r a) ≠ 0) ∧
    (∀ a b : Fin r, a.val < j → b.val < j → G (esI k r b) (eI k r a) ≠ 0 →
      β b = β a ∧ G *ᵥ bvec (eI k r a) = G (esI k r b) (eI k r a) • bvec (esI k r b)) ∧
    (∀ a b a' b' : Fin r, a.val < j → b.val < j → a'.val < j → b'.val < j → G (esI k r b) (eI k r a) ≠ 0 →
      G (esI k r b') (eI k r a') ≠ 0 → β b = β b' → b < b' → a' < a) := by
  obtain ⟨-, -, -, -, -, hX, -, -, hdet, hblk, hord⟩ := h
  have h3 : ∀ a b : Fin r, a.val < j → b.val < j → G (esI k r b) (eI k r a) ≠ 0 → β b = β a :=
    fun a b ha hb h => hblk ⟨b.val, hb⟩ ⟨a.val, ha⟩ h
  have h4 : ∀ a b a' b' : Fin r, a.val < j → b.val < j → a'.val < j → b'.val < j → G (esI k r b) (eI k r a) ≠ 0 →
      G (esI k r b') (eI k r a') ≠ 0 → β b = β b' → b < b' → a' < a :=
    fun a b a' b' ha hb ha' hb' h h' hβ hlt =>
      (hord ⟨b.val, hb⟩ ⟨a.val, ha⟩ ⟨b'.val, hb'⟩ ⟨a'.val, ha'⟩ h h' hβ).2.2 hlt
  refine ⟨fun b hb => ?_, fun a ha => ?_, fun a b ha hb h => ⟨h3 a b ha hb h, ?_⟩, h4⟩
  · by_contra hc
    push Not at hc
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero ⟨b.val, hb⟩ fun a => hc (Fin.castLE hj a) a.2)
  · by_contra hc
    push Not at hc
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero ⟨a.val, ha⟩ fun b => hc (Fin.castLE hj b) b.2)
  · funext i
    by_cases hi : i = esI k r b
    · subst hi; simp [mv, bv]
    · rw [Pi.smul_apply, bv_ne hi, smul_zero]
      by_cases hi' : ∀ b' : Fin r, b'.val < j → i ≠ esI k r b'
      · exact xst_coord (hX a ha).2 i hi'
      · push Not at hi'
        obtain ⟨b', hb', rfl⟩ := hi'
        rw [mv]
        by_contra hne
        have hβ : β b = β b' := (h3 a b ha hb h).trans (h3 a b' ha hb' hne).symm
        rcases lt_trichotomy b b' with hlt | heq | hlt
        · exact lt_irrefl _ (h4 a b a b' ha hb ha hb' h hne hβ hlt)
        · exact hi (by rw [heq])
        · exact lt_irrefl _ (h4 a b' a b ha hb' ha hb hne h hβ.symm hlt)

theorem isClosed_N : IsClosed (Nset k r) := by
  unfold Nset UH
  simp only [Set.ofPred_and, Set.ofPred_forall, Set.mem_ofPred_eq]
  refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_const) (IsClosed.inter ?_ ?_)
  · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const

theorem closedSub {g : Mat k r} (hg : IsUnit g.det) : IsClosedSub k r (Rset k r g) := by
  obtain ⟨n1, n2, n3⟩ := nSubgroup k r
  refine ⟨fun x hx => hx.1.1, ?_, ⟨n1, ?_⟩, fun a ha b hb => ⟨n2 _ ha.1 _ hb.1, ?_⟩, fun a ha => ⟨n3 _ ha.1, ?_⟩⟩
  · exact isClosed_N.inter (isClosed_N.preimage (f := fun x : Mat k r => g * x * g⁻¹) (by fun_prop))
  · rw [mul_one, Matrix.mul_nonsing_inv _ hg]; exact n1
  · have := n2 _ ha.2 _ hb.2
    rwa [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hg]] at this
  · have := n3 _ ha.2
    rwa [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hg, ← Matrix.mul_assoc] at this

theorem col_zero {hj : j ≤ r} {β : Fin r → ℕ} {c : ℂ} {z z' : Fin (2 * r + k + 1) → ℂ} {g ρ : Mat k r}
    (hg : IsUnit g.det) (h : IsNormal0 k r hj β c z z' g⁻¹) (hρ : ρ ∈ Rset k r g) (b : Fin r) (hb : b.val < j)
    (i : Fin (2 * r + k + 1)) (hi : ∀ b' : Fin r, b'.val < j → β b' ≤ β b → i ≠ esI k r b') :
    ρ i (esI k r b) = 0 := by
  obtain ⟨h1, h2, h3, -⟩ := nf h
  have hmon : Monotone β := h.2.2.2.1
  obtain ⟨a, ha, hY⟩ := h1 b hb
  obtain ⟨hβ, hG⟩ := h3 a b ha hb hY
  have e1 : ρ *ᵥ (g⁻¹ *ᵥ bvec (eI k r a)) = g⁻¹ *ᵥ ((g * ρ * g⁻¹) *ᵥ bvec (eI k r a)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hg]
  have e2 : (g⁻¹ *ᵥ ((g * ρ * g⁻¹) *ᵥ bvec (eI k r a))) i = 0 := by
    refine van_map (P := fun p => a.val < p.val) (Q := fun i' => i' = i) _ _ ?_ ?_ i rfl
    · rintro i' p rfl hp
      have hp' : p.val < j := by omega
      obtain ⟨b', hb', hY'⟩ := h2 ⟨p.val, by omega⟩ hp'
      obtain ⟨hβ', hG'⟩ := h3 ⟨p.val, by omega⟩ b' hp' hb' hY'
      have := congrFun hG' i'
      rw [mv, Pi.smul_apply, bv_ne (hi b' hb' ?_), smul_zero] at this
      · exact this
      · rw [hβ, hβ']; exact hmon (by rw [Fin.le_def]; simpa using hp)
    · intro p hp
      rw [mv, hρ.2.2.1 a p hp.le, if_neg]
      rintro rfl
      exact lt_irrefl _ hp
  rw [← e1, hG, Matrix.mulVec_smul, Pi.smul_apply, mv, smul_eq_mul] at e2
  exact (mul_eq_zero.1 e2).resolve_left hY

theorem upper_tri (x : UT r → ℂ) : (upper x).BlockTriangular id := by
  intro a b h
  have h : b < a := h
  simp [upper, h.not_gt, h.ne']

theorem upper_diag (x : UT r → ℂ) (a : Fin r) : upper x a a = 1 := by simp [upper]

theorem upper_unit (x : UT r → ℂ) : IsUnit (upper x).det := by
  rw [((GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties 0 r).2.2.2 x).1]; exact isUnit_one

theorem inv_tri {α : Type} [LinearOrder α] {u : Matrix (Fin r) (Fin r) ℂ} (hu : IsUnit u.det) {β : Fin r → α}
    (h : u.BlockTriangular β) : u⁻¹.BlockTriangular β := by
  let _ := Matrix.invertibleOfIsUnitDet u hu
  exact Matrix.blockTriangular_inv_of_blockTriangular h

theorem inv_diag (x : UT r → ℂ) (a : Fin r) : (upper x)⁻¹ a a = 1 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul _ (upper_unit x)) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, upper_diag, mul_one] at h
  · simpa using h
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h1 | h1
    · rw [inv_tri (upper_unit x) (upper_tri x) h1, zero_mul]
    · rw [upper_tri x h1, mul_zero]
  · simp

theorem upperIn_tri (β : Fin r → ℕ) (x : UTin β → ℂ) : (upperIn β x).BlockTriangular (OrderDual.toDual ∘ β) := by
  intro a b h
  have h : β a < β b := h
  have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ h
  simp [upperIn, upper, h.ne, hab]

theorem col_es {u : Matrix (Fin r) (Fin r) ℂ} (hu : IsUnit u.det) (B : Fin r → Fin (k + 1) → ℂ)
    (S : Matrix (Fin r) (Fin r) ℂ) (b : Fin r) :
    (uEmb k r u * pEl k r B S) *ᵥ bvec (esI k r b) = (∑ a, star (u⁻¹ b a) • bvec (esI k r a)) +
      (∑ i, B b i • bvec (wI k r i)) +
      ∑ a, (S a b - herm (Hb k) (B b) (B a) / 2) • ∑ a', u a' a • bvec (eI k r a') := by
  obtain ⟨-, -, h1, h2, h3⟩ := (GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties k r).2.2.1 u hu
  have hw : ∀ i, uEmb k r u *ᵥ bvec (wI k r i) = bvec (wI k r i) := fun i => h3 _ fun p hp => bv_ne (by
    rintro rfl; simp only [wI] at hp; omega)
  rw [← Matrix.mulVec_mulVec, ((GlobalTheory.T.isotropicStabilizerRadical_structure k r).1 B S).2.2.1 b]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, h1, h2, hw]

theorem herm_zero_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) : herm H 0 v = 0 := by simp [herm]

theorem herm_zero_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) : herm H v 0 = 0 := by simp [herm]

theorem subset_range {hj : j ≤ r} {β : Fin r → ℕ} {c : ℂ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r}
    (hg : IsUnit g.det) (h : IsNormal0 k r hj β c z z' g⁻¹) : Rset k r g ⊆ Set.range (rEl k r j β) := by
  intro ρ hρ
  obtain ⟨⟨x, B, s, t⟩, -, hq⟩ := (GlobalTheory.T.unipotent_levi_radical_coords_homeomorph k r).1.2.2 hρ.1
  have hq : uEmb k r (upper x) * pEl k r B (skewM s t) = ρ := hq
  have hmon : Monotone β := h.2.2.2.1
  have hlast := h.2.2.2.2.1
  have hu := upper_unit x
  have hc := fun (b : Fin r) i => congrFun (col_es hu B (skewM s t) b) i
  simp only [hq, mv] at hc
  have hB : ∀ b : Fin r, b.val < j → B b = 0 := fun b hb => by
    funext i
    have := col_zero hg h hρ b hb (wI k r i) fun b' _ _ => w_ne_es _ _
    rw [hc] at this
    simpa [Finset.sum_apply, bv, w_ne_es, w_inj, (e_ne_w _ _).symm] using this
  have hS : ∀ a b : Fin r, b.val < j → skewM s t a b = 0 := fun a b hb => by
    have : upper x *ᵥ (fun a => skewM s t a b) = 0 := by
      funext a'
      have := col_zero hg h hρ b hb (eI k r a') fun b' _ _ => e_ne_es _ _
      rw [hc, hB b hb] at this
      simpa [Finset.sum_apply, bv, e_ne_es, e_inj, e_ne_w, herm_zero_left, Matrix.mulVec, dotProduct, mul_comm]
        using this
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hu.ne_zero this) a
  have hui : (upper x)⁻¹.BlockTriangular (OrderDual.toDual ∘ β) := by
    intro b a hab
    have hab : β b < β a := hab
    have hb : b.val < j := by
      by_contra hb
      have hba : b ≤ a := by
        by_contra hba
        exact absurd (hmon (not_le.1 hba).le) hab.not_ge
      exact hab.ne' ((hlast a b (by omega)).2 (by rw [Fin.le_def] at hba; omega))
    have := col_zero hg h hρ b hb (esI k r a) fun b' _ h' h'' => by
      rw [es_inj.1 h''] at hab; omega
    rw [hc] at this
    simpa [Finset.sum_apply, bv, (w_ne_es _ _).symm, es_inj, (e_ne_es _ _).symm] using this
  have hu' := inv_tri (Matrix.isUnit_nonsing_inv_det _ hu) hui
  rw [Matrix.nonsing_inv_nonsing_inv _ hu] at hu'
  refine ⟨(fun p => x p.1, fun a => B a.1, fun p => s p.1, fun a => t a.1), ?_⟩
  rw [← hq]
  unfold rEl upperIn pTop pOf
  congr 3
  · funext p
    split_ifs with hp
    · rfl
    · have := hu' (i := p.1.1) (j := p.1.2) (show β p.1.1 < β p.1.2 from lt_of_le_of_ne (hmon p.2.le) hp)
      simp only [upper, p.2, dif_pos] at this
      exact this.symm
  · funext a
    dsimp only
    split_ifs with ha
    · rfl
    · exact (hB a (by omega)).symm
  · funext p
    dsimp only
    split_ifs with hp
    · rfl
    · have := hS p.1.2 p.1.1 (by omega)
      simp only [skewM, p.2, p.2.not_gt, dif_pos, dif_neg, not_false_eq_true, neg_eq_zero, star_eq_zero] at this
      exact this.symm
  · funext a
    dsimp only
    split_ifs with ha
    · rfl
    · have := hS a a (by omega)
      simpa [skewM, eq_comm] using this

theorem range_subset {hj : j ≤ r} {β : Fin r → ℕ} {c c' : ℂ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r}
    (hg : IsUnit g.det) (h0 : IsNormal0 k r hj β c' z' z g) (h : IsNormal0 k r hj β c z z' g⁻¹)
    (hW : ∀ w, inWb k r w → inWb k r (g⁻¹ *ᵥ w)) (hcc : c * c' = 1) :
    Set.range (rEl k r j β) ⊆ Rset k r g := by
  rintro _ ⟨⟨x, q⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, upperIn β x = upper y := ⟨_, rfl⟩
  obtain ⟨B, s, t, hp, hB, hS⟩ : ∃ B s t, pTop k r j q = pEl k r B (skewM s t) ∧ (∀ a : Fin r, a.val < j → B a = 0) ∧
      ∀ a b : Fin r, b.val < j → skewM s t a b = 0 := by
    refine ⟨_, _, _, rfl, fun a ha => dif_neg (by omega), fun a b hb => ?_⟩
    unfold skewM
    split_ifs with h1 h2
    · exact dif_neg (by rw [Fin.lt_def] at h1; simp only; omega)
    · dsimp only
      rw [dif_neg (by omega)]; simp
    · have : a = b := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      subst this
      simp only
      rw [dif_neg (by omega)]; simp
  have hblk : (upper y).BlockTriangular (OrderDual.toDual ∘ β) := hy ▸ upperIn_tri β x
  have hρ : rEl k r j β (x, q) = uEmb k r (upper y) * pEl k r B (skewM s t) := by
    unfold rEl; rw [← hy, ← hp]
  rw [hρ]
  have hu := upper_unit y
  have hmon : Monotone β := h.2.2.2.1
  have hlast := h.2.2.2.2.1
  obtain ⟨h1, h2, h3, h4⟩ := nf h
  obtain ⟨-, -, u1, -, u3⟩ := (GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties k r).2.2.1 _ hu
  obtain ⟨p1, -, -, p4⟩ := (GlobalTheory.T.isotropicStabilizerRadical_structure k r).1 B (skewM s t)
  have hN : uEmb k r (upper y) * pEl k r B (skewM s t) ∈ Nset k r :=
    (nSubgroup k r).2.1 _ ((GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties k r).2.2.2 y).2 _ (p4 ((GlobalTheory.T.isotropicStabilizerRadical_structure k r).2.1 s t)).1
  obtain ⟨-, g2, -⟩ := uHGroup _ (Hpk k r) (by
    have := congrArg Matrix.det (hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ this)
  have hgg : ∀ v, g *ᵥ (g⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hg, Matrix.one_mulVec]
  have hges : ∀ a b : Fin r, a.val < j → b.val < j → g⁻¹ (esI k r b) (eI k r a) ≠ 0 → ∀ i,
      g⁻¹ (esI k r b) (eI k r a) * g i (esI k r b) = bvec (eI k r a) i := fun a b ha hb hY i => by
    have := congrFun (hgg (bvec (eI k r a))) i
    rwa [(h3 a b ha hb hY).2, Matrix.mulVec_smul, Pi.smul_apply, mv, smul_eq_mul] at this
  have hutop : ∀ a b : Fin r, a.val < j → j ≤ b.val → upper y a b = 0 := fun a b ha hb =>
    hblk (show β a < β b from lt_of_le_of_ne (hmon (by rw [Fin.le_def]; omega))
      fun he => by have := (hlast a b hb).1 he; omega)
  refine ⟨hN, g2 _ (g2 _ h0.1 _ hN.1) _ h.1, fun a i hi => ?_, fun i p hp1 hp2 hi => ?_⟩
  · rw [← mv (g * _ * _), ← bv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    by_cases ha : a.val < j
    · obtain ⟨b, hb, hY⟩ := h2 a ha
      rw [(h3 a b ha hb hY).2, Matrix.mulVec_smul, col_es hu, hB b hb]
      simp only [hS _ b hb, herm_zero_left, Pi.zero_apply, zero_smul, zero_div, sub_zero, Finset.sum_const_zero,
        add_zero, Matrix.mulVec_smul, Matrix.mulVec_sum, Pi.smul_apply, Finset.sum_apply, mv, smul_eq_mul]
      rw [Finset.sum_eq_single b, inv_diag, star_one, one_mul, hges a b ha hb hY]
      · intro b' _ hb'
        by_cases hz : (upper y)⁻¹ b b' = 0
        · rw [hz, star_zero, zero_mul]
        have e1 : b < b' := lt_of_le_of_ne (not_lt.1 fun hlt => hz (inv_tri hu (upper_tri y) hlt)) hb'.symm
        have e2 : β b = β b' := le_antisymm (hmon e1.le) (not_lt.1 fun hlt => hz (inv_tri hu hblk hlt))
        have e3 : b'.val < j := by
          by_contra hc
          have := (hlast b b' (by omega)).1 e2
          omega
        obtain ⟨a', ha', hY'⟩ := h1 b' e3
        have e4 := h4 a b a' b' ha hb ha' e3 hY hY' e2 e1
        have e5 := hges a' b' ha' e3 hY' i
        rw [bv_ne (by rintro rfl; simp only [eI] at hi; rw [Fin.lt_def] at e4; omega)] at e5
        rw [(mul_eq_zero.1 e5).resolve_left hY', mul_zero]
      · simp
    · rw [(h.2.2.2.2.2.2.1 a (by omega)).1, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, p1, u1]
      simp only [Matrix.mulVec_smul, Matrix.mulVec_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_eq_single a, upper_diag, one_mul, (h0.2.2.2.2.2.2.1 a (by omega)).1, Pi.smul_apply, smul_eq_mul,
        ← mul_assoc, hcc, one_mul]
      · intro a' _ ha'
        by_cases e1 : a'.val < j
        · rw [hutop a' a e1 (by omega), zero_mul]
        rcases lt_or_gt_of_ne ha' with e2 | e2
        · rw [(h0.2.2.2.2.2.2.1 a' (by omega)).1, Pi.smul_apply,
            bv_ne (by rintro rfl; simp only [eI] at hi; rw [Fin.lt_def] at e2; omega), smul_zero, mul_zero]
        · rw [upper_tri y e2, zero_mul]
      · simp
  · rw [← mv (g * _ * _), ← bv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hw : inWb k r (g⁻¹ *ᵥ bvec p) := hW _ fun i' hi' => bv_ne (by rintro rfl; omega)
    have e0 : pEl k r B (skewM s t) *ᵥ (g⁻¹ *ᵥ bvec p) =
        g⁻¹ *ᵥ bvec p + (pEl k r B (skewM s t) - 1) *ᵥ (g⁻¹ *ᵥ bvec p) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e0, Matrix.mulVec_add, u3 _ hw, Matrix.mulVec_add, hgg, Pi.add_apply, add_eq_left]
    refine van_map (P := fun i' => ¬ (j ≤ i'.val ∧ i'.val < r)) (Q := fun i' => r ≤ i'.val) _ _ ?_ ?_ i hi
    · intro i' p' hi' hp'
      have hp' := not_not.1 hp'
      have := congrFun (h0.2.2.2.2.2.2.1 ⟨p'.val, hp'.2⟩ hp'.1).1 i'
      rw [mv, Pi.smul_apply, bv_ne (by rintro rfl; simp only [eI] at hi'; omega), smul_zero] at this
      exact this
    refine van_map (P := fun i' => ¬ (j ≤ i'.val ∧ i'.val < r)) _ _ ?_ ?_
    · intro i' p' hi' hp'
      have hp' := not_not.1 hp'
      have := congrFun (u1 ⟨p'.val, hp'.2⟩) i'
      rw [mv, Finset.sum_apply, Finset.sum_eq_zero] at this
      · exact this
      · intro a _
        by_cases ha : a.val < j
        · rw [hutop a _ ha hp'.1, zero_smul]; rfl
        · rw [Pi.smul_apply, bv_ne (by rintro rfl; exact hi' ⟨by simp only [eI]; omega, a.2⟩), smul_zero]
    refine van_map (P := fun i' => i'.val < r ∨ r + k < i'.val) _ _ ?_ hw
    intro i' p' hi' hp'
    rw [Matrix.sub_apply, Matrix.one_apply]
    unfold pEl
    split_ifs with c1 c2 c3 c4
    · simp
    · rw [hB _ (by simp only; omega), herm_zero_right]; simp
    · omega
    · omega
    · simp

end GlobalTheory.Amp.CommonStab

namespace GlobalTheory.Amp

open CommonStab in

theorem rset_normal0 : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → Rset k r g₀ = Set.range (rEl k r j β) ∧ IsClosedSub k r (Rset k r g₀) := by
  intro k r j hj z z' g β c hz hz' hT h
  obtain ⟨hT', -, h', -⟩ := GlobalTheory.T.normalFormFlagZero_middle_inverse_minor_orthogonal k r j hj z z' g β c hz hz' hT h
  obtain ⟨-, ⟨m, -, hm⟩, -⟩ := GlobalTheory.T.normalFormFlagZero_middle_inverse_minor_orthogonal k r j hj z' z g⁻¹ β c⁻¹ hz' hz (hT' ▸ hT) h'
  obtain ⟨-, -, g3⟩ := uHGroup _ (Hpk k r) (by
    have := congrArg Matrix.det (hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ this)
  have hg := (g3 g h.1).1
  have hc : c ≠ 0 := by
    rintro rfl
    simpa using h.2.1
  refine ⟨Set.Subset.antisymm (subset_range hg h') (range_subset hg h h' (fun w hw => ?_) (inv_mul_cancel₀ hc)),
    closedSub hg⟩
  rw [hm w hw]
  refine van_map (P := fun i' => i'.val < r ∨ r + k < i'.val) _ _ ?_ hw
  intro i p hi hp
  unfold mEmb
  rw [dif_neg (by omega), if_neg (by rintro rfl; exact hp hi)]

end GlobalTheory.Amp
