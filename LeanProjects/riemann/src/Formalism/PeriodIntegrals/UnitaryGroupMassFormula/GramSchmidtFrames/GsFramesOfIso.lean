import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.FixOfPos

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

def IsoCore : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ y ∈ gfSig D0, ∀ α ∈ UWset k r z, ∀ β ∈ UWset k r z',
      α *ᵥ D0.nu = D0.nu → β⁻¹ *ᵥ D0.nu' = D0.nu' → (∀ u ∈ D0.U0, α *ᵥ (β *ᵥ u) = u) →
      ∃ m ∈ C2.N0set k r z, ∃ m' ∈ C2.N0set k r z', α * (m⁻¹ * y * m') * β = y

section aux

variable {k r : ℕ}

lemma uw_X {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {α : B.Mat k r} (hα : α ∈ UWset k r z)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ Xsp k r) : α *ᵥ v = v := by
  have hα' := hα
  unfold UWset at hα'
  simp only [Set.mem_setOf_eq] at hα'
  obtain ⟨-, hfix, -⟩ := hα'
  unfold Xsp at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact (hfix a).1
  | zero => exact Matrix.mulVec_zero α
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
  | smul c x _ hx => rw [Matrix.mulVec_smul, hx]

lemma uw_inWb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {α : B.Mat k r} (hα : α ∈ UWset k r z)
    {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) : inWb k r (α *ᵥ u) := by
  have hα' := hα
  unfold UWset at hα'
  simp only [Set.mem_setOf_eq] at hα'
  obtain ⟨hU, hfix, -⟩ := hα'
  unfold UH at hU
  simp only [Set.mem_setOf_eq] at hU
  have key : ∀ x w : Fin (2 * r + k + 1) → ℂ,
      star (α *ᵥ w) ⬝ᵥ (Hpk k r *ᵥ (α *ᵥ x)) = star w ⬝ᵥ (Hpk k r *ᵥ x) := by
    intro x w
    rw [Matrix.star_mulVec, ← dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, hU]
  have hstar : ∀ (w : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)),
      star w ⬝ᵥ Pi.single j 1 = star (w j) := by
    intro w j
    rw [dotProduct_single, mul_one]
    rfl
  have hHe : ∀ a : Fin r, Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
    intro a
    have ha := a.isLt
    funext i
    have hi := i.isLt
    unfold Hpk bvec eI esI
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_mk]
    split_ifs <;> first | rfl | omega | (simp only [Fin.ext_iff, Fin.val_mk] at *; omega)
  have hHe' : ∀ a : Fin r, Hpk k r *ᵥ bvec (eI k r a) = bvec (esI k r a) := by
    intro a
    have ha := a.isLt
    funext i
    have hi := i.isLt
    unfold Hpk bvec eI esI
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_mk]
    split_ifs <;> first | rfl | omega | (simp only [Fin.ext_iff, Fin.val_mk] at *; omega)
  intro i hi
  have hsi : star ((α *ᵥ u) i) = 0 := by
    rcases hi with hi | hi
    · have he : bvec (eI k r ⟨i, hi⟩) = Pi.single i 1 := by
        unfold bvec eI
        rfl
      calc star ((α *ᵥ u) i) = star (α *ᵥ u) ⬝ᵥ Pi.single i 1 := (hstar _ _).symm
        _ = star (α *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ (α *ᵥ bvec (esI k r ⟨i, hi⟩))) := by
          rw [(hfix _).2, hHe, he]
        _ = star u ⬝ᵥ (Hpk k r *ᵥ bvec (esI k r ⟨i, hi⟩)) := key _ _
        _ = star (u i) := by rw [hHe, he, hstar]
        _ = 0 := by rw [hu i (Or.inl hi), star_zero]
    · have hi2 := i.isLt
      have h' : 2 * r + k - (i : ℕ) < r := by omega
      have he : bvec (esI k r ⟨2 * r + k - i, h'⟩) = Pi.single i 1 := by
        unfold bvec esI
        dsimp only
        congr 1
        ext
        simp only [Fin.val_mk]
        omega
      calc star ((α *ᵥ u) i) = star (α *ᵥ u) ⬝ᵥ Pi.single i 1 := (hstar _ _).symm
        _ = star (α *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ (α *ᵥ bvec (eI k r ⟨2 * r + k - i, h'⟩))) := by
          rw [(hfix _).1, hHe', he]
        _ = star u ⬝ᵥ (Hpk k r *ᵥ bvec (eI k r ⟨2 * r + k - i, h'⟩)) := key _ _
        _ = star (u i) := by rw [hHe', he, hstar]
        _ = 0 := by rw [hu i (Or.inr hi), star_zero]
  exact star_eq_zero.mp hsi

lemma herm_X_wb {x z : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) (hz : inWb k r z) : herm (Hpk k r) x z = 0 := by
  unfold Xsp at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    unfold herm
    simp only [dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (i : ℕ) < r ∨ r + k < (i : ℕ)
    · simp [hz i hi]
    · push_neg at hi
      have ha := a.isLt
      have hsum : (Hpk k r *ᵥ bvec (eI k r a)) i = 0 := by
        unfold Hpk bvec eI
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_mk]
        split_ifs <;> first | rfl | (simp only [Fin.ext_iff, Fin.val_mk] at *; omega) | omega
      simp [hsum]
  | zero =>
    unfold herm
    rw [Matrix.mulVec_zero, dotProduct_zero]
  | add x y _ _ hx hy =>
    unfold herm at *
    rw [Matrix.mulVec_add, dotProduct_add, hx, hy, add_zero]
  | smul c x _ hx =>
    unfold herm at *
    rw [Matrix.mulVec_smul, dotProduct_smul, hx, smul_zero]

lemma X_wb_zero {v : Fin (2 * r + k + 1) → ℂ} (hX : v ∈ Xsp k r) (hW : inWb k r v) : v = 0 := by
  have hlow : ∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → v i = 0 := by
    clear hW
    unfold Xsp at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro i hi
      unfold bvec eI
      dsimp only
      rw [Pi.single_apply, if_neg]
      intro h
      have h1 := congrArg Fin.val h
      simp only [Fin.val_mk] at h1
      have := a.isLt
      omega
    | zero =>
      intro i _
      rfl
    | add x y _ _ hx hy =>
      intro i hi
      simp [hx i hi, hy i hi]
    | smul c x _ hx =>
      intro i hi
      simp [hx i hi]
  funext i
  by_cases hi : (i : ℕ) < r
  · exact hW i (Or.inl hi)
  · exact hlow i (by omega)

lemma det_ne_of_G {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {y : B.Mat k r}
    (hG : 0 < Gf k r z z' y) : (Zhat k r z z' y).det ≠ 0 := by
  have hD : Dmin k r z z' y (Fin.last (r + 1)) ≠ 0 := by
    intro h
    unfold Gf at hG
    rw [h, map_zero] at hG
    have := mul_nonneg (mul_nonneg hz.2.le hz'.2.le) (Complex.normSq_nonneg (Dmin k r z z' y ⟨r, by omega⟩))
    linarith
  unfold Dmin at hD
  have hid : (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt) : Fin (r + 1) → Fin (r + 1)) = id :=
    funext fun i => Fin.ext rfl
  rwa [hid, Matrix.submatrix_id_id] at hD

lemma lift_unique {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {y : B.Mat k r}
    (hG : 0 < Gf k r z z' y) {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r)
    (horth : ∀ a, herm (Hpk k r) (y *ᵥ x) (fvec k r z a) = 0) : x = 0 := by
  have hx' := (mem_Xsp_iff x).1 hx
  set c : Fin (r + 1) → ℂ := fun b => if h : b.val < r then x (eI k r ⟨b.val, h⟩) else 0 with hc
  have ex : x = ∑ b, c b • fvec k r z' b := by
    funext i
    rw [Finset.sum_apply]
    by_cases hi : i.val < r
    · rw [Finset.sum_eq_single ⟨i.val, by omega⟩]
      · have e1 : eI k r ⟨i.val, hi⟩ = i := Fin.ext (by simp [eI])
        simp [hc, hi, fvec, e1, bvec]
      · intro b _ hb
        simp only [Pi.smul_apply, smul_eq_mul, hc]
        split_ifs with h
        · have : i ≠ eI k r ⟨b.val, h⟩ := by
            intro e; apply hb; apply Fin.ext; have := congrArg Fin.val e; simp [eI] at this ⊢; omega
          simp [fvec, h, bvec, this]
        · simp
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [hx' i (by omega)]
      symm
      refine Finset.sum_eq_zero fun b _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, hc]
      split_ifs with h
      · have : i ≠ eI k r ⟨b.val, h⟩ := by
          intro e; have := congrArg Fin.val e; simp [eI] at this; omega
        simp [fvec, h, bvec, this]
      · simp
  have hZc : Zhat k r z z' y *ᵥ c = 0 := by
    funext a
    have := horth a
    rw [ex, mv_sum] at this
    simp only [mulVec_smul] at this
    rw [hm_sum_l] at this
    simp only [mulVec, dotProduct, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => by simp only [Zhat]; ring
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero (det_ne_of_G hz hz' hG) hZc
  rw [ex, hc0]
  simp

end aux

theorem stabCore_of (hI : IsoCore) : StabCore := by
  intro k r z z' hk hr hz hz' D0 y hy α hα β hβ hν hν' hay
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have Gz := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz
  have Gz' := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz'
  have hαi := Wz.inv_mem α hα
  have hβu := Wz'.unit β hβ
  have hαu := Wz.unit α hα
  have hβν : β *ᵥ D0.nu' = D0.nu' := by
    conv_lhs => rw [← hν']
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hβu, one_mulVec]
  have hαβ : ∀ u ∈ D0.U0, α *ᵥ (β *ᵥ u) = u := by
    intro u hu
    obtain ⟨⟨huW, huz⟩, huν⟩ := (D0.isotropic_subspace_eq u).1 hu
    obtain ⟨⟨_, huz'⟩, huν'⟩ := (D0.isotropic_subspace_eq_primed u).1 hu
    have hbW : inWb k r (β *ᵥ u) := uw_inWb hz'.1 hβ huW
    have hbU : β *ᵥ u ∈ D0.U0 := by
      refine (D0.isotropic_subspace_eq_primed _).2 ⟨⟨hbW, ?_⟩, ?_⟩
      · conv_lhs => rw [← hβ.2.2]
        rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hβ.1]; exact huz'
      · conv_lhs => rw [← hβν]
        rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hβ.1]; exact huν'
    obtain ⟨⟨_, hbz⟩, _⟩ := (D0.isotropic_subspace_eq _).1 hbU
    obtain ⟨v, hv, v', hv', e1⟩ := hy.2.2.2.2 (β *ᵥ u) hbU
    obtain ⟨w, hw, w', hw', e2⟩ := hay.2.2.2.2 u hu

    have e3 : y *ᵥ (β *ᵥ u + w') = α⁻¹ *ᵥ u + w := by
      have h : α⁻¹ *ᵥ ((α * y * β) *ᵥ (u + w')) = α⁻¹ *ᵥ u + w := by
        rw [e2, mulVec_add, uw_X hz.1 hαi hw]
      rw [← h, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hαu,
        Matrix.one_mul, ← mulVec_mulVec, Matrix.mulVec_add β u w', uw_X hz'.1 hβ hw']
    have hx0 : w' - v' ∈ Xsp k r := Submodule.sub_mem _ hw' hv'
    have e4 : y *ᵥ (w' - v') = (α⁻¹ *ᵥ u - β *ᵥ u) + (w - v) := by
      have : w' - v' = (β *ᵥ u + w') - (β *ᵥ u + v') := by abel
      rw [this, mulVec_sub, e3, e1]; abel
    have hαiW : inWb k r (α⁻¹ *ᵥ u) := uw_inWb hz.1 hαi huW
    have hαiz : herm (Hpk k r) (α⁻¹ *ᵥ u) z = 0 := by
      conv_lhs => rw [← hαi.2.2]
      rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hαi.1]; exact huz
    have hdW : inWb k r (α⁻¹ *ᵥ u - β *ᵥ u) := by
      intro i hi; simp [hαiW i hi, hbW i hi]
    have hwv : w - v ∈ Xsp k r := Submodule.sub_mem _ hw hv
    have hx00 : w' - v' = 0 := by
      refine lift_unique hz hz' hy.2.1 hx0 fun a => ?_
      rw [e4, hm_add_l]
      unfold fvec
      split_ifs with ha
      · rw [herm_bvec_eI, herm_bvec_eI, (mem_Xsp_iff _).1 hwv _ (by simp [esI]; omega),
          hdW _ (Or.inr (by simp [esI]; omega)), add_zero]
      · rw [hm_sub_l, hαiz, hbz, sub_zero, herm_X_wb hwv hz.1, add_zero]
    rw [hx00, mulVec_zero] at e4
    have hd0 : α⁻¹ *ᵥ u - β *ᵥ u = 0 := by
      have hd : α⁻¹ *ᵥ u - β *ᵥ u = -(w - v) := by rw [eq_neg_iff_add_eq_zero]; exact e4.symm
      refine X_wb_zero ?_ hdW
      rw [hd]; exact Submodule.neg_mem _ hwv
    rw [← sub_eq_zero.1 hd0, mulVec_mulVec, Matrix.mul_nonsing_inv _ hαu, one_mulVec]
  obtain ⟨m, hm, m', hm', e⟩ := hI k r z z' hk hr hz hz' D0 y hy α hα β hβ hν hν' hαβ
  refine ⟨1, Gz.one_mem, m, hm, 1, Gz'.one_mem, m', hm', α, hα, β, hβ, ?_, e⟩
  rw [Matrix.inv_eq_left_inv (Matrix.mul_one (1 : B.Mat k r))]
  simp

theorem gfStab_of_iso (hI : IsoCore) : GfStab := gfStab_of (stabCore_of hI)

end PI.UnitaryGroupMassFormula.GsFr
