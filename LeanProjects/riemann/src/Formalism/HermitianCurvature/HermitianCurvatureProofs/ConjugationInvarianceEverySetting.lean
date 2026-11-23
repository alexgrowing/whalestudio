import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B2x4

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section form
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

lemma herm_sum (u v : Fin m → ℂ) : ∑ j, herm H (bvec j) v * u j = herm H u v := by
  simp only [herm, dotProduct, mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma herm_add_left (u u' w : Fin m → ℂ) : herm H (u + u') w = herm H u w + herm H u' w := by
  simp only [herm, mulVec_add, dotProduct_add]

lemma herm_sub_left (u u' w : Fin m → ℂ) : herm H (u - u') w = herm H u w - herm H u' w := by
  simp only [herm, mulVec_sub, dotProduct_sub]

lemma herm_smul_left (c : ℂ) (u w : Fin m → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma herm_add_right (u w w' : Fin m → ℂ) : herm H u (w + w') = herm H u w + herm H u w' := by
  simp only [herm, star_add, add_dotProduct]

lemma herm_sub_right (u w w' : Fin m → ℂ) : herm H u (w - w') = herm H u w - herm H u w' := by
  simp only [herm, star_sub, sub_dotProduct]

lemma herm_smul_right (c : ℂ) (u w : Fin m → ℂ) : herm H u (c • w) = star c * herm H u w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

lemma herm_symm (hH : Hᴴ = H) (u w : Fin m → ℂ) : star (herm H u w) = herm H w u := by
  unfold herm
  rw [← Matrix.star_dotProduct_star, star_star, star_mulVec, hH, ← dotProduct_mulVec]

lemma herm_bvec (i j : Fin m) : herm H (bvec j) (bvec i) = H i j := by
  simp [herm, bvec, dotProduct, mulVec, Pi.single_apply]

lemma herm_mulVec (g : Matrix (Fin m) (Fin m) ℂ) (u w : Fin m → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ w) = herm (gᴴ * H * g) u w := by
  unfold herm
  rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star w) gᴴ]

lemma mem_UH_of_herm (g : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ u w, herm H (g *ᵥ u) (g *ᵥ w) = herm H u w) : g ∈ UH H := by
  show gᴴ * H * g = H
  ext i j
  rw [← herm_bvec (gᴴ * H * g), ← herm_mulVec, h, herm_bvec]

lemma heis_isom (hH : Hᴴ = H) (e v : Fin m → ℂ) (b : ℂ) (hee : herm H e e = 0) (hve : herm H v e = 0)
    (hb : b + star b + herm H v v = 0) (u w : Fin m → ℂ) :
    herm H (u - herm H u v • e + herm H u e • (v + b • e)) (w - herm H w v • e + herm H w e • (v + b • e)) =
      herm H u w := by
  have hev : herm H e v = 0 := by rw [← herm_symm H hH v e, hve, star_zero]
  simp only [herm_add_left, herm_sub_left, herm_smul_left, herm_add_right, herm_sub_right, herm_smul_right,
    herm_symm H hH, hee, hve, hev]
  linear_combination (herm H u e * herm H e w) * hb

end form

def lastI (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

lemma Hpk_herm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1

lemma Hpk_zero_row (k r' : ℕ) (j : Fin (2 * (1 + r') + k + 1)) :
    Hpk k (1 + r') (eI k (1 + r') (a0 r')) j = if j.val = 2 * (1 + r') + k then 1 else 0 := by
  have hv : (eI k (1 + r') (a0 r')).val = 0 := rfl
  unfold Hpk
  split_ifs <;> first | rfl | (exfalso; omega)

lemma hermitian_first_basis_right (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u (e0 k r') = u (lastI k r') := by
  rw [← herm_sum]
  rw [Finset.sum_eq_single (lastI k r')]
  · rw [e0, herm_bvec, Hpk_zero_row, if_pos (show (lastI k r').val = 2 * (1 + r') + k from rfl), one_mul]
  · intro j _ hj
    have : j.val ≠ 2 * (1 + r') + k := fun h => hj (Fin.ext h)
    rw [e0, herm_bvec, Hpk_zero_row, if_neg this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma hermitian_form_base_vector_left (k r' : ℕ) (w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (e0 k r') w = star (w (lastI k r')) := by
  rw [← herm_symm _ (Hpk_herm k (1 + r')), hermitian_first_basis_right]

lemma goodRowsProjector_apply_eq_sum (k r' : ℕ) (i : Fin (2 * (1 + r') + k + 1)) : e0 k r' i = if i.val = 0 then 1 else 0 := by
  simp only [e0, bvec, eI, a0, Pi.single_apply, Fin.ext_iff]

lemma liftVec_last (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (lastI k r') = 0 := by
  unfold liftVec lastI
  rw [dif_neg (by simp only []; omega)]

lemma sum_lift (k r' : ℕ) (F : Fin (2 * (1 + r') + k + 1) → ℂ)
    (h : ∀ p, ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) → F p = 0) :
    ∑ p, F p = ∑ j, F (levPos k 1 r' j) := by
  symm
  apply Finset.sum_of_injOn (levPos k 1 r')
  · intro a _ b _ hab
    have := congrArg Fin.val hab
    simp only [levPos] at this
    exact Fin.ext (by omega)
  · intro a _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  · intro p _ hp
    apply h
    intro hc
    apply hp
    refine ⟨⟨p.val - 1, by omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
    apply Fin.ext
    simp only [levPos]
    omega
  · intro _ _; rfl

lemma liftVec_levPos (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' y (levPos k 1 r' j) = y j := by
  have := j.isLt
  unfold liftVec levPos
  rw [dif_pos (by simp only []; omega)]
  congr 1

lemma liftVec_out (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (hp : ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)) : liftVec k 1 r' y p = 0 := by
  unfold liftVec
  rw [dif_neg hp]

lemma Hpk_levPos (k r' : ℕ) (i j : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') (levPos k 1 r' i) (levPos k 1 r' j) = Hpk k r' i j := by
  have e1 : (levPos k 1 r' i = levPos k 1 r' j) ↔ i.val = j.val := by
    simp only [levPos, Fin.ext_iff]; omega
  have e2 : (i = j) ↔ i.val = j.val := Fin.ext_iff
  have hi : (levPos k 1 r' i).val = i.val + 1 := rfl
  have hj : (levPos k 1 r' j).val = j.val + 1 := rfl
  unfold Hpk
  simp only [e1, e2]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma herm_lift (k r' : ℕ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' y) (liftVec k 1 r' y') = herm (Hpk k r') y y' := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  rw [sum_lift]
  · apply Finset.sum_congr rfl; intro i _
    rw [liftVec_levPos, sum_lift]
    · congr 1
      apply Finset.sum_congr rfl; intro j _
      rw [liftVec_levPos, Hpk_levPos]
    · intro p hp; rw [liftVec_out k r' y p hp, mul_zero]
  · intro p hp; rw [liftVec_out k r' y' p hp, star_zero, zero_mul]

lemma hb_rel (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' y s + star (hb k r' y s) + herm (Hpk k r') y y = 0 := by
  have h := herm_symm _ (Hpk_herm k r') y y
  have him : (herm (Hpk k r') y y).im = 0 := by
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  apply Complex.ext
  · simp [hb]
  · simp [hb, him]

theorem heisAct : HeisAct := by
  intro k r' v u b
  ext i
  simp only [heisG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  have h1 : ∀ (w φ : Fin (2 * (1 + r') + k + 1) → ℂ), (Matrix.vecMulVec w φ *ᵥ u) i = (∑ j, φ j * u j) * w i := by
    intro w φ
    simp only [mulVec, dotProduct, vecMulVec_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h1, h1, herm_sum, herm_sum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

lemma heisG_apply (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) (i j : Fin (2 * (1 + r') + k + 1)) :
    heisG k r' v b i j = (if i = j then 1 else 0) - e0 k r' i * herm (Hpk k (1 + r')) (bvec j) v +
      (v i + b * e0 k r' i) * (if j.val = 2 * (1 + r') + k then 1 else 0) := by
  simp only [heisG, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, hermitian_first_basis_right,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, lastI, Fin.ext_iff]
  congr 2
  simp only [eq_comm]

theorem heisMem : HeisMem := by
  intro k r' x
  obtain ⟨y, s⟩ := x
  refine ⟨?_, ?_, ?_⟩
  · apply mem_UH_of_herm
    intro u w
    simp only [heis0]
    rw [heisAct, heisAct]
    apply heis_isom _ (Hpk_herm k (1 + r'))
    · rw [hermitian_first_basis_right, goodRowsProjector_apply_eq_sum]; simp [lastI]
    · rw [hermitian_first_basis_right, liftVec_last]
    · rw [herm_lift]; exact hb_rel k r' y s
  · intro a i hai
    have ha := a.isLt
    simp only [heis0]
    have hv : (eI k (1 + r') a).val = a.val := rfl
    have hz : (if (eI k (1 + r') a).val = 2 * (1 + r') + k then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    rw [heisG_apply, hz, mul_zero, add_zero, goodRowsProjector_apply_eq_sum]
    by_cases hi : i.val = 0
    · have : bvec (eI k (1 + r') a) = e0 k r' := by
        unfold e0; congr 1; apply Fin.ext; simp only [eI, a0]; omega
      rw [this, hermitian_form_base_vector_left, liftVec_last]; simp
    · rw [if_neg hi]; simp
  · intro i j h1 h2 h3
    simp only [heis0]
    have hz : (if j.val = 2 * (1 + r') + k then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    have hz2 : (if i.val = 0 then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    rw [heisG_apply, hz, mul_zero, add_zero, goodRowsProjector_apply_eq_sum, hz2]; simp

end Formalism.FourierDecayAlt.P.B2x4

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem weyl_haar_from_compact : Formalism.FourierDecayAlt.B2.HaarWFromCompact := by
  intro h1 h2 h3 k r z hz hT
  exact h1 k r _ (h2 k r z) (h3 k r z hz hT)

theorem conjugation_invariance_of_parts : Formalism.FourierDecayAlt.B2.AssembleConjInv := by
  intro hCC hN hW hK hU
  have raw : ConjInvRaw := by
    intro k r z μN hz hT hμ h hh
    exact hCC k r (Nset k r) (UWset k r z) μN (hN k r) (hW k r z) (hK k r z hz hT)
      (fun a ha u hu => (hU k r z hz a ha u hu).1) hμ h hh
  refine ⟨raw, ?_⟩
  intro k r Wp Wq _ _ _ _ D h₀ hh
  rcases hh with hh | hh
  · exact raw k r D.z D.μN D.z_mem D.T_pos D.haarN h₀ hh
  · exact raw k r D.z' D.μN D.z'_mem D.T'_pos D.haarN h₀ hh

theorem B2x4.conjInv_of (hN : ClosedN) (hW : ClosedW) (hK : CompactW) : ConjInvRaw ∧ ConjInvAll :=
  conjugation_invariance_of_parts compact_subgroup_conjugation hN hW hK uWNormal

theorem b2_conjInvRaw_proof : Formalism.FourierDecayAlt.B2.ConjInvRaw :=
  (B2x4.conjInv_of unipotent_radical_closed weyl_subgroup_closed weyl_subgroup_compact).1

theorem conjugation_invariance_every_setting : Formalism.FourierDecayAlt.B2.ConjInvAll :=
  (B2x4.conjInv_of unipotent_radical_closed weyl_subgroup_closed weyl_subgroup_compact).2

theorem heisenberg_action_formula : Formalism.FourierDecayAlt.B2.HeisAct := B2x4.heisAct

theorem heisenberg_mem_unipotent : Formalism.FourierDecayAlt.B2.HeisMem := B2x4.heisMem

end Formalism.FourierDecayAlt.P
