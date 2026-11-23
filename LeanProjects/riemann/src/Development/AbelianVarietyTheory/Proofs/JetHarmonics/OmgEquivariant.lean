import Mathlib
import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.StatementU
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MulVecBvecApply

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmgEquiv

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}

lemma herm_UH {h : Mx k r} (hh : h ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ v) (h *ᵥ w) = herm (Hpk k r) v w := by
  have e : hᴴ * Hpk k r * h = Hpk k r := hh
  unfold Formalism.QuantumDeterminants.herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [e]

lemma fix_fvec {h : Mx k r} (hh : h ∈ UWset k r z) (a : Fin (r + 1)) :
    h *ᵥ fvec k r z a = fvec k r z a := by
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hh
  unfold Formalism.QuantumDeterminants.fvec
  split_ifs with ha
  · exact (hh.2.1 ⟨a.val, ha⟩).1
  · exact hh.2.2

private lemma hpk_apply_of_outer {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if i.val + l.val = 2 * r + k then 1 else 0 := by
  have := i.isLt
  have := l.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

private lemma hpk_apply_of_middle {i : Fin (2 * r + k + 1)} (hi : r ≤ i.val ∧ i.val ≤ r + k) (l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if i = l then (if i.val = r + k then -1 else 1) else 0 := by
  have := i.isLt
  have := l.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

private lemma hpk_mul_hpk : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have := i.isLt
  have := j.isLt
  by_cases hout : i.val < r ∨ r + k < i.val
  · have hp : 2 * r + k - i.val < 2 * r + k + 1 := by omega
    have hp' : 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val := by omega
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, hp⟩]
    · rw [hpk_apply_of_outer hout, hpk_apply_of_outer (i := ⟨2 * r + k - i.val, hp⟩) hp']
      simp only [Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega) | norm_num
    · intro l _ hl
      rw [hpk_apply_of_outer hout, if_neg, zero_mul]
      intro e
      exact hl (Fin.ext (show l.val = 2 * r + k - i.val by omega))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hmid : r ≤ i.val ∧ i.val ≤ r + k := by omega
    rw [Finset.sum_eq_single i]
    · rw [hpk_apply_of_middle hmid, hpk_apply_of_middle hmid]
      by_cases hij : i = j
      · subst hij
        by_cases hv : i.val = r + k <;> simp [hv]
      · simp [hij]
    · intro l _ hl
      rw [hpk_apply_of_middle hmid, if_neg (Ne.symm hl), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

private lemma hpk_conjTranspose_hpk_mul_eq_one_of_mem_UH {g : Mx k r} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have e : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [e, hpk_mul_hpk]

private lemma inv_eq_hpk_mul_conjTranspose_mul_hpk {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (hpk_conjTranspose_hpk_mul_eq_one_of_mem_UH hg)

private lemma inv_mul_cancel_of_mem_UH {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ * g = 1 := by
  rw [inv_eq_hpk_mul_conjTranspose_mul_hpk hg]
  exact hpk_conjTranspose_hpk_mul_eq_one_of_mem_UH hg

private lemma mul_inv_cancel_of_mem_UH {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv (h := Matrix.isUnit_det_of_left_inverse (hpk_conjTranspose_hpk_mul_eq_one_of_mem_UH hg))

private lemma inv_mem_UH_jet_harmonics {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have e : gᴴ * Hpk k r * g = Hpk k r := hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [e]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [mul_inv_cancel_of_mem_UH hg, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

private lemma inv_mulVec_eq_of_mulVec_eq_of_mem_UH {g : Mx k r} (hg : g ∈ UH (Hpk k r)) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : g *ᵥ v = v) : g⁻¹ *ᵥ v = v := by
  calc g⁻¹ *ᵥ v = g⁻¹ *ᵥ (g *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, inv_mul_cancel_of_mem_UH hg, Matrix.one_mulVec]

lemma inv_mem {h : Mx k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hh ⊢
  obtain ⟨hU, hb, hz⟩ := hh
  exact ⟨inv_mem_UH_jet_harmonics hU, fun a => ⟨inv_mulVec_eq_of_mulVec_eq_of_mem_UH hU (hb a).1, inv_mulVec_eq_of_mulVec_eq_of_mem_UH hU (hb a).2⟩, inv_mulVec_eq_of_mulVec_eq_of_mem_UH hU hz⟩

private lemma herm_hpk_bvec_eq_of_outer (v : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : p.val < r ∨ r + k < p.val) (hpq : p.val + q.val = 2 * r + k) :
    herm (Hpk k r) v (bvec p) = v q := by
  have hs : star (bvec p : Fin (2 * r + k + 1) → ℂ) = bvec p := by
    ext j
    by_cases hj : j = p
    · subst hj
      simp [Formalism.QuantumDeterminants.bvec]
    · simp [Formalism.QuantumDeterminants.bvec, hj]
  unfold Formalism.QuantumDeterminants.herm
  rw [hs]
  unfold Formalism.QuantumDeterminants.bvec
  rw [single_dotProduct, one_mul]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single q]
  · rw [hpk_apply_of_outer hp, if_pos hpq, one_mul]
  · intro l _ hl
    rw [hpk_apply_of_outer hp, if_neg, zero_mul]
    intro e
    exact hl (Fin.ext (by omega))
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma block {h : Mx k r} (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1))
    (hij : ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k))) :
    h i j = if i = j then 1 else 0 := by
  have hh' := hh
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hh'
  obtain ⟨hU, hb, -⟩ := hh'
  have hcol : ∀ i j : Fin (2 * r + k + 1), (h *ᵥ bvec j) i = h i j := by
    intro i j
    simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hbv : ∀ i j : Fin (2 * r + k + 1), bvec j i = if i = j then (1 : ℂ) else 0 := by
    intro i j
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]
  have hfix : ∀ p : Fin (2 * r + k + 1), (p.val < r ∨ r + k < p.val) → h *ᵥ bvec p = bvec p := by
    intro p hp
    have := p.isLt
    rcases hp with hp | hp
    · have hq := (hb ⟨p.val, hp⟩).1
      rwa [show eI k r ⟨p.val, hp⟩ = p from Fin.ext rfl] at hq
    · have hp' : 2 * r + k - p.val < r := by omega
      have hq := (hb ⟨2 * r + k - p.val, hp'⟩).2
      rwa [show esI k r ⟨2 * r + k - p.val, hp'⟩ = p from
        Fin.ext (show 2 * r + k - (2 * r + k - p.val) = p.val by omega)] at hq
  have := i.isLt
  have := j.isLt
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [← hcol, hfix j hj, hbv]
  · have hi : i.val < r ∨ r + k < i.val := by
      by_contra hc
      exact hij ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    have hlt : 2 * r + k - i.val < 2 * r + k + 1 := by omega
    have hp : 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val := by omega
    have hpi : 2 * r + k - i.val + i.val = 2 * r + k := by omega
    calc h i j = (h *ᵥ bvec j) i := (hcol i j).symm
      _ = herm (Hpk k r) (h *ᵥ bvec j) (bvec ⟨2 * r + k - i.val, hlt⟩) :=
          (herm_hpk_bvec_eq_of_outer _ ⟨2 * r + k - i.val, hlt⟩ i hp hpi).symm
      _ = herm (Hpk k r) (h *ᵥ bvec j) (h *ᵥ bvec ⟨2 * r + k - i.val, hlt⟩) := by
          rw [hfix ⟨2 * r + k - i.val, hlt⟩ hp]
      _ = herm (Hpk k r) (bvec j) (bvec ⟨2 * r + k - i.val, hlt⟩) :=
          GlobalTheory.WigSh.OmgEquiv.herm_UH hU _ _
      _ = bvec j i := herm_hpk_bvec_eq_of_outer _ ⟨2 * r + k - i.val, hlt⟩ i hp hpi
      _ = if i = j then 1 else 0 := hbv i j

lemma mul_inv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := mul_inv_cancel_of_mem_UH hg

lemma inv_eq {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := inv_eq_hpk_mul_conjTranspose_mul_hpk hg

lemma mul_mem {a b : Mx k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ea : aᴴ * Hpk k r * a = Hpk k r := ha
  have eb : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ea, eb]

lemma wb_comm {h : Mx k r} (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then (h *ᵥ v) i else 0) =
      h *ᵥ (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  split_ifs with hi
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rfl
    · have hne : i ≠ j := fun e => hj (by subst e; exact hi)
      simp [GlobalTheory.WigSh.OmgEquiv.block hh i j (fun hc => hj hc.2), hne]
  · refine (Finset.sum_eq_zero fun j _ => ?_).symm
    split_ifs with hj
    · have hne : i ≠ j := fun e => hi (by subst e; exact hj)
      simp [GlobalTheory.WigSh.OmgEquiv.block hh i j (fun hc => hi hc.1), hne]
    · rw [mul_zero]

lemma prW_comm {h : Mx k r} (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.D.prW k r z (h *ᵥ v) = h *ᵥ Formalism.FourierDecayAlt.D.prW k r z v := by
  have hh' := hh
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hh'
  obtain ⟨hU, -, hz⟩ := hh'
  have key : ∀ w : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) (h *ᵥ w) z = herm (Hpk k r) w z := by
    intro w
    calc herm (Hpk k r) (h *ᵥ w) z = herm (Hpk k r) (h *ᵥ w) (h *ᵥ z) := by rw [hz]
      _ = herm (Hpk k r) w z := GlobalTheory.WigSh.OmgEquiv.herm_UH hU w z
  simp only [Formalism.FourierDecayAlt.D.prW]
  rw [GlobalTheory.WigSh.OmgEquiv.wb_comm hh v, Matrix.mulVec_sub, Matrix.mulVec_smul, hz, key]

lemma Zhat_eq {g h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') :
    Zhat k r z z' (h⁻¹ * g * h') = Zhat k r z z' g := by
  have hi := GlobalTheory.WigSh.OmgEquiv.inv_mem hh
  have hiU : h⁻¹ ∈ UH (Hpk k r) := by
    have hi' := hi
    simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hi'
    exact hi'.1
  ext a b
  simp only [Formalism.QuantumDeterminants.Zhat]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, GlobalTheory.WigSh.OmgEquiv.fix_fvec hh' b]
  calc herm (Hpk k r) (h⁻¹ *ᵥ (g *ᵥ fvec k r z' b)) (fvec k r z a)
      = herm (Hpk k r) (h⁻¹ *ᵥ (g *ᵥ fvec k r z' b)) (h⁻¹ *ᵥ fvec k r z a) := by
        rw [GlobalTheory.WigSh.OmgEquiv.fix_fvec hi a]
    _ = herm (Hpk k r) (g *ᵥ fvec k r z' b) (fvec k r z a) := GlobalTheory.WigSh.OmgEquiv.herm_UH hiU _ _

end GlobalTheory.WigSh.OmgEquiv

namespace GlobalTheory.WigSh

open OmgEquiv

theorem omg_equivariant : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g h h' : Mx k r), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → g ∈ UH (Hpk k r) → h ∈ UWset k r z → h' ∈ UWset k r z' → GlobalTheory.WigSh.omg k r z z' (h⁻¹ * g * h') = h'⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' g := by
  intro k r z z' g h h' _ _ _ _ hg hh hh'
  have hUW : ∀ {w : Fin (2 * r + k + 1) → ℂ} {m : Mx k r}, m ∈ UWset k r w → m ∈ UH (Hpk k r) := by
    intro w m hm
    simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hm
    exact hm.1
  have hG : h⁻¹ * g * h' ∈ UH (Hpk k r) :=
    GlobalTheory.WigSh.OmgEquiv.mul_mem
      (GlobalTheory.WigSh.OmgEquiv.mul_mem (hUW (GlobalTheory.WigSh.OmgEquiv.inv_mem hh)) hg) (hUW hh')
  unfold GlobalTheory.WigSh.omg
  rw [GlobalTheory.WigSh.OmgEquiv.Zhat_eq hh hh', ← GlobalTheory.WigSh.OmgEquiv.inv_eq hG, ← GlobalTheory.WigSh.OmgEquiv.inv_eq hg,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  set S := ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a with hSdef
  have hfixS : ∀ m : Mx k r, m ∈ UWset k r z → m *ᵥ S = S := by
    intro m hm
    rw [hSdef, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [Matrix.mulVec_smul, GlobalTheory.WigSh.OmgEquiv.fix_fvec hm a]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hfixS _ (GlobalTheory.WigSh.OmgEquiv.inv_mem (GlobalTheory.WigSh.OmgEquiv.inv_mem hh))]
  exact GlobalTheory.WigSh.OmgEquiv.prW_comm (GlobalTheory.WigSh.OmgEquiv.inv_mem hh') _

end GlobalTheory.WigSh
