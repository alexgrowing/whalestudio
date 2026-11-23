import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.IsUnitDetOfMemGV

open Matrix

noncomputable section

namespace PI.StabPairsW

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

variable {k r : ℕ}

theorem mul_of_col (z : Fin (2 * r + k + 1) → ℂ) (s : B.Mat k r) (x : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (h : ∀ b, s *ᵥ fvec k r z b = ∑ c, x c b • fvec k r z c) : s * Ff k r z = Ff k r z * x := by
  ext i b
  have hb := congrFun (h b) i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hb
  simp only [Matrix.mul_apply, Ff, Matrix.of_apply, hb]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

def coefOf (b : Fin (r + 1)) (y : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) : ℂ :=
  if a = b then 1 else if h : a.val < b.val then y (eI k r ⟨a.val, by omega⟩) else 0

theorem expand_of_tail (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (b : Fin (r + 1))
    (y : Fin (2 * r + k + 1) → ℂ) (hy : ∀ i : Fin (2 * r + k + 1), b.val ≤ i.val → y i = fvec k r z b i) :
    y = ∑ a, coefOf (k := k) b y a • fvec k r z a := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  simp only [coefOf, if_pos rfl, one_mul]
  have hrest : ∀ a ∈ Finset.univ.erase b, (if a = b then (1 : ℂ) else
      if h : a.val < b.val then y (eI k r ⟨a.val, by omega⟩) else 0) * fvec k r z a i =
      if h : a.val < b.val ∧ i.val = a.val then y i else 0 := by
    intro a ha
    have hab : a ≠ b := Finset.ne_of_mem_erase ha
    rw [if_neg hab]
    by_cases hlt : a.val < b.val
    · rw [dif_pos hlt]
      have har : a.val < r := by omega
      have hf : fvec k r z a = bvec (eI k r ⟨a.val, har⟩) := by simp [fvec, har]
      rw [hf]
      by_cases hia : i.val = a.val
      · rw [dif_pos ⟨hlt, hia⟩]
        have hi : i = eI k r ⟨a.val, har⟩ := Fin.ext (by simp [eI, hia])
        subst hi
        simp [bvec]
      · rw [dif_neg (fun h => hia h.2)]
        have hi : i ≠ eI k r ⟨a.val, har⟩ := fun h => hia (by rw [h]; simp [eI])
        simp [bvec, Pi.single_apply, hi]
    · rw [dif_neg hlt, dif_neg (fun h => hlt h.1), zero_mul]
  rw [Finset.sum_congr rfl hrest]
  by_cases hib : b.val ≤ i.val
  · rw [hy i hib, Finset.sum_eq_zero]
    · simp
    · intro a _
      rw [dif_neg]
      omega
  · have hir : i.val < r := by omega
    have hfb : fvec k r z b i = 0 := by
      unfold fvec
      split_ifs with hbr
      · have hne : i ≠ eI k r ⟨b.val, hbr⟩ := fun h => by
          have := congrArg Fin.val h
          simp [eI] at this
          omega
        simp [bvec, Pi.single_apply, hne]
      · exact hz i (Or.inl hir)
    rw [hfb, mul_zero, zero_add]
    rw [Finset.sum_eq_single ⟨i.val, by omega⟩]
    · rw [dif_pos ⟨by simp; omega, rfl⟩]
    · intro a _ ha
      rw [dif_neg]
      rintro ⟨-, h2⟩
      exact ha (Fin.ext h2.symm)
    · intro ha
      exfalso
      apply ha
      rw [Finset.mem_erase]
      refine ⟨fun h => ?_, Finset.mem_univ _⟩
      have := congrArg Fin.val h
      simp at this
      omega

theorem coefOf_UT (y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    (Matrix.of fun a b => coefOf (k := k) b (y b) a) ∈ UTset (r + 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · simp only [Matrix.of_apply, coefOf, if_neg hab.ne']
    rw [dif_neg (fun h => lt_asymm h (Fin.lt_def.1 hab))]
  · simp [coefOf]

theorem Sset_frame (z : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z) (s : B.Mat k r) (hs : s ∈ Sset k r z) :
    s ∈ B.GV k r ∧ s * Ff k r z = Ff k r z * uMap k r z s ∧ uMap k r z s ∈ UTset (r + 1) := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hGV : h * m ∈ B.GV k r := by
    show (h * m)ᴴ * Hpk k r * (h * m) = Hpk k r
    have h1 : hᴴ * Hpk k r * h = Hpk k r := hh.1
    have h2 : mᴴ * Hpk k r * m = Hpk k r := hm.1
    rw [Matrix.conjTranspose_mul]
    calc mᴴ * hᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [h1, h2]
  have htail : ∀ b : Fin (r + 1), ∀ i : Fin (2 * r + k + 1), b.val ≤ i.val →
      (m *ᵥ fvec k r z b) i = fvec k r z b i := by
    intro b i hbi
    by_cases hbr : b.val < r
    · have hf : fvec k r z b = bvec (eI k r ⟨b.val, hbr⟩) := by simp [fvec, hbr]
      rw [hf]
      have e : (m *ᵥ bvec (eI k r ⟨b.val, hbr⟩)) i = m i (eI k r ⟨b.val, hbr⟩) := by
        simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [e, hm.2.1 ⟨b.val, hbr⟩ i hbi]
      simp [bvec, Pi.single_apply]
    · have hf : fvec k r z b = z := by simp [fvec, hbr]
      rw [hf]
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · by_cases hik : i.val ≤ r + k
        · rw [hm.2.2 i i (by omega) hik (by omega), if_pos rfl, one_mul]
        · rw [hz.1 i (Or.inr (by omega)), mul_zero]
      · intro j _ hji
        by_cases hj1 : r ≤ j.val
        · by_cases hj2 : j.val ≤ r + k
          · rw [hm.2.2 i j hj1 hj2 (by omega), if_neg (Ne.symm hji), zero_mul]
          · rw [hz.1 j (Or.inr (not_le.1 hj2)), mul_zero]
        · rw [hz.1 j (Or.inl (not_le.1 hj1)), mul_zero]
      · simp
  have hmX : m * Ff k r z = Ff k r z *
      (Matrix.of fun a b => coefOf (k := k) b (m *ᵥ fvec k r z b) a) :=
    mul_of_col z m _ (fun b => expand_of_tail z hz.1 b _ (htail b))
  have hhF : h * Ff k r z = Ff k r z := by
    ext i a
    have e : h *ᵥ fvec k r z a = fvec k r z a := by
      unfold fvec
      split_ifs
      · exact (hh.2.1 _).1
      · exact hh.2.2
    have e2 := congrFun e i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Ff] using e2
  have hsF : h * m * Ff k r z = Ff k r z *
      (Matrix.of fun a b => coefOf (k := k) b (m *ᵥ fvec k r z b) a) := by
    rw [Matrix.mul_assoc, hmX, ← Matrix.mul_assoc, hhF]
  have hu := uMap_eq z hz _ _ hsF
  refine ⟨hGV, ?_, ?_⟩
  · rw [hu]
    exact hsF
  · rw [hu]
    exact coefOf_UT (fun b => m *ᵥ fvec k r z b)

theorem rho_conj (γ : B.Mat k r) (hγ : γ ∈ B.GV k r) (ρ s0 : B.Mat k r)
    (h : ρ = γ * s0 * γ⁻¹) : γ⁻¹ * ρ * γ = s0 ∧ γ * s0 = ρ * γ := by
  have hγ' : γᴴ * Hpk k r * γ = Hpk k r := hγ
  have hl : (Hpk k r * γᴴ * Hpk k r) * γ = 1 := by
    have e : Hpk k r * (γᴴ * Hpk k r * γ) = 1 := by rw [hγ', hpk_mul_self]
    simpa only [Matrix.mul_assoc] using e
  have hinv : γ⁻¹ = Hpk k r * γᴴ * Hpk k r := Matrix.inv_eq_left_inv hl
  have h1 : γ⁻¹ * γ = 1 := by rw [hinv, hl]
  subst h
  constructor
  · calc γ⁻¹ * (γ * s0 * γ⁻¹) * γ = (γ⁻¹ * γ) * s0 * (γ⁻¹ * γ) := by
          simp only [Matrix.mul_assoc]
      _ = s0 := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  · calc γ * s0 = γ * s0 * (γ⁻¹ * γ) := by rw [h1, Matrix.mul_one]
      _ = γ * s0 * γ⁻¹ * γ := by simp only [Matrix.mul_assoc]

theorem mapsStep : MapsStep := by
  intro k r z z' γ hs hp ρ hρ
  obtain ⟨⟨hρS, s', hs', hρeq⟩, -⟩ := hρ
  obtain ⟨hρG, hρF, hρU⟩ := Sset_frame z hs.2.1 ρ hρS
  obtain ⟨-, hsF, hsU⟩ := Sset_frame z' hs.2.2 s' hs'
  obtain ⟨hc1, hc2⟩ := rho_conj γ hp.1 ρ s' hρeq
  have hρH : ρᴴ * Hpk k r * ρ = Hpk k r := hρG
  refine ⟨hρU, ?_, ?_⟩
  · show uMap k r z' (γ⁻¹ * ρ * γ) ∈ UTset (r + 1)
    rw [hc1]
    exact hsU
  · show (uMap k r z ρ)ᴴ * Zhat k r z z' γ * uMap k r z' (γ⁻¹ * ρ * γ) = Zhat k r z z' γ
    rw [hc1, Zhat_eq]
    calc (uMap k r z ρ)ᴴ * ((Ff k r z)ᴴ * Hpk k r * γ * Ff k r z') * uMap k r z' s'
        = (Ff k r z * uMap k r z ρ)ᴴ * Hpk k r * γ * (Ff k r z' * uMap k r z' s') := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (ρ * Ff k r z)ᴴ * Hpk k r * (γ * s') * Ff k r z' := by
          rw [← hρF, ← hsF]
          simp only [Matrix.mul_assoc]
      _ = (Ff k r z)ᴴ * (ρᴴ * Hpk k r * ρ) * γ * Ff k r z' := by
          rw [hc2, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (Ff k r z)ᴴ * Hpk k r * γ * Ff k r z' := by rw [hρH]

theorem mul_eq_of_fix (z z' : Fin (2 * r + k + 1) → ℂ) (γ ρ : B.Mat k r)
    (hfix : ∀ v ∈ Uperp k r z z' γ, ρ *ᵥ v = v) {ι : Type*} (Q : Matrix (Fin (2 * r + k + 1)) ι ℂ)
    (hQ : ((Fm k r z z' γ)ᴴ * Hpk k r) * Q = 0) : ρ * Q = Q := by
  have hE : (Matrix.of fun i j => star (gramVec k r z z' γ i j)) = (Fm k r z z' γ)ᴴ := by
    ext a b
    simp [Fm, Matrix.conjTranspose_apply]
  have hcol : ∀ j, (fun p => Q p j) ∈ Uperp k r z z' γ := by
    intro j
    simp only [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [hE]
    funext a
    have e := congrFun (congrFun hQ a) j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using e
  ext i j
  have e := congrFun (hfix _ (hcol j)) i
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using e

theorem gramInv_of (h : GramIndependentSignature) : GramInv := by
  intro k r z z' γ hs hp
  obtain ⟨-, ⟨Q, -, hQG⟩, -, -⟩ := h k r z z' γ hs hp
  have hdet := congrArg Matrix.det hQG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg,
    Matrix.det_one] at hdet
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero, zero_mul] at hdet
  exact absurd hdet.symm (by simp)

theorem pairFormula_of (hG : GramInv) : PairFormula := by
  intro k r z z' γ hs hp ρ hρ
  obtain ⟨⟨hρS, s', hs', hρeq⟩, hfix⟩ := hρ
  obtain ⟨-, hρF, -⟩ := Sset_frame z hs.2.1 ρ hρS
  obtain ⟨-, hsF, -⟩ := Sset_frame z' hs.2.2 s' hs'
  obtain ⟨hc1, hc2⟩ := rho_conj γ hp.1 ρ s' hρeq
  have hGinv : gramM k r z z' γ * (gramM k r z z' γ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (hG k r z z' γ hs hp)
  have hρFm : ρ * Fm k r z z' γ =
      Fm k r z z' γ * Wm (uMap k r z ρ) (uMap k r z' (γ⁻¹ * ρ * γ)) := by
    rw [hc1, Fm_eq, Wm, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
    simp only [Matrix.mul_zero, add_zero, zero_add]
    congr 1
    all_goals first
      | exact hρF
      | rw [← Matrix.mul_assoc, ← hc2, Matrix.mul_assoc, hsF, Matrix.mul_assoc]
  have hQ : ((Fm k r z z' γ)ᴴ * Hpk k r) * (1 - Fm k r z z' γ * Km k r z z' γ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Km]
    have e : (Fm k r z z' γ)ᴴ * Hpk k r *
        (Fm k r z z' γ * ((gramM k r z z' γ)⁻¹ * (Fm k r z z' γ)ᴴ * Hpk k r)) =
        ((Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ) * (gramM k r z z' γ)⁻¹ *
          ((Fm k r z z' γ)ᴴ * Hpk k r) := by
      simp only [Matrix.mul_assoc]
    rw [e, ← gramM_eq, hGinv, Matrix.one_mul, sub_self]
  have hfixQ := mul_eq_of_fix z z' γ ρ hfix _ hQ
  calc ρ = ρ * (Fm k r z z' γ * Km k r z z' γ) + ρ * (1 - Fm k r z z' γ * Km k r z z' γ) := by
        rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
    _ = Fm k r z z' γ * Wm (uMap k r z ρ) (uMap k r z' (γ⁻¹ * ρ * γ)) * Km k r z z' γ +
          (1 - Fm k r z z' γ * Km k r z z' γ) := by
        rw [hfixQ, ← Matrix.mul_assoc, hρFm]
    _ = rhoOf k r z z' γ (pairMap k r z z' γ ρ).1 (pairMap k r z z' γ ρ).2 := by
        simp only [rhoOf, pairMap, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
        abel

theorem det_UT {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => hu.1 i j hij)]
  simp [hu.2]

theorem compDet : CompDet := by
  intro k r z z' γ hs hp p hpS q hqS
  obtain ⟨hp1, hp2, hpe⟩ := hpS
  obtain ⟨hq1, hq2, hqe⟩ := hqS
  have hZu : IsUnit (Zhat k r z z' γ) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_Zhat_ne z z' hs γ hp))
  have hU : ∀ {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}, u ∈ UTset (r + 1) → IsUnit u :=
    fun hu => (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_UT hu]; exact isUnit_one)
  have hUH : ∀ {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}, u ∈ UTset (r + 1) → IsUnit uᴴ :=
    fun hu => (Matrix.isUnit_iff_isUnit_det _).2
      (by rw [Matrix.det_conjTranspose, det_UT hu, star_one]; exact isUnit_one)
  constructor
  · intro h1
    have e : (p.1ᴴ * Zhat k r z z' γ) * p.2 = (p.1ᴴ * Zhat k r z z' γ) * q.2 := by
      rw [hpe, h1, hqe]
    exact Prod.ext h1 (((hUH hp1).mul hZu).mul_left_cancel e)
  · intro h2
    have e : p.1ᴴ * (Zhat k r z z' γ * p.2) = q.1ᴴ * (Zhat k r z z' γ * p.2) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hpe, h2, hqe]
    have h1 := (hZu.mul (hU hp2)).mul_right_cancel e
    exact Prod.ext (Matrix.conjTranspose_inj.1 h1) h2

end PI.StabPairsW
