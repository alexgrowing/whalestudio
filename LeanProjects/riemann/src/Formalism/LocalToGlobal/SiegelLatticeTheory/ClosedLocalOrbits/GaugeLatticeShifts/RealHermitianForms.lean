import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates

noncomputable section

open Matrix Finset
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.RealHermitianForms

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

section Form

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_add_l (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  unfold hJ; rw [star_add, add_dotProduct]

theorem hJ_add_r (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ; rw [mulVec_add, dotProduct_add]

theorem hJ_sub_l (x x' y : Fin n → ℂ) : hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
  unfold hJ; rw [star_sub, sub_dotProduct]

theorem hJ_sub_r (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  unfold hJ; rw [mulVec_sub, dotProduct_sub]

theorem hJ_smul_l (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = conj c * hJ ε x y := by
  unfold hJ; rw [star_smul, smul_dotProduct, smul_eq_mul]; rfl

theorem hJ_smul_r (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  unfold hJ; rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_zero_l (y : Fin n → ℂ) : hJ ε 0 y = 0 := by
  unfold hJ; simp

theorem hJ_conj_sym (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) := by
  unfold hJ
  simp only [Formalism.REAL.Jm, mulVec_diagonal, dotProduct, Pi.star_apply, map_sum, map_mul, RCLike.star_def,
    Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

theorem hJ_sum_r {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, c i * hJ ε x (y i) := by
  unfold hJ
  simp only [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem hJ_sum_l {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε (∑ i ∈ s, c i • y i) x = ∑ i ∈ s, conj (c i) * hJ ε (y i) x := by
  rw [hJ_conj_sym, hJ_sum_r, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← hJ_conj_sym]

theorem hJ_uj (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) : hJ ε (uMat g *ᵥ x) (uMat g *ᵥ y) = hJ ε x y := by
  have hg : Formalism.REAL.inUJ ε (uMat g) := g.2
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold Formalism.REAL.inUJ at hg
  rw [hg]

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  simp [uMat]

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem hJ_inv_r (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat g⁻¹ *ᵥ y) = hJ ε (uMat g *ᵥ x) y := by
  rw [← hJ_uj ε g x (uMat g⁻¹ *ᵥ y), mulVec_mulVec, uMat_mul_inv, one_mulVec]

theorem exists_of_hJ (E : Matrix (Fin n) (Fin n) ℂ) (hE : ∀ x y, hJ ε (E *ᵥ x) (E *ᵥ y) = hJ ε x y) :
    ∃ s : Formalism.REAL.UJ ε, uMat s = E := by
  have key : ∀ x y : Fin n → ℂ,
      star x ⬝ᵥ ((Eᴴ * Formalism.REAL.Jm ε * E) *ᵥ y) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
    intro x y
    have h := hE x y
    unfold hJ at h
    rw [← h, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h1 : Formalism.REAL.inUJ ε E := by
    unfold Formalism.REAL.inUJ
    ext i j
    have h := key (Pi.single i 1) (Pi.single j 1)
    simpa [dotProduct, mulVec, Pi.single_apply] using h
  have hL : (Formalism.REAL.Jm ε * Eᴴ * Formalism.REAL.Jm ε) * E = 1 := by
    have : (Formalism.REAL.Jm ε * Eᴴ * Formalism.REAL.Jm ε) * E = Formalism.REAL.Jm ε * (Eᴴ * Formalism.REAL.Jm ε * E) := by
      simp only [Matrix.mul_assoc]
    rw [this, h1, Formalism.REAL.Jm_mul_self]
  exact ⟨⟨Matrix.nonsingInvUnit E (Matrix.isUnit_det_of_left_inverse hL), h1⟩, rfl⟩

end Form

section Eich

variable {n : ℕ} (ε : Fin n → Bool)

def eichL (u w : Fin n → ℂ) (κ : ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun x := x + hJ ε w x • u - hJ ε u x • w + (κ * hJ ε u x) • u
  map_add' x y := by
    simp only [hJ_add_r, add_smul, mul_add]
    abel
  map_smul' c x := by
    simp only [hJ_smul_r, RingHom.id_apply]
    module

theorem eichL_apply (u w : Fin n → ℂ) (κ : ℂ) (x : Fin n → ℂ) :
    eichL ε u w κ x = x + hJ ε w x • u - hJ ε u x • w + (κ * hJ ε u x) • u := rfl

theorem eich_hJ (u w : Fin n → ℂ) (κ : ℂ) (huu : hJ ε u u = 0) (huw : hJ ε u w = 0)
    (hκ : κ + conj κ = -hJ ε w w) (x y : Fin n → ℂ) :
    hJ ε (eichL ε u w κ x) (eichL ε u w κ y) = hJ ε x y := by
  have hwu : hJ ε w u = 0 := by rw [hJ_conj_sym, huw, map_zero]
  have hxu : hJ ε x u = conj (hJ ε u x) := hJ_conj_sym ε x u
  have hxw : hJ ε x w = conj (hJ ε w x) := hJ_conj_sym ε x w
  simp only [eichL_apply, hJ_add_l, hJ_sub_l, hJ_smul_l, hJ_add_r, hJ_sub_r, hJ_smul_r, huu, huw, hwu, hxu, hxw,
    map_mul]
  linear_combination (conj (hJ ε u x) * hJ ε u y) * hκ

theorem exists_eich (u w : Fin n → ℂ) (huu : hJ ε u u = 0) (huw : hJ ε u w = 0) :
    ∃ s : Formalism.REAL.UJ ε, ∀ x, uMat s *ᵥ x = eichL ε u w (-(hJ ε w w) / 2) x := by
  have hκ : -(hJ ε w w) / 2 + conj (-(hJ ε w w) / 2) = -hJ ε w w := by
    have hr : conj (hJ ε w w) = hJ ε w w := (hJ_conj_sym ε w w).symm
    rw [map_div₀, map_neg, hr, map_ofNat]
    ring
  obtain ⟨s, hs⟩ := exists_of_hJ ε (LinearMap.toMatrix' (eichL ε u w (-(hJ ε w w) / 2))) (fun x y => by
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    exact eich_hJ ε u w _ huu huw hκ x y)
  exact ⟨s, fun x => by rw [hs, LinearMap.toMatrix'_mulVec]⟩

theorem exists_dual {m : ℕ} (f : Fin m → Fin n → ℂ) (hf : LinearIndependent ℂ f) (y : Fin m → ℂ) :
    ∃ w : Fin n → ℂ, ∀ b, hJ ε w (f b) = y b := by
  let M : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun b => Formalism.REAL.Jm ε *ᵥ f b
  have hJinj : LinearMap.ker (Matrix.mulVecLin (Formalism.REAL.Jm ε)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h2 : Formalism.REAL.Jm ε *ᵥ (Formalism.REAL.Jm ε *ᵥ x) = x := by
      rw [mulVec_mulVec, Formalism.REAL.Jm_mul_self, one_mulVec]
    rw [← h2]
    rw [Matrix.mulVecLin_apply] at hx
    rw [hx, mulVec_zero]
  have hrows : LinearIndependent ℂ M.row := by
    have hrow : M.row = ⇑(Matrix.mulVecLin (Formalism.REAL.Jm ε)) ∘ f := by
      ext b i
      rfl
    rw [hrow]
    exact hf.map' _ hJinj
  have hrank : Module.finrank ℂ (LinearMap.range M.mulVecLin) = m := by
    have h := Matrix.rank_eq_finrank_span_row M
    rw [finrank_span_eq_card hrows, Fintype.card_fin] at h
    exact h
  have htop : LinearMap.range M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hrank, Module.finrank_fin_fun])
  obtain ⟨v, hv⟩ : ∃ v, M.mulVecLin v = y := by
    rw [← LinearMap.mem_range, htop]; trivial
  refine ⟨star v, fun b => ?_⟩
  have hb := congrFun hv b
  rw [Matrix.mulVecLin_apply] at hb
  unfold hJ
  rw [star_star, dotProduct_comm]
  exact hb

end Eich

section Frame

variable {n r : ℕ} (ε : Fin n → Bool)

theorem fam_last (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : fam e z (Fin.last r) = z := by
  unfold fam; exact Fin.snoc_last (α := fun _ => Fin n → ℂ) _ _

theorem fam_cs (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (a : Fin r) : fam e z (Fin.castSucc a) = e a := by
  unfold fam; exact Fin.snoc_castSucc (α := fun _ => Fin n → ℂ) _ _ _

theorem hJ_e_fam (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (hee : ∀ a b, hJ ε (e a) (e b) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (c : Fin r) (b : Fin (r + 1)) : hJ ε (e c) (fam e z b) = 0 := by
  induction b using Fin.lastCases with
  | last => rw [fam_last]; exact hez c
  | cast a => rw [fam_cs]; exact hee c a

theorem realize_rows (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (hli : LinearIndependent ℂ (fam e z))
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hez : ∀ a, hJ ε (e a) z = 0)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hX : ∀ i j : Fin (r + 1), j ≤ i → X i j = 0) :
    ∀ m, m ≤ r → ∃ s : Formalism.REAL.UJ ε, ∀ b, uMat s *ᵥ fam e z b =
      fam e z b + ∑ a, (if a.1 < m then X a b else 0) • fam e z a := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨1, fun b => ?_⟩
    simp [uMat]
  | succ m ih =>
    intro hm
    obtain ⟨s, hs⟩ := ih (by omega)
    have hmr : m < r := by omega
    let c : Fin r := ⟨m, hmr⟩
    let row : Fin (r + 1) := Fin.castSucc c
    have hrowv : row.1 = m := rfl
    obtain ⟨w, hw⟩ := exists_dual ε (fam e z) hli (fun b => X row b)
    have huu : hJ ε (e c) (e c) = 0 := hee c c
    have huw : hJ ε (e c) w = 0 := by
      rw [hJ_conj_sym, ← fam_cs e z c, hw]
      show conj (X row row) = 0
      rw [hX row row le_rfl, map_zero]
    obtain ⟨t, ht⟩ := exists_eich ε (e c) w huu huw
    refine ⟨t * s, fun b => ?_⟩
    rw [uMat_mul, ← mulVec_mulVec, hs b, ht, eichL_apply]
    have hv0 : hJ ε (e c) (fam e z b + ∑ a, (if a.1 < m then X a b else 0) • fam e z a) = 0 := by
      rw [hJ_add_r, hJ_sum_r, hJ_e_fam ε e z hee hez]
      simp [hJ_e_fam ε e z hee hez]
    have hv1 : hJ ε w (fam e z b + ∑ a, (if a.1 < m then X a b else 0) • fam e z a) = X row b := by
      rw [hJ_add_r, hJ_sum_r, hw]
      have : ∀ a : Fin (r + 1), (if a.1 < m then X a b else 0) * hJ ε w (fam e z a) = 0 := by
        intro a
        split_ifs with ha
        · have hle : a ≤ row := by
            rw [Fin.le_def, hrowv]; exact ha.le
          rw [hw, hX row a hle, mul_zero]
        · rw [zero_mul]
      simp only [this, Finset.sum_const_zero, add_zero]
    rw [hv0, hv1]
    have hsplit : ∀ a : Fin (r + 1), (if a.1 < m + 1 then X a b else 0) =
        (if a.1 < m then X a b else 0) + (if a = row then X a b else 0) := by
      intro a
      by_cases h1 : a.1 < m
      · have hne : a ≠ row := by
          intro h; rw [h, hrowv] at h1; exact lt_irrefl _ h1
        rw [if_pos (by omega), if_pos h1, if_neg hne, add_zero]
      · by_cases h2 : a.1 = m
        · have heq : a = row := Fin.ext (by rw [h2, hrowv])
          rw [if_pos (by omega), if_neg h1, if_pos heq, zero_add]
        · have hne : a ≠ row := by
            intro h; rw [h, hrowv] at h2; exact h2 rfl
          rw [if_neg (by omega), if_neg h1, if_neg hne, add_zero]
    have hsum : ∑ a, (if a.1 < m + 1 then X a b else 0) • fam e z a =
        ∑ a, (if a.1 < m then X a b else 0) • fam e z a + X row b • e c := by
      rw [Finset.sum_congr rfl (fun a _ => by rw [hsplit a, add_smul]), Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single row (fun a _ ha => by rw [if_neg ha, zero_smul]) (fun h => absurd (Finset.mem_univ _) h),
        if_pos rfl, fam_cs]
    rw [hsum, mul_zero, zero_smul, zero_smul, sub_zero, add_zero]
    abel

theorem realize (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (hli : LinearIndependent ℂ (fam e z))
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hez : ∀ a, hJ ε (e a) z = 0)
    (P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hP1 : ∀ i j : Fin (r + 1), j < i → P i j = 0)
    (hP2 : ∀ a, P a a = 1) :
    ∃ s : Formalism.REAL.UJ ε, ∀ b, uMat s *ᵥ fam e z b = ∑ a, P a b • fam e z a := by
  have hX : ∀ i j : Fin (r + 1), j ≤ i → (P - 1) i j = 0 := by
    intro i j hij
    rcases lt_or_eq_of_le hij with h | h
    · rw [Matrix.sub_apply, hP1 i j h, Matrix.one_apply_ne (ne_of_gt h), sub_self]
    · rw [h, Matrix.sub_apply, hP2, Matrix.one_apply_eq, sub_self]
  obtain ⟨s, hs⟩ := realize_rows ε e z hli hee hez (P - 1) hX r le_rfl
  refine ⟨s, fun b => ?_⟩
  rw [hs b]
  have h1 : ∀ a : Fin (r + 1), (if a.1 < r then (P - 1) a b else 0) = P a b - (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) a b := by
    intro a
    split_ifs with ha
    · rfl
    · have hal : a = Fin.last r := Fin.ext (by have := a.2; simp only [Fin.val_last]; omega)
      rw [← Matrix.sub_apply, hX a b (hal ▸ Fin.le_last b)]
  rw [Finset.sum_congr rfl (fun a _ => by rw [h1 a, sub_smul]), Finset.sum_sub_distrib]
  have h2 : ∑ a, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) a b • fam e z a = fam e z b := by
    rw [Finset.sum_eq_single b (fun a _ ha => by rw [Matrix.one_apply_ne ha, zero_smul])
      (fun h => absurd (Finset.mem_univ _) h), Matrix.one_apply_eq, one_smul]
  rw [h2]
  abel

end Frame

end Formalism.L2.SG.RealObj.InfCut.RealHermitianForms
