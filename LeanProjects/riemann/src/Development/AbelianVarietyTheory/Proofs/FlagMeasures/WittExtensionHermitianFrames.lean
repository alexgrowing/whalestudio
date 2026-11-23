import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer

open Matrix

namespace GlobalTheory.SgAlg.WittField

variable {E : Type} [Field E] {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem form_add_left (v v' w : Fin n → E) : form σ J (v + v') w = form σ J v w + form σ J v' w := by
  simp [form, mulVec_add, dotProduct_add]

theorem form_sub_left (v v' w : Fin n → E) : form σ J (v - v') w = form σ J v w - form σ J v' w := by
  simp [form, mulVec_sub, dotProduct_sub]

theorem form_smul_left (c : E) (v w : Fin n → E) : form σ J (c • v) w = c * form σ J v w := by
  simp [form, mulVec_smul, dotProduct_smul]

theorem form_sub_right (v w w' : Fin n → E) : form σ J v (w - w') = form σ J v w - form σ J v w' := by
  simp only [form, Pi.sub_apply, map_sub]
  rw [show (fun i => σ (w i) - σ (w' i)) = (fun i => σ (w i)) - (fun i => σ (w' i)) from rfl, sub_dotProduct]

theorem form_smul_right (c : E) (v w : Fin n → E) : form σ J v (c • w) = σ c * form σ J v w := by
  simp only [form, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => σ c * σ (w i)) = σ c • (fun i => σ (w i)) from rfl, smul_dotProduct, smul_eq_mul]

theorem herm_entry (hJ : cT σ J = J) (i j : Fin n) : σ (J j i) = J i j := by
  have := congrFun (congrFun hJ i) j
  simpa [cT] using this

theorem form_conj (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (v w : Fin n → E) :
    form σ J w v = σ (form σ J v w) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show J j i = σ (J i j) from (herm_entry hJ j i).symm]
  ring

theorem form_add_right (v w w' : Fin n → E) : form σ J v (w + w') = form σ J v w + form σ J v w' := by
  simp only [form, Pi.add_apply, map_add]
  rw [show (fun i => σ (w i) + σ (w' i)) = (fun i => σ (w i)) + (fun i => σ (w' i)) from rfl, add_dotProduct]

theorem conj_mulVec (B : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    (fun i => σ ((B *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* cT σ B := by
  funext k
  simp [mulVec, vecMul, dotProduct, cT, map_sum, map_mul, mul_comm]

theorem form_mulVec (A B : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    form σ J (A *ᵥ v) (B *ᵥ w) = (fun i => σ (w i)) ⬝ᵥ ((cT σ B * J * A) *ᵥ v) := by
  unfold form
  rw [conj_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem isUn_form {g : Matrix (Fin n) (Fin n) E} (hg : IsUn σ J g) (v w : Fin n → E) :
    form σ J (g *ᵥ v) (g *ᵥ w) = form σ J v w := by
  rw [form_mulVec, hg]; rfl

theorem single_entry (M : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (fun k => σ ((Pi.single i (1 : E) : Fin n → E) k)) ⬝ᵥ (M *ᵥ (Pi.single j (1 : E) : Fin n → E)) = M i j := by
  have : (fun k => σ ((Pi.single i (1 : E) : Fin n → E) k)) = (Pi.single i (1 : E) : Fin n → E) := by
    funext k; by_cases h : k = i
    · subst h; simp
    · simp [h]
  rw [this]
  simp [mulVec, dotProduct, Pi.single_apply]

theorem isUn_of_form {g : Matrix (Fin n) (Fin n) E}
    (h : ∀ v w, form σ J (g *ᵥ v) (g *ᵥ w) = form σ J v w) : IsUn σ J g := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rw [form_mulVec] at this
  unfold form at this
  rwa [single_entry, single_entry] at this

theorem cT_mul (A B : Matrix (Fin n) (Fin n) E) : cT σ (A * B) = cT σ B * cT σ A := by
  unfold cT
  rw [Matrix.map_mul, transpose_mul]

theorem isUn_mul {g h : Matrix (Fin n) (Fin n) E} (hg : IsUn σ J g) (hh : IsUn σ J h) :
    IsUn σ J (g * h) := by
  unfold IsUn at *
  have : cT σ h * cT σ g * J * (g * h) = cT σ h * (cT σ g * J * g) * h := by
    simp only [Matrix.mul_assoc]
  rw [cT_mul, this, hg, hh]

theorem isUn_one : IsUn σ J 1 := isUn_of_form (by intro v w; simp)

def qr (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (u : Fin n → E) (l : E) : Matrix (Fin n) (Fin n) E :=
  1 - l • vecMulVec u ((fun i => σ (u i)) ᵥ* J)

theorem qr_mulVec (u : Fin n → E) (l : E) (v : Fin n → E) :
    qr σ J u l *ᵥ v = v - (l * form σ J v u) • u := by
  have h1 : ((fun i => σ (u i)) ᵥ* J) ⬝ᵥ v = form σ J v u := by
    unfold form; rw [dotProduct_mulVec]
  unfold qr
  rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, h1, op_smul_eq_smul, smul_smul]

theorem qr_form (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (u : Fin n → E) (l : E)
    (hl : l * σ l * form σ J u u = l + σ l) (v w : Fin n → E) :
    form σ J (qr σ J u l *ᵥ v) (qr σ J u l *ᵥ w) = form σ J v w := by
  rw [qr_mulVec, qr_mulVec]
  simp only [form_sub_left, form_sub_right, form_smul_left, form_smul_right, map_mul]
  rw [form_conj hσ hJ w u]
  linear_combination (form σ J v u * σ (form σ J w u)) * hl

theorem isUn_qr (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (u : Fin n → E) (l : E)
    (hl : l * σ l * form σ J u u = l + σ l) : IsUn σ J (qr σ J u l) :=
  isUn_of_form (qr_form hσ hJ u l hl)

theorem qr_fix (u : Fin n → E) (l : E) (y : Fin n → E) (hy : form σ J y u = 0) :
    qr σ J u l *ᵥ y = y := by
  rw [qr_mulVec, hy]; simp

theorem stepA (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) {a : ℕ} (y : Fin a → Fin n → E)
    (x x' : Fin n → E) (hy : ∀ i, form σ J (y i) x = form σ J (y i) x')
    (hxx : form σ J x x = form σ J x' x') (hc : form σ J x (x - x') ≠ 0) :
    ∃ g, IsUn σ J g ∧ (∀ i, g *ᵥ y i = y i) ∧ g *ᵥ x = x' := by
  set c := form σ J x (x - x') with hcdef
  have hσc : σ c ≠ 0 := by
    intro h; apply hc; rw [← hσ c, h, map_zero]
  have hN : form σ J (x - x') (x - x') = c + σ c := by
    rw [hcdef, ← form_conj hσ hJ]
    simp only [form_sub_left, form_sub_right]
    linear_combination (-1 : E) * hxx
  refine ⟨qr σ J (x - x') c⁻¹, isUn_qr hσ hJ _ _ ?_, fun i => qr_fix _ _ _ ?_, ?_⟩
  · rw [map_inv₀, hN]; field_simp; ring
  · rw [form_sub_right, hy i, sub_self]
  · rw [qr_mulVec, ← hcdef, inv_mul_cancel₀ hc, one_smul]; abel

theorem step (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (h2 : (2 : E) ≠ 0) {a : ℕ} (y : Fin a → Fin n → E)
    (x x' : Fin n → E) (hy : ∀ i, form σ J (y i) x = form σ J (y i) x')
    (hxx : form σ J x x = form σ J x' x') (u₁ u₂ : Fin n → E)
    (hu₁ : ∀ i, form σ J (y i) u₁ = 0) (hxu₁ : form σ J x u₁ = 1)
    (hu₂ : ∀ i, form σ J (y i) u₂ = 0) (hxu₂ : form σ J x' u₂ = 1) :
    ∃ g, IsUn σ J g ∧ (∀ i, g *ᵥ y i = y i) ∧ g *ᵥ x = x' := by
  by_cases hc : form σ J x (x - x') ≠ 0
  · exact stepA hσ hJ y x x' hy hxx hc
  push_neg at hc

  obtain ⟨u, hu, hxu, hx'u⟩ : ∃ u : Fin n → E, (∀ i, form σ J (y i) u = 0) ∧
      form σ J x u ≠ 0 ∧ form σ J x' u ≠ 0 := by
    by_cases h1 : form σ J x' u₁ ≠ 0
    · exact ⟨u₁, hu₁, by rw [hxu₁]; exact one_ne_zero, h1⟩
    by_cases h2' : form σ J x u₂ ≠ 0
    · exact ⟨u₂, hu₂, h2', by rw [hxu₂]; exact one_ne_zero⟩
    push_neg at h1 h2'
    refine ⟨u₁ + u₂, fun i => ?_, ?_, ?_⟩
    · rw [form_add_right, hu₁, hu₂]; simp
    · rw [form_add_right, hxu₁, h2']; simp
    · rw [form_add_right, h1, hxu₂]; simp

  obtain ⟨l, hl0, hl⟩ : ∃ l : E, l ≠ 0 ∧ l * σ l * form σ J u u = l + σ l := by
    by_cases hN : form σ J u u = 0
    · exact ⟨δ, hδ, by rw [hN, hσδ]; ring⟩
    · have hσN : σ (form σ J u u) = form σ J u u := (form_conj hσ hJ u u).symm
      refine ⟨2 / form σ J u u, div_ne_zero h2 hN, ?_⟩
      rw [map_div₀, hσN, map_ofNat]
      field_simp; ring
  set z := qr σ J u l *ᵥ x with hz
  have hzx : z = x - (l * form σ J x u) • u := qr_mulVec u l x
  obtain ⟨g, hg, hgy, hgz⟩ := stepA hσ hJ y z x' (fun i => by
      rw [hzx, form_sub_right, form_smul_right, hu i, mul_zero, sub_zero, hy i])
    (by rw [hz, qr_form hσ hJ u l hl, hxx])
    (by
      have hval : form σ J z (z - x') = l * form σ J x u * form σ J u x' := by
        rw [hzx]
        simp only [form_sub_left, form_sub_right, form_smul_left, form_smul_right, map_mul]
        rw [form_sub_right] at hc
        rw [form_conj hσ hJ x u]
        linear_combination hc + (form σ J x u * σ (form σ J x u)) * hl
      rw [hval, form_conj hσ hJ x' u]
      refine mul_ne_zero (mul_ne_zero hl0 hxu) ?_
      intro h; apply hx'u; rw [← hσ (form σ J x' u), h, map_zero])
  refine ⟨g * qr σ J u l, isUn_mul hg (isUn_qr hσ hJ u l hl), fun i => ?_, ?_⟩
  · rw [← mulVec_mulVec, qr_fix u l (y i) (hu i), hgy i]
  · rw [← mulVec_mulVec, ← hz, hgz]

theorem form_dual (hσ : ∀ x, σ (σ x) = x) (hdet : IsUnit J.det) (m v : Fin n → E) :
    form σ J v (fun k => σ ((m ᵥ* J⁻¹) k)) = m ⬝ᵥ v := by
  unfold form
  simp only [hσ]
  rw [show (fun k => (m ᵥ* J⁻¹) k) = m ᵥ* J⁻¹ from rfl, ← dotProduct_mulVec, mulVec_mulVec,
    nonsing_inv_mul J hdet, one_mulVec]

theorem witt_vec (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (hdet : IsUnit J.det) {δ : E}
    (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (h2 : (2 : E) ≠ 0) (a : ℕ) :
    ∀ (x x' ℓ ℓ' : Fin a → Fin n → E), (∀ i j, ℓ i ⬝ᵥ x j = if i = j then 1 else 0) →
      (∀ i j, ℓ' i ⬝ᵥ x' j = if i = j then 1 else 0) →
      (∀ i j, form σ J (x i) (x j) = form σ J (x' i) (x' j)) →
      ∃ g, IsUn σ J g ∧ ∀ j, g *ᵥ x j = x' j := by
  induction a with
  | zero => intro x x' ℓ ℓ' _ _ _; exact ⟨1, isUn_one, fun j => j.elim0⟩
  | succ a ih =>
    intro x x' ℓ ℓ' hℓ hℓ' hx
    obtain ⟨g₁, hg₁, hg₁x⟩ := ih (fun j => x j.castSucc) (fun j => x' j.castSucc)
      (fun i => ℓ i.castSucc) (fun i => ℓ' i.castSucc)
      (fun i j => by simp [hℓ, Fin.castSucc_inj]) (fun i j => by simp [hℓ', Fin.castSucc_inj])
      (fun i j => hx _ _)
    have hinv : (J⁻¹ * cT σ g₁ * J) * g₁ = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ g₁), hg₁, nonsing_inv_mul J hdet]
    set m := ℓ (Fin.last a) ᵥ* (J⁻¹ * cT σ g₁ * J) with hm
    have hm' : ∀ v, m ⬝ᵥ (g₁ *ᵥ v) = ℓ (Fin.last a) ⬝ᵥ v := by
      intro v; rw [hm, ← dotProduct_mulVec, mulVec_mulVec, hinv, one_mulVec]
    obtain ⟨h, hh, hhy, hhx⟩ := step hσ hJ hδ hσδ h2 (fun i => x' i.castSucc) (g₁ *ᵥ x (Fin.last a))
      (x' (Fin.last a))
      (fun i => by
        have := isUn_form hg₁ (x i.castSucc) (x (Fin.last a))
        rw [hg₁x i, hx] at this; exact this)
      (by rw [isUn_form hg₁, hx])
      (fun k => σ ((m ᵥ* J⁻¹) k)) (fun k => σ ((ℓ' (Fin.last a) ᵥ* J⁻¹) k))
      (fun i => by rw [form_dual hσ hdet, ← hg₁x i, hm', hℓ]; simp [(Fin.castSucc_lt_last i).ne'])
      (by rw [form_dual hσ hdet, hm', hℓ]; simp)
      (fun i => by rw [form_dual hσ hdet, hℓ']; simp [(Fin.castSucc_lt_last i).ne'])
      (by rw [form_dual hσ hdet, hℓ']; simp)
    refine ⟨h * g₁, isUn_mul hh hg₁, fun j => ?_⟩
    rw [← mulVec_mulVec]
    induction j using Fin.lastCases with
    | last => exact hhx
    | cast i => rw [hg₁x i, hhy i]

theorem pairM_entry {a : ℕ} (X : Matrix (Fin n) (Fin a) E) (i j : Fin a) :
    pairM σ J X X i j = form σ J (fun k => X k j) (fun k => X k i) := by
  simp only [pairM, cT, form, Matrix.mul_apply, mulVec, dotProduct, transpose_apply, map_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.SgAlg.WittField

open GlobalTheory.SgAlg Matrix in

theorem GlobalTheory.SgAlg.witt_free_field : ∀ {E : Type} [Field E] (σ : E →+* E), IsQA σ → ∀ {n a : ℕ}
    (J : Matrix (Fin n) (Fin n) E), IsHermU σ J → ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X →
    Free X' → pairM σ J X X = pairM σ J X' X' → ∃ g, IsUn σ J g ∧ g * X = X' := by
  intro E _ σ hQ n a J hJ X X' ⟨L, hL⟩ ⟨L', hL'⟩ hG
  obtain ⟨hσ, ⟨e, he⟩, -, h2, -⟩ := hQ
  have hδ : e - σ e ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
  have hσδ : σ (e - σ e) = -(e - σ e) := by rw [map_sub, hσ]; ring
  obtain ⟨g, hg, hgx⟩ := WittField.witt_vec hσ hJ.1 hJ.2 hδ hσδ h2.ne_zero a
    (fun j k => X k j) (fun j k => X' k j) (fun i => L i) (fun i => L' i)
    (fun i j => by rw [← Matrix.mul_apply', hL, Matrix.one_apply])
    (fun i j => by rw [← Matrix.mul_apply', hL', Matrix.one_apply])
    (fun i j => by rw [← WittField.pairM_entry X j i, ← WittField.pairM_entry X' j i, hG])
  refine ⟨g, hg, ?_⟩
  ext k j
  have := congrFun (hgx j) k
  simpa [Matrix.mul_apply, mulVec, dotProduct] using this
