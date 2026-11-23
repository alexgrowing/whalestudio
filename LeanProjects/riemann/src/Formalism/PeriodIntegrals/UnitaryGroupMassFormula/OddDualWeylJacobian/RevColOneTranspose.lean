import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

section Lin

variable {R : Type} [CommRing R] {k M : ℕ}

theorem rel_add {f g f' g' : MvPolynomial (Fin k × Fin k) R} (h1 : Rel R k M f f') (h2 : Rel R k M g g') :
    Rel R k M (f + g) (f' + g') := by
  unfold Rel at *
  rw [map_add, h1, h2, mul_add]

theorem rel_smul {f f' : MvPolynomial (Fin k × Fin k) R} (c : R) (h : Rel R k M f f') :
    Rel R k M (c • f) (c • f') := by
  unfold Rel at *
  rw [map_smul, h, mul_smul_comm]

theorem rel_zero : Rel R k M (0 : MvPolynomial (Fin k × Fin k) R) 0 := by
  unfold Rel
  simp

theorem rel_natMul {f f' : MvPolynomial (Fin k × Fin k) R} (n : ℕ) (h : Rel R k M f f') :
    Rel R k M ((n : MvPolynomial (Fin k × Fin k) R) * f) ((n : MvPolynomial (Fin k × Fin k) R) * f') := by
  unfold Rel at *
  rw [map_mul, map_natCast, h]
  ring

theorem rowDiv_add (a b : Fin k) (j : ℕ) (f g : MvPolynomial (Fin k × Fin k) R) :
    rowDiv R a b j (f + g) = rowDiv R a b j f + rowDiv R a b j g := by
  simp only [rowDiv, map_add, Polynomial.coeff_add]

theorem rowDiv_smul (a b : Fin k) (j : ℕ) (c : R) (f : MvPolynomial (Fin k × Fin k) R) :
    rowDiv R a b j (c • f) = c • rowDiv R a b j f := by
  simp only [rowDiv, map_smul, Polynomial.coeff_smul]

def rowDivL (a b : Fin k) (j : ℕ) : MvPolynomial (Fin k × Fin k) R →ₗ[R] MvPolynomial (Fin k × Fin k) R where
  toFun := rowDiv R a b j
  map_add' := rowDiv_add a b j
  map_smul' := rowDiv_smul a b j

theorem weyl_rowDiv {ν : Fin k → ℕ} (a b : Fin k) (j : ℕ) {f : MvPolynomial (Fin k × Fin k) R}
    (hf : f ∈ weyl R k k le_rfl ν) : rowDiv R a b j f ∈ weyl R k k le_rfl ν := by
  have key : weyl R k k le_rfl ν ≤ (weyl R k k le_rfl ν).comap (rowDivL a b j) := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨(a, b, j) :: w, rfl⟩
  exact key hf

theorem applyWord_nil {ν : MvPolynomial (Fin k × Fin k) R} : applyWord R [] ν = ν := rfl

theorem applyWord_cons (x : Fin k × Fin k × ℕ) (w : List (Fin k × Fin k × ℕ)) (f : MvPolynomial (Fin k × Fin k) R) :
    applyWord R (x :: w) f = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) := rfl

theorem mem_of_pm {S : Submodule R (MvPolynomial (Fin k × Fin k) R)} {x : MvPolynomial (Fin k × Fin k) R}
    (u : MvPolynomial (Fin k × Fin k) R) (hu : u = 1 ∨ u = -1) (hx : x ∈ S) : u * x ∈ S := by
  rcases hu with rfl | rfl
  · rw [one_mul]; exact hx
  · rw [neg_one_mul]; exact S.neg_mem hx

end Lin

private theorem mh_applyWord_hw (hMh : MHhw) (hMd : MHdiv)
    (R : Type) [CommRing R] (k : ℕ) (ν : Fin k → ℕ) (w : List (Fin k × Fin k × ℕ)) :
    MH R (applyWord R w (hw R (le_refl k) ν)) := by
  induction w with
  | nil => exact hMh R k ν
  | cons x w ih => exact hMd R k x.1 x.2.1 x.2.2 _ ih

theorem core1 (h1 : W1) (hMh : MHhw) (hMd : MHdiv) (hD : Diag) (hL : LowMem) (h4 : W4hw)
    (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ) (hl : Antitone lam) :
    ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
      Rel R (m + 1) (expM lam) f f' := by
  have hCu : ∀ u : R, (u = 1 ∨ u = -1) → (C u : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) = 1 ∨
      (C u : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) = -1 := by
    intro u hu
    rcases hu with rfl | rfl
    · left; exact C_1
    · right; rw [C_neg, C_1]
  have key : ∀ w : List (Fin (m + 1) × Fin (m + 1) × ℕ),
      ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam)
          (applyWord R w (hw R le_rfl (nuOf lam))) f' := by
    intro w
    induction w with
    | nil =>
      obtain ⟨u, hu, hrel⟩ := h4 R m lam hl
      exact ⟨C u * low R (nuOf (lamStar lam)),
        mem_of_pm _ (hCu u hu) (hL R (m + 1) _), hrel⟩
    | cons x w ih =>
      obtain ⟨f', hf', hrel⟩ := ih
      obtain ⟨a, b, j⟩ := x
      rw [applyWord_cons]
      dsimp only
      rcases eq_or_ne a b with rfl | hab
      · obtain ⟨d, hd⟩ := mh_applyWord_hw hMh hMd R (m + 1) (nuOf lam) w a
        rw [hD R (m + 1) a j d _ hd]
        refine ⟨((d.choose j : ℕ) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) * f', ?_,
          (rel_natMul (h := hrel)) _⟩
        rw [← nsmul_eq_mul]
        exact nsmul_mem hf' _
      · exact ⟨(-1) ^ j * rowDiv R b a j f',
          mem_of_pm _ (neg_one_pow_eq_or _ j) (weyl_rowDiv b a j hf'),
          h1 R (m + 1) (expM lam) a b j _ f' hab hrel⟩
  intro f hf
  let S : Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
    { carrier := {f | ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam) f f'}
      add_mem' := by
        rintro f g ⟨f', hf', h⟩ ⟨g', hg', h'⟩
        exact ⟨f' + g', Submodule.add_mem _ hf' hg', (rel_add h) h'⟩
      zero_mem' := ⟨0, Submodule.zero_mem _, rel_zero⟩
      smul_mem' := by
        rintro c f ⟨f', hf', h⟩
        exact ⟨c • f', Submodule.smul_mem _ c hf', (rel_smul (h := h)) c⟩ }
  have hle : weyl R (m + 1) (m + 1) le_rfl (nuOf lam) ≤ S := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact key w
  exact hle hf

section Top

variable {K : Type} [Field K]

theorem lamStar_lamStar {m : ℕ} (lam : Fin (m + 1) → ℤ) : lamStar (lamStar lam) = lam := by
  funext i
  simp [lamStar]

theorem antitone_lamStar {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (lamStar lam) := by
  intro i j hij
  simp only [lamStar]
  exact neg_le_neg (h (Fin.rev_le_rev.mpr hij))

theorem isUnit_invT {n : ℕ} {g : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) : IsUnit ((g⁻¹)ᵀ).det := by
  rw [det_transpose]
  exact isUnit_nonsing_inv_det g hg

theorem invT_invT {n : ℕ} {g : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) : (((g⁻¹)ᵀ)⁻¹)ᵀ = g := by
  have h1 : IsUnit (gᵀ).det := by rwa [det_transpose]
  rw [transpose_nonsing_inv g, nonsing_inv_nonsing_inv _ h1, transpose_transpose]

theorem revCol_eq {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : revCol A = A * revCol 1 := by
  ext i j
  simp [revCol, Matrix.mul_apply, Matrix.one_apply]

theorem revCol_one_mul_self {m : ℕ} : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) * revCol 1 = 1 := by
  rw [← revCol_eq]
  ext i j
  simp only [revCol, submatrix_apply]
  rw [Fin.rev_rev]
  rfl

theorem revCol_one_transpose {m : ℕ} : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K))ᵀ = revCol 1 := by
  ext i j
  simp only [revCol, transpose_apply, submatrix_apply, id_eq, one_apply]
  have h : (j = i.rev) ↔ (i = j.rev) :=
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  by_cases hij : i = j.rev
  · rw [if_pos hij, if_pos (h.mpr hij)]
  · rw [if_neg hij, if_neg (fun h' => hij (h.mp h'))]

theorem isUnit_revInv {m : ℕ} {z : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hz : IsUnit z.det) :
    IsUnit (revCol (z⁻¹)ᵀ).det := by
  have hP : IsUnit (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det := by
    have h : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det *
        (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det = 1 := by
      rw [← det_mul, revCol_one_mul_self, det_one]
    exact ⟨⟨_, _, h, h⟩, rfl⟩
  rw [revCol_eq, det_mul]
  exact (isUnit_invT hz).mul hP

theorem revInv_revInv {m : ℕ} {z : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hz : IsUnit z.det) :
    revCol ((revCol (z⁻¹)ᵀ)⁻¹)ᵀ = z := by
  have hP : revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * revCol 1 = 1 :=
    revCol_one_mul_self
  have hPinv : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K))⁻¹ = revCol 1 :=
    inv_eq_left_inv hP
  rw [revCol_eq ((z⁻¹)ᵀ), Matrix.mul_inv_rev, hPinv, transpose_mul, invT_invT hz,
    revCol_one_transpose, revCol_eq (z * revCol 1), mul_assoc, hP, mul_one]

theorem sgn_zpow_pm (hS : SgnPM) (m : ℕ) (n : ℤ) : sgnK K m ^ n = 1 ∨ sgnK K m ^ n = -1 := by
  rcases hS K m with h | h
  · left
    rw [h, _root_.one_zpow]
  · rw [h]
    rcases Int.even_or_odd n with he | ho
    · left
      exact he.neg_one_zpow
    · right
      exact ho.neg_one_zpow

private theorem eq_of_rel_of_isHomogeneous_of_uniq (hU : Uniq) {m M D : ℕ}
    {F F₁ F₂ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K}
    (h₁ : Rel K (m + 1) M F F₁) (h₂ : Rel K (m + 1) M F F₂)
    (d₁ : IsHomogeneous F₁ D) (d₂ : IsHomogeneous F₂ D) : F₁ = F₂ := by
  unfold Rel at h₁ h₂
  have hd : IsHomogeneous (F₁ - F₂) D := by
    rw [← mem_homogeneousSubmodule] at d₁ d₂ ⊢
    exact Submodule.sub_mem _ d₁ d₂
  have h0 : dualSub K (m + 1) (F₁ - F₂) = 0 := by
    rw [map_sub, h₁, h₂, sub_self]
  exact sub_eq_zero.mp (hU K (m + 1) D (F₁ - F₂) hd h0)

theorem dir1 (hC : ∀ (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
      ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam) f f')
    (hH : HomW) (hB : Bk) (hE : EV) (hU : Uniq) (hDB : DualB) (hS : SgnPM) (hG : GStep)
    (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) :
    ∀ F ∈ Dl0 O m lam (colSpan O g), ∃ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F' := by
  intro F hF
  by_cases hl : Antitone lam
  swap
  · unfold Dl0 at hF
    rw [if_neg hl, Submodule.mem_bot] at hF
    subst hF
    exact ⟨0, Submodule.zero_mem _, fun z _ => by simp⟩
  have hl' := antitone_lamStar hl
  unfold Dl0 at hF
  rw [if_pos hl] at hF
  simp only [Submodule.mem_iInf] at hF
  have hbal := hB m lam hl
  have hhom : ∀ f' ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
      IsHomogeneous f' (degW (nuOf (lamStar lam))) :=
    fun f' hf' => hH O (m + 1) _ f' hf'
  obtain ⟨F', -, hrel, hF'hom⟩ := hG O K m lam g hg hbal hhom (hC O m lam hl) F (hF g ⟨hg, rfl⟩)
  have hF'lat : F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ) := by
    unfold Dl0
    rw [if_pos hl']
    simp only [Submodule.mem_iInf]
    rintro g' ⟨hg', hspan⟩
    have hh : IsUnit ((g'⁻¹)ᵀ).det := isUnit_invT hg'
    have hspan' : colSpan O g = colSpan O (g'⁻¹)ᵀ := by
      have := hDB O K m (g⁻¹)ᵀ g' (isUnit_invT hg) hg' hspan
      rwa [invT_invT hg] at this
    obtain ⟨F'', hF''mem, hrel'', hF''hom⟩ :=
      hG O K m lam (g'⁻¹)ᵀ hh hbal hhom (hC O m lam hl) F (hF _ ⟨hh, hspan'⟩)
    rw [invT_invT hg'] at hF''mem
    rw [eq_of_rel_of_isHomogeneous_of_uniq hU hrel hrel'' hF'hom hF''hom]
    exact hF''mem
  refine ⟨C (sgnK K m ^ lamStar lam (Fin.last m)) * F', ?_,
    fun z hz => hE K m _ _ _ _ F F' hbal hrel hF'hom z hz⟩
  rcases sgn_zpow_pm (K := K) hS m (lamStar lam (Fin.last m)) with h | h
  · rw [h, C_1, one_mul]
    exact hF'lat
  · rw [h, C_neg, C_1, neg_one_mul]
    exact Submodule.neg_mem _ hF'lat

theorem oddFact_of (hC1 : ∀ (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
      ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam) f f')
    (hH : HomW) (hB : Bk) (hE : EV) (hU : Uniq) (hDB : DualB) (hS : SgnPM) (hG : GStep)
    (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : OddFact (K := K) O m lam := by
  intro g hg
  refine ⟨dir1 hC1 hH hB hE hU hDB hS hG O m lam g hg, ?_⟩
  intro F' hF'
  have hfw := dir1 hC1 hH hB hE hU hDB hS hG O m (lamStar lam) ((g⁻¹)ᵀ)
    (isUnit_invT hg)
  rw [lamStar_lamStar, invT_invT hg] at hfw
  obtain ⟨F, hF, hid⟩ := hfw F' hF'
  refine ⟨F, hF, fun z hz => ?_⟩
  have := hid (revCol (z⁻¹)ᵀ) (isUnit_revInv hz)
  rw [revInv_revInv hz] at this
  exact this.symm

theorem oddDualWeyl_of (h1 : W1) (hMh : MHhw) (hMd : MHdiv) (hD : Diag) (hL : LowMem) (h4 : W4hw)
    (hH : HomW) (hB : Bk) (hE : EV) (hU : Uniq) (hDB : DualB) (hS : SgnPM) (hG : GStep)
    (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : OddFact (K := K) O m lam := oddFact_of
    (fun R _ m lam hl => core1 h1 hMh hMd hD hL h4 R m lam hl)
    hH hB hE hU hDB hS hG O m lam

end Top

end PI.OddDualWeyl
