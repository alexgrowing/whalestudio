import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PiNonunit

noncomputable section
open Matrix

namespace PI.SqPair.LCP

section Alg
variable {R : Type} [CommRing R] [StarRing R]

def e0 : Matrix (Fin 2) (Fin 2) R := diagonal ![1, 0]

theorem finiteAdeleIdempotentOfF_mul_self : (e0 : Matrix (Fin 2) (Fin 2) R) * e0 = e0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e0]

theorem elementary_hyperbolic : (e0 : Matrix (Fin 2) (Fin 2) R)ᴴ * hyp = hyp - hyp * e0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e0, hyp, Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct, diagonal_apply]

theorem elementary_commutes_diagonal (d : Fin 2 → R) :
    (e0 : Matrix (Fin 2) (Fin 2) R) * diagonal d = diagonal d * e0 := by
  rw [e0, diagonal_mul_diagonal, diagonal_mul_diagonal]; congr 1; ext i; ring

theorem isUnit_ct {ι : Type} [Fintype ι] [DecidableEq ι] {u : Matrix ι ι R} (hu : IsUnit u.det) :
    IsUnit uᴴ := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_conjTranspose]; exact hu.star)

theorem cancel_conj {ι : Type} [Fintype ι] [DecidableEq ι] {u X Y : Matrix ι ι R}
    (hu : IsUnit u.det) (h : uᴴ * X * u = uᴴ * Y * u) : X = Y := by
  have hU : IsUnit u := (Matrix.isUnit_iff_isUnit_det _).2 hu
  have h2 : uᴴ * X = uᴴ * Y := hU.mul_right_cancel h
  exact (isUnit_ct hu).mul_left_cancel h2

theorem assemble {κ : Type} [Fintype κ] [DecidableEq κ]
    (A h u u' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) (A₁ h₂ : Matrix κ κ R) (d : Fin 2 → R)
    (hu : IsUnit u.det) (hu' : IsUnit u'.det)
    (hA : uᴴ * A * u = fromBlocks hyp 0 0 A₁)
    (hh : h * u' = u * fromBlocks (diagonal d) 0 0 h₂)
    (e₂ f₂ : Matrix κ κ R) (he : e₂ * e₂ = e₂) (heA : e₂ᴴ * A₁ = A₁ * (1 - e₂))
    (hef : e₂ * h₂ = h₂ * f₂) : PConcl A h := by
  set E : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks e0 0 0 e₂ with hEdef
  set F : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks e0 0 0 f₂ with hFdef
  set D : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks (diagonal d) 0 0 h₂ with hDdef
  set B : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks hyp 0 0 A₁ with hBdef
  have hi : u⁻¹ * u = 1 := nonsing_inv_mul u hu
  have hi' : u'⁻¹ * u' = 1 := nonsing_inv_mul u' hu'
  have hE : E * E = E := by simp [hEdef, fromBlocks_multiply, finiteAdeleIdempotentOfF_mul_self, he]
  have hED : E * D = D * F := by simp [hEdef, hDdef, hFdef, fromBlocks_multiply, elementary_commutes_diagonal, hef]
  have heA' : e₂ᴴ * A₁ = A₁ - A₁ * e₂ := by rw [heA, Matrix.mul_sub, Matrix.mul_one]
  have hEB : Eᴴ * B = B - B * E := by
    rw [hEdef, hBdef, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    ext (i | i) (j | j) <;>
      simp [elementary_hyperbolic, heA', Matrix.sub_apply]
  refine ⟨u * E * u⁻¹, u' * F * u'⁻¹, ?_, ?_, ?_⟩
  · calc u * E * u⁻¹ * (u * E * u⁻¹) = u * (E * (u⁻¹ * u) * E) * u⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = u * E * u⁻¹ := by rw [hi, Matrix.mul_one, hE]
  · apply cancel_conj hu
    have hct : uᴴ * (u⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, hi, conjTranspose_one]
    calc uᴴ * ((u * E * u⁻¹)ᴴ * A) * u = (uᴴ * (u⁻¹)ᴴ) * Eᴴ * (uᴴ * A * u) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Eᴴ * B := by rw [hct, Matrix.one_mul, hA]
      _ = B - B * E * (u⁻¹ * u) := by rw [hi, Matrix.mul_one, hEB]
      _ = uᴴ * (A * (1 - u * E * u⁻¹)) * u := by
          rw [← hA]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  · have hh' : h = u * D * u'⁻¹ := by
      rw [← hh, Matrix.mul_assoc, mul_nonsing_inv u' hu', Matrix.mul_one]
    rw [hh']
    calc u * E * u⁻¹ * (u * D * u'⁻¹) = u * (E * (u⁻¹ * u) * D) * u'⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = u * (D * (u'⁻¹ * u') * F) * u'⁻¹ := by rw [hi, hi', Matrix.mul_one, Matrix.mul_one, hED]
      _ = u * D * u'⁻¹ * (u' * F * u'⁻¹) := by simp only [Matrix.mul_assoc]

theorem blk_unimod {κ : Type} [Fintype κ] [DecidableEq κ]
    {A u : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R} {A₁ : Matrix κ κ R} (hu : IsUnit u.det)
    (hA : Unimod A) (h : uᴴ * A * u = fromBlocks hyp 0 0 A₁) : Unimod A₁ := by
  constructor
  · have h1 : (uᴴ * A * u)ᴴ = uᴴ * A * u := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA.1, Matrix.mul_assoc]
    rw [h, fromBlocks_conjTranspose] at h1
    exact (fromBlocks_inj.1 h1).2.2.2
  · have h1 : IsUnit (uᴴ * A * u).det := by
      rw [det_mul, det_mul, det_conjTranspose]; exact (hu.star.mul hA.2).mul hu
    rw [h, det_fromBlocks_zero₂₁] at h1
    exact isUnit_of_mul_isUnit_right h1

theorem blk_rel {κ : Type} [Fintype κ] [DecidableEq κ] (ϖ : R) (k : ℕ)
    (A A' h u u' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) (A₁ A₁' h₂ : Matrix κ κ R) (d : Fin 2 → R)
    (hrel : hᴴ * A * h = (ϖ ^ (2 * k)) • A')
    (hA : uᴴ * A * u = fromBlocks hyp 0 0 A₁) (hA' : u'ᴴ * A' * u' = fromBlocks hyp 0 0 A₁')
    (hh : h * u' = u * fromBlocks (diagonal d) 0 0 h₂) :
    h₂ᴴ * A₁ * h₂ = (ϖ ^ (2 * k)) • A₁' := by
  have e1 : (h * u')ᴴ * A * (h * u') = (ϖ ^ (2 * k)) • fromBlocks hyp 0 0 A₁' := by
    rw [← hA', conjTranspose_mul]
    calc u'ᴴ * hᴴ * A * (h * u') = u'ᴴ * (hᴴ * A * h) * u' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hrel, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : (h * u')ᴴ * A * (h * u') = (fromBlocks (diagonal d) 0 0 h₂)ᴴ *
      (uᴴ * A * u) * fromBlocks (diagonal d) 0 0 h₂ := by
    rw [hh, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e2, hA, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_smul] at e1
  have := (fromBlocks_inj.1 e1).2.2.2
  simpa using this

theorem phyp_reindex {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (s : κ ≃ ι) {ϖ : R} {A A' h : Matrix ι ι R} {k : ℕ} (hP : PHyp ϖ A A' h k) :
    PHyp ϖ (A.submatrix s s) (A'.submatrix s s) (h.submatrix s s) k := by
  obtain ⟨⟨hA, hAd⟩, ⟨hA', hA'd⟩, hr⟩ := hP
  refine ⟨⟨by rw [conjTranspose_submatrix, hA], by rw [det_submatrix_equiv_self]; exact hAd⟩,
    ⟨by rw [conjTranspose_submatrix, hA'], by rw [det_submatrix_equiv_self]; exact hA'd⟩, ?_⟩
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hr, submatrix_smul]; rfl

theorem isBase_reindex {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (s : κ ≃ ι) {ϖ : R} {h : Matrix ι ι R} {k : ℕ} (hb : IsBase ϖ (h.submatrix s s) k) :
    IsBase ϖ h k := by
  obtain ⟨h₁, hu, he⟩ := hb
  refine ⟨h₁.submatrix s.symm s.symm, by rw [det_submatrix_equiv_self]; exact hu, ?_⟩
  have : h = (h.submatrix s s).submatrix s.symm s.symm := by simp
  rw [this, he, submatrix_smul]; rfl

theorem pconcl_reindex {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (s : κ ≃ ι) {A h : Matrix ι ι R} (hc : PConcl (A.submatrix s s) (h.submatrix s s)) :
    PConcl A h := by
  obtain ⟨e, f, he, heA, hef⟩ := hc
  have hA : A = (A.submatrix s s).submatrix s.symm s.symm := by simp
  have hh : h = (h.submatrix s s).submatrix s.symm s.symm := by simp
  refine ⟨e.submatrix s.symm s.symm, f.submatrix s.symm s.symm, ?_, ?_, ?_⟩
  · rw [submatrix_mul_equiv, he]
  · rw [hA, conjTranspose_submatrix, submatrix_mul_equiv, heA, ← submatrix_one_equiv s.symm]
    rw [show ((1 : Matrix κ κ R).submatrix s.symm s.symm) - e.submatrix s.symm s.symm
      = (1 - e).submatrix s.symm s.symm from rfl, submatrix_mul_equiv]
  · rw [hh, submatrix_mul_equiv, submatrix_mul_equiv, hef]

end Alg

theorem pgen_main (hB : BaseLag) (hS : Step) {R : Type} [CommRing R] [StarRing R]
    (R₀ : Subring R) [HenselianLocalRing R₀] [Finite (IsLocalRing.ResidueField R₀)] (ϖ : R)
    (hI : Inert R₀ ϖ) (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      Fintype.card ι = n → Even n → PGen ϖ ι := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ _ hc hev A A' h k hP
  by_cases hb : IsBase ϖ h k
  · obtain ⟨h₁, hh₁, rfl⟩ := hb
    obtain ⟨e, he, heA⟩ := hB R R₀ ϖ hI ι (hc ▸ hev) A hP.1
    refine ⟨e, h₁⁻¹ * e * h₁, he, heA, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [← Matrix.mul_assoc, mul_nonsing_inv h₁ hh₁, Matrix.one_mul]
  · match n, ih, hc, hev with
    | 0, _, hc, _ =>
      have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hc
      exact absurd ⟨1, by simp, by ext i; exact isEmptyElim i⟩ hb
    | 1, _, _, hev => exact absurd hev (by decide)
    | m + 2, ih, hc, hev =>
      let s : Fin 2 ⊕ Fin m ≃ ι := Fintype.equivOfCardEq (by simp [hc]; omega)
      apply pconcl_reindex s
      have hP' := phyp_reindex s hP
      have hb' : ¬ IsBase ϖ (h.submatrix s s) k := fun hb' => hb (isBase_reindex s hb')
      obtain ⟨u, u', A₁, A₁', h₂, d, hu, hu', hA, hA', hh⟩ := hS R R₀ ϖ hI (Fin m) _ _ _ k hP' hb'
      have hU₁ := blk_unimod hu hP'.1 hA
      have hU₁' := blk_unimod hu' hP'.2.1 hA'
      have hr := blk_rel ϖ k _ _ _ u u' A₁ A₁' h₂ d hP'.2.2 hA hA' hh
      have hevm : Even m := by
        obtain ⟨r, hr⟩ := hev; exact ⟨r - 1, by omega⟩
      obtain ⟨e₂, f₂, he, heA, hef⟩ :=
        ih m (by omega) (Fin m) (Fintype.card_fin m) hevm A₁ A₁' h₂ k ⟨hU₁, hU₁', hr⟩
      exact assemble _ _ u u' A₁ h₂ d hu hu' hA hh e₂ f₂ he heA hef

theorem locCartanPair_of (h1 : Dichotomy) (hB : BaseLag) (hS : Step) :
    PI.SqPair.LocCartanPair := by
  intro R _ σ hσ R₀ hR₀ _ _ _ _ hθ ϖ hϖ N hN k h hh
  let _ : StarRing R :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := fun a b => map_add σ a b }
  have hR₀' : ∀ x, x ∈ R₀ ↔ star x = x := hR₀
  have hθ' : ∃ θ : R, IsUnit (θ - star θ) := hθ
  have hh' : hᴴ * 1 * h = ((ϖ : R) ^ (2 * k)) • (1 : Matrix (Fin N) (Fin N) R) := by
    rw [Matrix.mul_one]; exact hh
  rcases h1 R R₀ hR₀' hθ' ϖ hϖ with ⟨ε, hε, hεs⟩ | hI
  · refine ⟨ε • 1, ε • 1, ?_, ?_, ?_⟩
    · simp [smul_smul, hε]
    · change (ε • (1 : Matrix (Fin N) (Fin N) R))ᴴ = _
      rw [conjTranspose_smul, conjTranspose_one, hεs, sub_smul, one_smul]
    · simp
  · obtain ⟨e, f, he, heA, hef⟩ := pgen_main hB hS R₀ (ϖ : R) hI N (Fin N) (Fintype.card_fin N) hN
      1 1 h k ⟨⟨conjTranspose_one, by simp⟩, ⟨conjTranspose_one, by simp⟩, hh'⟩
    refine ⟨e, f, he, ?_, hef⟩
    rw [Matrix.mul_one, Matrix.one_mul] at heA
    exact heA

end PI.SqPair.LCP
