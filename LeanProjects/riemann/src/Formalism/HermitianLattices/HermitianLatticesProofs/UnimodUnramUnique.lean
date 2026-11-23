import Mathlib
import Formalism.HermitianLattices.StatementJac

noncomputable section

namespace Formalism.HermitianLatticesTheory

open Polynomial IsLocalRing Matrix

section Quad

variable {S : Type*} [CommRing S] [HenselianLocalRing S]

theorem unimodUnramUnique_lift (T N d s₀ t₀ : S)
    (h0 : s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d ∈ maximalIdeal S)
    (h1 : IsUnit (2 * s₀ + T * t₀)) :
    ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  set f : S[X] := X ^ 2 + C (T * t₀) * X + C (N * t₀ ^ 2 - d) with hfdef
  have hf : f.Monic := by rw [hfdef]; monicity!
  have he : f.eval s₀ = s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d := by
    rw [hfdef]; simp; ring
  have hd : f.derivative.eval s₀ = 2 * s₀ + T * t₀ := by
    rw [hfdef]; simp only [derivative_add, derivative_C, derivative_X_pow, derivative_C_mul_X, add_zero]
    simp
  obtain ⟨s, hs, -⟩ := HenselianLocalRing.is_henselian f hf s₀ (he ▸ h0) (hd ▸ h1)
  refine ⟨s, t₀, ?_⟩
  have h2 : f.eval s = 0 := hs
  rw [hfdef] at h2
  simp at h2
  linear_combination h2

theorem unimodUnramUnique_split (T N d r : S) (hr : r ^ 2 + T * r + N = 0)
    (hu : IsUnit (T + 2 * r)) : ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨1 + r * ((d - 1) * v), (d - 1) * v, ?_⟩
  linear_combination ((d - 1) * v) ^ 2 * hr + (d - 1) * hv

theorem unimodUnramUnique_ff {k : Type*} [Field k] [Finite k] (T N d : k)
    (hD : T ^ 2 - 4 * N ≠ 0) : ∃ a b : k, a ^ 2 + T * a * b + N * b ^ 2 = d := by
  classical
  have := Fintype.ofFinite k
  rcases Nat.mod_two_eq_zero_or_one (Fintype.card k) with h | h
  · obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (FiniteField.even_card_iff_char_two.2 h) d
    exact ⟨c, 0, by rw [hc]; ring⟩
  · have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero (fun hc => by
      rw [FiniteField.even_card_iff_char_two.1 hc] at h; exact absurd h (by decide))
    have hf : (X ^ 2 : k[X]).degree = 2 := by compute_degree!
    have hg : (C (-(T ^ 2 - 4 * N)) * X ^ 2 + C (-(4 * d)) : k[X]).degree = 2 := by
      compute_degree!
      intro h; exact hD (by linear_combination -h)
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg h
    simp at hxy
    refine ⟨(x - T * y) / 2, y, ?_⟩
    field_simp
    linear_combination hxy

theorem unimodUnramUnique_quad [Finite (ResidueField S)] (T N d : S)
    (hD : IsUnit (T ^ 2 - 4 * N)) (hd : IsUnit d) :
    ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  have hD' : residue S (T ^ 2 - 4 * N) ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hD
  have h2 : residue S 2 = 2 := map_ofNat _ 2
  have h4 : residue S 4 = 4 := map_ofNat _ 4
  by_cases hroot : ∃ ρ : ResidueField S, ρ ^ 2 + residue S T * ρ + residue S N = 0
  · obtain ⟨ρ, hρ⟩ := hroot
    obtain ⟨r₀, rfl⟩ := residue_surjective ρ
    set g : S[X] := X ^ 2 + C T * X + C N with hgdef
    have hg : g.Monic := by rw [hgdef]; monicity!
    have he : g.eval r₀ = r₀ ^ 2 + T * r₀ + N := by rw [hgdef]; simp
    have hd1 : g.derivative.eval r₀ = 2 * r₀ + T := by rw [hgdef]; simp; ring
    have hsq : (2 * r₀ + T) ^ 2 = (T ^ 2 - 4 * N) + 4 * (r₀ ^ 2 + T * r₀ + N) := by ring
    have h0 : g.eval r₀ ∈ maximalIdeal S := by
      rw [he, ← residue_eq_zero_iff]; simpa using hρ
    have h1 : IsUnit (g.derivative.eval r₀) := by
      rw [hd1, ← residue_ne_zero_iff_isUnit]
      intro hz
      apply hD'
      have key : residue S (T ^ 2 - 4 * N) = (residue S (2 * r₀ + T)) ^ 2
          - 4 * residue S (r₀ ^ 2 + T * r₀ + N) := by
        rw [← map_pow, ← map_ofNat (residue S) 4, ← map_mul, ← map_sub]
        congr 1; linear_combination -hsq
      have hz2 : residue S (r₀ ^ 2 + T * r₀ + N) = 0 := (residue_eq_zero_iff _).2 (he ▸ h0)
      rw [key, hz, hz2]; ring
    obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian g hg r₀ h0 h1
    have hr' : r ^ 2 + T * r + N = 0 := by
      have h2 : g.eval r = 0 := hr
      rw [hgdef] at h2; simpa using h2
    apply unimodUnramUnique_split T N d r hr'
    have : (T + 2 * r) ^ 2 = T ^ 2 - 4 * N := by linear_combination 4 * hr'
    rw [← isUnit_pow_iff (two_ne_zero), this]; exact hD
  · push Not at hroot
    have hN : IsUnit N := by
      rw [← residue_ne_zero_iff_isUnit]
      intro h; exact hroot 0 (by simp [h])
    obtain ⟨a, b, hab⟩ := unimodUnramUnique_ff (residue S T) (residue S N) (residue S d)
      (by simpa [h4] using hD')
    obtain ⟨s₀, rfl⟩ := residue_surjective a
    obtain ⟨t₀, rfl⟩ := residue_surjective b
    have h0 : s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d ∈ maximalIdeal S := by
      rw [← residue_eq_zero_iff]; simp only [map_sub, map_add, map_mul, map_pow]
      rw [hab]; ring
    by_cases hs : IsUnit (2 * s₀ + T * t₀)
    · exact unimodUnramUnique_lift T N d s₀ t₀ h0 hs
    ·
      have ht : IsUnit (T * s₀ + 2 * N * t₀) := by
        rw [← residue_ne_zero_iff_isUnit]
        rw [← residue_ne_zero_iff_isUnit, not_not] at hs
        intro ht
        have hs' := hs
        simp only [map_add, map_mul, h2] at hs' ht
        have hdz : residue S d ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hd
        apply hdz
        rw [← hab]
        have hDk : residue S T ^ 2 - 4 * residue S N ≠ 0 := by simpa [h4] using hD'
        have htz : residue S t₀ = 0 := by
          have : (residue S T ^ 2 - 4 * residue S N) * residue S t₀ = 0 := by
            linear_combination residue S T * hs' - 2 * ht
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hDk
          · exact h
        have hsz : residue S s₀ = 0 := by
          have : (residue S T ^ 2 - 4 * residue S N) * residue S s₀ = 0 := by
            linear_combination residue S T * ht - 2 * residue S N * hs'
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hDk
          · exact h
        simp [htz, hsz]
      obtain ⟨v, hv⟩ := hN.exists_right_inv
      obtain ⟨t, s, hts⟩ := unimodUnramUnique_lift (T * v) v (d * v) t₀ s₀
        (by
          have : t₀ ^ 2 + T * v * t₀ * s₀ + v * s₀ ^ 2 - d * v
              = v * (s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d) + (1 - N * v) * t₀ ^ 2 := by ring
          rw [this, hv, sub_self, zero_mul, add_zero]
          exact Ideal.mul_mem_left _ _ h0)
        (by
          have : 2 * t₀ + T * v * s₀ = v * (T * s₀ + 2 * N * t₀) + (1 - N * v) * (2 * t₀) := by ring
          rw [this, hv, sub_self, zero_mul, add_zero]
          exact (isUnit_iff_exists_inv.2 ⟨N, by rw [mul_comm]; exact hv⟩).mul ht)
      exact ⟨s, t, by linear_combination N * hts - (T * s * t + s ^ 2 - d) * hv⟩

end Quad

section Herm

variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}

theorem unimodUnramUnique_fixUnit (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {x : R} (hx : star x = x)
    (hu : IsUnit x) : IsUnit (⟨x, (hR₀ x).2 hx⟩ : R₀) := by
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have h1 : star y * x = 1 := by
    have := congrArg star hy
    rwa [star_mul, hx, star_one] at this
  have hy' : star y = y := by
    calc star y = star y * (x * y) := by rw [hy, mul_one]
      _ = (star y * x) * y := by ring
      _ = y := by rw [h1, one_mul]
  exact isUnit_iff_exists_inv.2 ⟨⟨y, (hR₀ y).2 hy'⟩, Subtype.ext hy⟩

theorem unimodUnramUnique_unitAdd [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {x y : R}
    (hx : star x = x) (hy : star y = y) (h : IsUnit (x + y)) : IsUnit x ∨ IsUnit y := by
  have hxy : star (x + y) = x + y := by rw [star_add, hx, hy]
  have := unimodUnramUnique_fixUnit hR₀ hxy h
  have e : (⟨x + y, (hR₀ _).2 hxy⟩ : R₀) = ⟨x, (hR₀ x).2 hx⟩ + ⟨y, (hR₀ y).2 hy⟩ := rfl
  rw [e] at this
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h1 | h1
  · exact Or.inl (by simpa using h1.map R₀.subtype)
  · exact Or.inr (by simpa using h1.map R₀.subtype)

theorem unimodUnramUnique_trFix (x : R) : star (x + star x) = x + star x := by
  rw [star_add, star_star, add_comm]

theorem unimodUnramUnique_nontriv [IsLocalRing R₀] : Nontrivial R :=
  ⟨⟨0, 1, fun h => zero_ne_one (α := R₀) (Subtype.ext (by simpa using h))⟩⟩

def unimodUnramUnique_J [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) : Ideal R where
  carrier := {r | ∀ c : R, ¬ IsUnit (c * r + star (c * r))}
  add_mem' := by
    intro a b ha hb c h
    have e : c * (a + b) + star (c * (a + b))
        = (c * a + star (c * a)) + (c * b + star (c * b)) := by
      rw [mul_add, star_add]; ring
    rw [e] at h
    rcases unimodUnramUnique_unitAdd hR₀ (unimodUnramUnique_trFix _)
      (unimodUnramUnique_trFix _) h with h | h
    exacts [ha c h, hb c h]
  zero_mem' := fun c => by
    have := unimodUnramUnique_nontriv (R₀ := R₀)
    simp
  smul_mem' := by
    intro a r hr c
    simpa [smul_eq_mul, mul_assoc] using hr (c * a)

theorem unimodUnramUnique_mem_J [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) (r : R) :
    r ∈ unimodUnramUnique_J hR₀ ↔ ∀ c : R, ¬ IsUnit (c * r + star (c * r)) := Iff.rfl

theorem unimodUnramUnique_hermFix {ι : Type} (A : Matrix ι ι R) (hA : Aᴴ = A) (i j : ι) :
    star (A j i) = A i j := by
  simpa [conjTranspose_apply] using congrFun (congrFun hA i) j

theorem unimodUnramUnique_offdiag [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x)
    {θ : R} (hθ : IsUnit (θ - star θ)) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι R) (hA : Aᴴ = A) (hdet : IsUnit A.det) (hdiag : ∀ i, ¬ IsUnit (A i i)) :
    ∃ i j c, i ≠ j ∧ IsUnit (c * A i j + star (c * A i j)) := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ i j, A i j ∈ unimodUnramUnique_J hR₀ := by
    intro i j
    rw [unimodUnramUnique_mem_J]
    intro c
    by_cases hij : i = j
    · subst hij
      have hfix := unimodUnramUnique_hermFix A hA i i
      have e : c * A i i + star (c * A i i) = (c + star c) * A i i := by
        rw [star_mul, hfix]; ring
      rw [e]; exact fun h => hdiag i (isUnit_of_mul_isUnit_right h)
    · exact hcon i j c hij
  have hdetJ : A.det ∈ unimodUnramUnique_J hR₀ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]
    have : (Ideal.Quotient.mk (unimodUnramUnique_J hR₀)).mapMatrix A = 0 := by
      ext i j
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hmem i j
    rw [this, det_zero]
  have htop := Ideal.eq_top_of_isUnit_mem _ hdetJ hdet
  have h1 : (1 : R) ∈ unimodUnramUnique_J hR₀ := htop ▸ Submodule.mem_top
  rw [unimodUnramUnique_mem_J] at h1
  obtain ⟨v, hv⟩ := hθ.exists_right_inv
  apply h1 (θ * v)
  have h2 : star v * (θ - star θ) = -1 := by
    have := congrArg star hv
    rw [star_mul, star_sub, star_star, star_one] at this
    linear_combination -this
  have hsv : star v = -v := by
    calc star v = star v * ((θ - star θ) * v) := by rw [hv, mul_one]
      _ = (star v * (θ - star θ)) * v := by ring
      _ = -v := by rw [h2]; ring
  have : θ * v * 1 + star (θ * v * 1) = 1 := by
    rw [mul_one, star_mul, hsv]; linear_combination hv
  rw [this]; exact isUnit_one

theorem unimodUnramUnique_norm [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ)) {d : R}
    (hd : star d = d) (hdu : IsUnit d) : ∃ w : R, star w * w = d := by
  have hT : star (θ + star θ) = θ + star θ := unimodUnramUnique_trFix θ
  have hN : star (star θ * θ) = star θ * θ := by rw [star_mul, star_star]
  have hD : star ((θ - star θ) ^ 2) = (θ - star θ) ^ 2 := by
    rw [star_pow, star_sub, star_star]; ring
  set T : R₀ := ⟨θ + star θ, (hR₀ _).2 hT⟩ with hTdef
  set N : R₀ := ⟨star θ * θ, (hR₀ _).2 hN⟩ with hNdef
  set d₀ : R₀ := ⟨d, (hR₀ _).2 hd⟩ with hd₀def
  have hDu : IsUnit (T ^ 2 - 4 * N) := by
    have := unimodUnramUnique_fixUnit hR₀ hD (hθ.pow 2)
    convert this using 1
    apply Subtype.ext
    simp only [hTdef, hNdef]
    push_cast
    rw [show ((4 : R₀) : R) = 4 from map_ofNat R₀.subtype 4]
    ring
  obtain ⟨s, t, hst⟩ :=
    unimodUnramUnique_quad T N d₀ hDu (unimodUnramUnique_fixUnit hR₀ hd hdu)
  refine ⟨(s : R) + (t : R) * θ, ?_⟩
  have hs : star (s : R) = s := (hR₀ _).1 s.2
  have ht : star (t : R) = t := (hR₀ _).1 t.2
  have := congrArg Subtype.val hst
  simp only [hTdef, hNdef, hd₀def] at this
  push_cast at this
  rw [star_add, star_mul, hs, ht]
  linear_combination this

theorem unimodUnramUnique_scale [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (hA : Aᴴ = A) (i : ι)
    (hi : IsUnit (A i i)) : ∃ g : Matrix ι ι R, IsUnit g.det ∧ (gᴴ * A * g) i i = 1 := by
  have hfix := unimodUnramUnique_hermFix A hA i i
  obtain ⟨v, hv⟩ := hi.exists_right_inv
  have h1 : star v * A i i = 1 := by
    have := congrArg star hv; rwa [star_mul, hfix, star_one] at this
  have hvfix : star v = v := by
    calc star v = star v * (A i i * v) := by rw [hv, mul_one]
      _ = (star v * A i i) * v := by ring
      _ = v := by rw [h1, one_mul]
  have hvu : IsUnit v := isUnit_iff_exists_inv.2 ⟨A i i, by rw [mul_comm]; exact hv⟩
  obtain ⟨w, hw⟩ := unimodUnramUnique_norm hR₀ hθ hvfix hvu
  have hwu : IsUnit w := isUnit_of_mul_isUnit_right (hw ▸ hvu)
  refine ⟨diagonal (Function.update 1 i w), ?_, ?_⟩
  · rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simpa using hwu
  · rw [diagonal_conjTranspose]
    simp [diagonal_mul, mul_diagonal]
    linear_combination (A i i) * hw + hv

theorem unimodUnramUnique_transv {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R)
    (i j : ι) (c : R) :
    ((transvection j i c)ᴴ * A * transvection j i c) i i
      = A i i + (c * A i j + star c * A j i) + star c * c * A j j := by
  simp [transvection, Matrix.add_mul, Matrix.mul_add, conjTranspose_single,
    single_mul_apply_same, mul_single_apply_same, Matrix.mul_assoc]
  ring

theorem unimodUnramUnique_diag [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι R) (hA : Aᴴ = A)
    (hdet : IsUnit A.det) : ∃ g : Matrix ι ι R, IsUnit g.det ∧ ∃ i, (gᴴ * A * g) i i = 1 := by
  by_cases h : ∃ i, IsUnit (A i i)
  · obtain ⟨i, hi⟩ := h
    obtain ⟨g, hg, hgi⟩ := unimodUnramUnique_scale hR₀ hθ A hA i hi
    exact ⟨g, hg, i, hgi⟩
  · push Not at h
    obtain ⟨i, j, c, hij, hc⟩ := unimodUnramUnique_offdiag hR₀ hθ A hA hdet h
    set g₁ := transvection j i c with hg₁def
    set B := g₁ᴴ * A * g₁ with hBdef
    have hB : Bᴴ = B := by simp [hBdef, conjTranspose_mul, hA, Matrix.mul_assoc]
    have hBi : IsUnit (B i i) := by
      rw [hBdef, hg₁def, unimodUnramUnique_transv A i j c]
      have hji : A j i = star (A i j) := (unimodUnramUnique_hermFix A hA j i).symm
      have hfi := unimodUnramUnique_hermFix A hA i i
      have hfj := unimodUnramUnique_hermFix A hA j j
      have e : A i i + (c * A i j + star c * A j i) + star c * c * A j j
          = (c * A i j + star (c * A i j)) + (A i i + star c * c * A j j) := by
        rw [star_mul, ← hji]; ring
      rw [e]
      have hfy : star (A i i + star c * c * A j j) = A i i + star c * c * A j j := by
        simp only [star_add, star_mul, star_star, hfi, hfj]; ring
      have hy : ¬ IsUnit (A i i + star c * c * A j j) := by
        intro hy
        have hfz : star (star c * c * A j j) = star c * c * A j j := by
          simp only [star_mul, star_star, hfj]; ring
        rcases unimodUnramUnique_unitAdd hR₀ hfi hfz hy with h1 | h1
        · exact h i h1
        · exact h j (isUnit_of_mul_isUnit_right h1)
      by_contra hn
      have hsum : IsUnit ((c * A i j + star (c * A i j) + (A i i + star c * c * A j j))
          + -(A i i + star c * c * A j j)) := by rw [add_neg_cancel_right]; exact hc
      have hfs : star (c * A i j + star (c * A i j) + (A i i + star c * c * A j j))
          = c * A i j + star (c * A i j) + (A i i + star c * c * A j j) := by
        rw [star_add, unimodUnramUnique_trFix, hfy]
      have hfn : star (-(A i i + star c * c * A j j)) = -(A i i + star c * c * A j j) := by
        rw [star_neg, hfy]
      rcases unimodUnramUnique_unitAdd hR₀ hfs hfn hsum with h1 | h1
      · exact hn h1
      · exact hy (IsUnit.neg_iff _ |>.1 h1)
    obtain ⟨g₂, hg₂, hg₂i⟩ := unimodUnramUnique_scale hR₀ hθ B hB i hBi
    refine ⟨g₁ * g₂, ?_, i, ?_⟩
    · rw [det_mul, hg₁def, det_transvection_of_ne j i (Ne.symm hij), one_mul]; exact hg₂
    · rw [← hg₂i, hBdef]; simp [conjTranspose_mul, Matrix.mul_assoc]

theorem unimodUnramUnique_block {κ : Type} [Fintype κ] [DecidableEq κ]
    (IH : ∀ A : Matrix κ κ R, Aᴴ = A → IsUnit A.det →
      ∃ g : Matrix κ κ R, IsUnit g.det ∧ gᴴ * A * g = 1)
    (B : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R) (hB : Bᴴ = B) (hdet : IsUnit B.det)
    (h1 : B (Sum.inl ()) (Sum.inl ()) = 1) :
    ∃ g : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R, IsUnit g.det ∧ gᴴ * B * g = 1 := by
  have hB11 : B.toBlocks₁₁ = 1 := by
    ext a b; cases a; cases b; simpa [toBlocks₁₁] using h1
  set P := B.toBlocks₁₂
  set Q := B.toBlocks₂₁
  set D₀ := B.toBlocks₂₂
  have hBe : B = fromBlocks 1 P Q D₀ := by rw [← hB11, fromBlocks_toBlocks]
  rw [hBe] at hB hdet ⊢
  rw [fromBlocks_conjTranspose] at hB
  obtain ⟨-, hQP, hPQ, hD₀⟩ := fromBlocks_inj.1 hB
  rw [det_fromBlocks_one₁₁] at hdet
  have hD : (D₀ - Q * P)ᴴ = D₀ - Q * P := by
    rw [conjTranspose_sub, conjTranspose_mul, hD₀, hPQ, hQP]
  obtain ⟨g', hg', hg'D⟩ := IH _ hD hdet
  refine ⟨fromBlocks 1 (-(P * g')) 0 g', ?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, det_one, one_mul]; exact hg'
  · rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_one]
    rw [← hg'D]
    simp only [conjTranspose_one, conjTranspose_zero, conjTranspose_neg, conjTranspose_mul, hPQ]
    congr 1 <;> simp [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] <;> abel

theorem unimodUnramUnique_transport {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ]
    [DecidableEq ι] (e : κ ≃ ι) (B : Matrix ι ι R) (g : Matrix κ κ R)
    (hg : gᴴ * B.submatrix e e * g = 1) :
    (g.submatrix e.symm e.symm)ᴴ * B * g.submatrix e.symm e.symm = 1 := by
  have hB : B = (B.submatrix e e).submatrix e.symm e.symm := by simp
  rw [hB, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hg,
    submatrix_one_equiv]

theorem unimodUnramUnique_main [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ)) (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
      ∀ A : Matrix ι ι R, Aᴴ = A → IsUnit A.det →
        ∃ g : Matrix ι ι R, IsUnit g.det ∧ gᴴ * A * g = 1 := by
  induction n with
  | zero =>
    intro ι _ _ hc A _ _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hc
    exact ⟨1, by simp, by ext i; exact isEmptyElim i⟩
  | succ n ih =>
    intro ι _ _ hc A hA hdet
    have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨g₁, hg₁, i, hi⟩ := unimodUnramUnique_diag hR₀ hθ A hA hdet
    set B := g₁ᴴ * A * g₁ with hBdef
    have hB : Bᴴ = B := by simp [hBdef, conjTranspose_mul, hA, Matrix.mul_assoc]
    have hBdet : IsUnit B.det := by
      rw [hBdef, det_mul, det_mul, det_conjTranspose]; exact (hg₁.star.mul hdet).mul hg₁
    let κ := {j // j ≠ i}
    have hκ : Fintype.card κ = n := by
      have := Fintype.card_subtype_compl (fun j => j = i)
      simp only [Fintype.card_subtype_eq, hc] at this
      simpa [κ] using this
    let e : Unit ⊕ κ ≃ ι :=
      { toFun := Sum.elim (fun _ => i) Subtype.val
        invFun := fun j => if h : j = i then Sum.inl () else Sum.inr ⟨j, h⟩
        left_inv := by
          rintro (⟨⟩ | ⟨j, hj⟩)
          · simp
          · simp [hj]
        right_inv := by intro j; by_cases h : j = i <;> simp [h] }
    have hB' : (B.submatrix e e)ᴴ = B.submatrix e e := by rw [conjTranspose_submatrix, hB]
    have hB'det : IsUnit (B.submatrix e e).det := by rw [det_submatrix_equiv_self]; exact hBdet
    have hB'1 : B.submatrix e e (Sum.inl ()) (Sum.inl ()) = 1 := hi
    obtain ⟨g₂, hg₂, hg₂e⟩ := unimodUnramUnique_block (ih κ hκ) _ hB' hB'det hB'1
    refine ⟨g₁ * g₂.submatrix e.symm e.symm, ?_, ?_⟩
    · rw [det_mul, det_submatrix_equiv_self]; exact hg₁.mul hg₂
    · have := unimodUnramUnique_transport e B g₂ hg₂e
      rw [← this, hBdef]; simp [conjTranspose_mul, Matrix.mul_assoc]

end Herm

theorem unimodUnramUnique : UnimodUnramUnique := by
  intro R _ σ hσ R₀ hR₀ _ _ hθ n A hA hdet
  obtain ⟨θ, hθ⟩ := hθ
  let _ : StarRing R :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := fun a b => map_add σ a b }
  have hR₀' : ∀ x, x ∈ R₀ ↔ star x = x := hR₀
  have hA' : Aᴴ = A := hA
  obtain ⟨g, hg, hgA⟩ := unimodUnramUnique_main hR₀' hθ n (Fin n) (by simp) A hA' hdet
  exact ⟨g, hg, hgA⟩

end Formalism.HermitianLatticesTheory
