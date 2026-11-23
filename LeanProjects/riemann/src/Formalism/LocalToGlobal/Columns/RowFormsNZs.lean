import Mathlib
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Columns.CoefCol
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
import Formalism.LocalToGlobal.Columns.RowFormsNZp
import Formalism.LocalToGlobal.Columns.RowFormsNZa

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Pt

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} [NeZero n]
  {SG : Finset (HeightOneSpectrum (𝓞 E))}

def nzPt (a : GLG E n SG) : DecoSet E n ∅ SG := ((1 : UF E n), a) • DecoSet.base E n ∅ SG

theorem nz_base_be (w : SG) (x : Fin n → 𝓞 E) :
    (Deco.base E n ∅ SG).be w (fun i => algebraMap (𝓞 E) E (x i)) = fun i => Ideal.Quotient.mk w.1.asIdeal (x i) := by
  have h1 : (fun i => algebraMap (𝓞 E) E (x i) : Sp E n) ∈ stdLat E n := (mem_stdLat _).2 fun i => ⟨x i, rfl⟩
  simp only [Deco.base]
  rw [if_pos (le_locP _ _ h1)]
  funext i
  rw [reduction_coe]

theorem nzPt_N (a : GLG E n SG) : (nzPt a).1.N = stdLat E n := by
  show gmap (1 : Sp E n ≃ₗ[E] Sp E n) (stdLat E n) = stdLat E n
  ext x
  rw [mem_gmap]
  rfl

theorem nzPt_be (a : GLG E n SG) (w : SG) (x : Sp E n) :
    (nzPt a).1.be w x = (a w).1.mulVec ((Deco.base E n ∅ SG).be w x) := rfl

theorem nz_stab (a : GLG E n SG) (γ : UF E n) (h : GLG E n SG) (e : (γ, h) • nzPt a = nzPt a) :
    ∃ G : Matrix (Fin n) (Fin n) (𝓞 E), (∀ i j, algebraMap (𝓞 E) E (G i j) = γ.1 (Pi.single j 1) i) ∧
      ∀ w, (h w).1 * (a w).1 = (a w).1 * G.map (Ideal.Quotient.mk w.1.asIdeal) := by
  have eN : gmap γ.1 (nzPt a).1.N = (nzPt a).1.N := congrArg (fun d : DecoSet E n ∅ SG => d.1.N) e
  rw [nzPt_N] at eN
  have hmem : ∀ j, γ.1 (Pi.single j 1) ∈ stdLat E n := by
    intro j
    rw [← eN, mem_gmap, LinearEquiv.symm_apply_apply]
    have := single_mem_stdLat (E := E) (n := n) j 1
    rwa [map_one] at this
  choose G hG using fun j => (mem_stdLat _).1 (hmem j)
  refine ⟨Matrix.of fun i j => G j i, fun i j => hG j i, fun w => ?_⟩
  have eB : ∀ x, (h w).1.mulVec ((nzPt a).1.be w (γ.1.symm x)) = (nzPt a).1.be w x := fun x =>
    congrFun (congrFun (congrArg (fun d : DecoSet E n ∅ SG => d.1.be) e) w) x
  ext i j
  have h1 := congrFun (eB (γ.1 (Pi.single j 1))) i
  rw [LinearEquiv.symm_apply_apply, nzPt_be, nzPt_be] at h1
  have h2 : (Pi.single j 1 : Sp E n) = fun i => algebraMap (𝓞 E) E ((Pi.single j 1 : Fin n → 𝓞 E) i) := by
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have h3 : γ.1 (Pi.single j 1) = fun i => algebraMap (𝓞 E) E (G j i) := funext fun i => (hG j i).symm
  rw [h3, nz_base_be, h2, nz_base_be, Matrix.mulVec_mulVec] at h1
  have h4 : (fun i => Ideal.Quotient.mk w.1.asIdeal ((Pi.single j 1 : Fin n → 𝓞 E) i)) =
      (Pi.single j 1 : Fin n → 𝓞 E ⧸ w.1.asIdeal) := by
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [h4, Matrix.mulVec_single_one] at h1
  rw [Matrix.col_apply] at h1
  rw [h1, Matrix.mul_apply]
  rfl

theorem nz_unitary (γ : UF E n) (G : Matrix (Fin n) (Fin n) (𝓞 E))
    (hG : ∀ i j, algebraMap (𝓞 E) E (G i j) = γ.1 (Pi.single j 1) i) (j k : Fin n) :
    ∑ i, star (algebraMap (𝓞 E) E (G i j)) * algebraMap (𝓞 E) E (G i k) = if j = k then 1 else 0 := by
  have h1 := γ.2 (Pi.single j 1) (Pi.single k 1)
  rw [hStd_apply, hStd_single_left] at h1
  simp only [hG]
  rw [h1, Pi.single_apply]

theorem nz_ufGL_apply (γ : UF E n) (i j : Fin n) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = γ.1 (Pi.single j 1) i := by
  show (LinearMap.toMatrix' ((γ.1 : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n)) i j = _
  rw [LinearMap.toMatrix'_apply]
  congr 2

end Pt

section Comb

variable {n : ℕ}

theorem mul_pM_apply (R : Type) [CommRing R] (M : Matrix (Fin n) (Fin n) R) (s : Equiv.Perm (Fin n)) (i j : Fin n) :
    (M * pM R s) i j = M i (s j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
  · rw [pM_apply, if_pos rfl, mul_one]
  · intro b _ hb
    rw [pM_apply, if_neg hb, mul_zero]
  · simp

theorem pM_mul_apply (R : Type) [CommRing R] (M : Matrix (Fin n) (Fin n) R) (s : Equiv.Perm (Fin n)) (i j : Fin n) :
    (pM R s * M) i j = M (s⁻¹ i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (s⁻¹ i)]
  · rw [pM_apply, if_pos (by simp), one_mul]
  · intro b _ hb
    rw [pM_apply, if_neg (fun h => hb (by rw [h]; simp)), zero_mul]
  · simp

theorem nz_perm_of_le {φ : Fin n → ℕ} (s : Equiv.Perm (Fin n)) (h : ∀ b, φ (s b) ≤ φ b) (b : Fin n) : φ (s b) = φ b :=
  (Finset.sum_eq_sum_iff_of_le (fun b _ => h b)).mp (Equiv.sum_comp s φ) b (Finset.mem_univ b)

theorem nz_fine {r : ℕ} {bl : List ℕ} (s : Equiv.Perm (Fin n)) (h : ∀ b : Fin n, fine r bl (s b).val = fine r bl b.val) :
    (∀ b : Fin n, b.val < r → s b = b) ∧ ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val := by
  have key : ∀ b : Fin n, (b.val < r → s b = b) ∧ coarse r bl (s b).val = coarse r bl b.val := by
    intro b
    have hb := h b
    unfold fine at hb
    by_cases h1 : b.val < r
    · rw [if_pos h1] at hb
      by_cases h2 : (s b).val < r
      · rw [if_pos h2] at hb
        have : s b = b := Fin.ext hb
        exact ⟨fun _ => this, by rw [this]⟩
      · rw [if_neg h2] at hb
        omega
    · rw [if_neg h1] at hb
      by_cases h2 : (s b).val < r
      · rw [if_pos h2] at hb
        omega
      · rw [if_neg h2] at hb
        refine ⟨fun h => absurd h h1, ?_⟩
        rw [coarse_of_le (Nat.not_lt.mp h2), coarse_of_le (Nat.not_lt.mp h1)]
        omega
  exact ⟨fun b => (key b).1, fun b => (key b).2⟩

theorem nz_uni {κ : Type} [CommRing κ] {r : ℕ} {bl : List ℕ} (s : Equiv.Perm (Fin n)) (u : Fin n → κ) (hu : ∀ b, u b ≠ 0)
    (M : GL (Fin n) κ) (hM : ∀ a b, M.1 a b = if a = s b then u b else 0) (hm : M ∈ uniUT n κ r bl) :
    (∀ b : Fin n, b.val < r → s b = b) ∧ (∀ b : Fin n, b.val < r → u b = 1) ∧
      ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val := by
  have h1 : ∀ b : Fin n, fine r bl (s b).val ≤ fine r bl b.val := by
    intro b
    by_contra hc
    have := mem_btG.mp hm.1 (s b) b (Nat.not_le.mp hc)
    rw [hM, if_pos rfl] at this
    exact hu b this
  obtain ⟨h2, h3⟩ := nz_fine s (nz_perm_of_le (φ := fun b => fine r bl b.val) s h1)
  refine ⟨h2, fun b hb => ?_, h3⟩
  have := hm.2 b hb
  rwa [hM, if_pos (h2 b hb).symm] at this

theorem nz_ge_of_fix {r : ℕ} (s : Equiv.Perm (Fin n)) (hfix : ∀ b : Fin n, b.val < r → s b = b) (b : Fin n) :
    r ≤ (s b).val ↔ r ≤ b.val := by
  constructor
  · intro h
    by_contra hc
    rw [hfix b (Nat.not_le.mp hc)] at h
    exact hc h
  · intro h
    by_contra hc
    have := hfix (s b) (Nat.not_le.mp hc)
    rw [s.injective this] at hc
    exact hc h

theorem nz_fix_inv {r : ℕ} (s : Equiv.Perm (Fin n)) (hfix : ∀ b : Fin n, b.val < r → s b = b) (b : Fin n) (hb : b.val < r) :
    s⁻¹ b = b := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact (hfix b hb).symm

variable (κ : Type) [CommRing κ]

def nzN (n r : ℕ) (i0 : Fin n) : Matrix (Fin n) (Fin n) κ := Matrix.of fun a b => if r ≤ a.val ∧ b = i0 then 1 else 0

theorem nzN_apply {r : ℕ} (i0 a b : Fin n) : nzN κ n r i0 a b = if r ≤ a.val ∧ b = i0 then 1 else 0 := rfl

theorem nzN_mul {r : ℕ} (i0 : Fin n) (M : Matrix (Fin n) (Fin n) κ) (a c : Fin n) :
    (nzN κ n r i0 * M) a c = if r ≤ a.val then M i0 c else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i0]
  · rw [nzN_apply]
    by_cases h : r ≤ a.val
    · rw [if_pos ⟨h, rfl⟩, if_pos h, one_mul]
    · rw [if_neg (fun hh => h hh.1), if_neg h, zero_mul]
  · intro b _ hb
    rw [nzN_apply, if_neg (fun hh => hb hh.2), zero_mul]
  · simp

theorem nz_mono_mul_nzN {r : ℕ} (i0 : Fin n) (s : Equiv.Perm (Fin n)) (u : Fin n → κ) (M : Matrix (Fin n) (Fin n) κ)
    (hM : ∀ a b, M a b = if a = s b then u b else 0) (a c : Fin n) :
    (M * nzN κ n r i0) a c = if r ≤ (s⁻¹ a).val ∧ c = i0 then u (s⁻¹ a) else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (s⁻¹ a)]
  · rw [hM, if_pos (by simp), nzN_apply]
    split_ifs <;> simp
  · intro b _ hb
    rw [hM, if_neg (fun h => hb (by rw [h]; simp)), zero_mul]
  · simp

theorem nzN_sq {r : ℕ} (i0 : Fin n) (hi : i0.val < r) : nzN κ n r i0 * nzN κ n r i0 = 0 := by
  ext a c
  have h0 : nzN κ n r i0 i0 c = 0 := by
    rw [nzN_apply]
    exact if_neg (fun h => absurd h.1 (Nat.not_le.mpr hi))
  rw [nzN_mul, h0]
  simp

def nzA {r : ℕ} (i0 : Fin n) (hi : i0.val < r) : GL (Fin n) κ where
  val := 1 + nzN κ n r i0
  inv := 1 - nzN κ n r i0
  val_inv := by
    have : (1 + nzN κ n r i0) * (1 - nzN κ n r i0) = 1 - nzN κ n r i0 * nzN κ n r i0 := by noncomm_ring
    rw [this, nzN_sq κ i0 hi, sub_zero]
  inv_val := by
    have : (1 - nzN κ n r i0) * (1 + nzN κ n r i0) = 1 - nzN κ n r i0 * nzN κ n r i0 := by noncomm_ring
    rw [this, nzN_sq κ i0 hi, sub_zero]

variable {κ}

theorem permutation_scalars_eq_one {r : ℕ} {bl : List ℕ} (i0 : Fin n) (hi : i0.val < r) (s : Equiv.Perm (Fin n)) (u : Fin n → κ)
    (hfix : ∀ b : Fin n, b.val < r → s b = b) (hu0 : u i0 = 1) (M : Matrix (Fin n) (Fin n) κ)
    (hM : ∀ a b, M a b = if a = s b then u b else 0) (h : GL (Fin n) κ) (hh : h ∈ blockUT n κ r bl)
    (e : (nzA κ i0 hi).1 * h.1 = M * (nzA κ i0 hi).1) (b : Fin n) (hb : r ≤ b.val) : u b = 1 := by
  have e' : ∀ a c, h.1 a c + (if r ≤ a.val then h.1 i0 c else 0) =
      M a c + if r ≤ (s⁻¹ a).val ∧ c = i0 then u (s⁻¹ a) else 0 := by
    intro a c
    have := congrFun (congrFun e a) c
    change ((1 + nzN κ n r i0) * h.1) a c = (M * (1 + nzN κ n r i0)) a c at this
    rw [add_mul, mul_add, one_mul, mul_one, Matrix.add_apply, Matrix.add_apply, nzN_mul,
      nz_mono_mul_nzN κ i0 s u M hM] at this
    exact this
  have h1 := e' i0 i0
  rw [if_neg (Nat.not_le.mpr hi), nz_fix_inv s hfix i0 hi, if_neg (fun hh => absurd hh.1 (Nat.not_le.mpr hi)), hM,
    if_pos (hfix i0 hi).symm, hu0, add_zero, add_zero] at h1
  have h2 := e' (s b) i0
  have hsb : r ≤ (s b).val := (nz_ge_of_fix s hfix b).mpr hb
  have h3 : h.1 (s b) i0 = 0 := by
    apply mem_btG.mp hh
    rw [coarse_of_lt hi, coarse_of_le hsb]
    omega
  have h4 : s⁻¹ (s b) = b := by simp
  have h5 : s b ≠ s i0 := fun hc => by
    have := s.injective hc
    rw [this] at hb
    omega
  rw [if_pos hsb, h3, h1, h4, if_pos ⟨hb, rfl⟩, hM, if_neg h5, zero_add, zero_add] at h2
  exact h2.symm

theorem nz_comm {r : ℕ} (i0 : Fin n) (hi : i0.val < r) (s : Equiv.Perm (Fin n))
    (hfix : ∀ b : Fin n, b.val < r → s b = b) : permGL κ s * nzA κ i0 hi = nzA κ i0 hi * permGL κ s := by
  apply Units.ext
  show pM κ s * (1 + nzN κ n r i0) = (1 + nzN κ n r i0) * pM κ s
  rw [mul_add, add_mul, mul_one, one_mul]
  congr 1
  ext a c
  rw [nzN_mul, nz_mono_mul_nzN κ i0 s (fun _ => 1) (pM κ s) (fun a b => pM_apply κ s a b), pM_apply]
  have h1 : r ≤ (s⁻¹ a).val ↔ r ≤ a.val := by
    have := nz_ge_of_fix s hfix (s⁻¹ a)
    rw [show s (s⁻¹ a) = a by simp] at this
    exact this.symm
  have h2 : i0 = s c ↔ c = i0 := by
    constructor
    · intro h
      have h3 := hfix i0 hi
      rw [h] at h3
      have := s.injective h3
      rw [h, this]
    · intro h
      rw [h, hfix i0 hi]
  by_cases ha : r ≤ a.val
  · by_cases hc : c = i0
    · rw [if_pos ⟨h1.mpr ha, hc⟩, if_pos ha, if_pos (h2.mpr hc)]
    · rw [if_neg (fun h => hc h.2), if_pos ha, if_neg (fun h => hc (h2.mp h))]
  · rw [if_neg (fun h => ha (h1.mp h.1)), if_neg ha]

end Comb

section Stab

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem nz_monomial (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (G : Matrix (Fin n) (Fin n) (𝓞 E))
    (hU : ∀ j k, ∑ i, star (algebraMap (𝓞 E) E (G i j)) * algebraMap (𝓞 E) E (G i k) = if j = k then 1 else 0) :
    ∃ s : Equiv.Perm (Fin n), (∀ j, star ((G (s j) j : 𝓞 E) : E) * ((G (s j) j : 𝓞 E) : E) = 1) ∧
      ∀ i j, i ≠ s j → G i j = 0 := by
  have h1 : ∀ j, ∃ i, star ((G i j : 𝓞 E) : E) * ((G i j : 𝓞 E) : E) = 1 ∧ ∀ i', i' ≠ i → G i' j = 0 := fun j =>
    nz_mono hconj (fun i => G i j) (by
      have := hU j j
      rw [if_pos rfl] at this
      exact this)
  choose s0 hs1 hs2 using h1
  have hinj : Function.Injective s0 := by
    intro j k hjk
    by_contra hne
    have h2 := hU j k
    rw [if_neg hne, Finset.sum_eq_single (s0 j)] at h2
    · have h3 : algebraMap (𝓞 E) E (G (s0 j) j) ≠ 0 := by
        intro h0
        have := hs1 j
        change star (algebraMap (𝓞 E) E (G (s0 j) j)) * algebraMap (𝓞 E) E (G (s0 j) j) = 1 at this
        rw [h0, mul_zero] at this
        exact zero_ne_one this
      have h4 : algebraMap (𝓞 E) E (G (s0 j) k) ≠ 0 := by
        intro h0
        have := hs1 k
        rw [← hjk] at this
        change star (algebraMap (𝓞 E) E (G (s0 j) k)) * algebraMap (𝓞 E) E (G (s0 j) k) = 1 at this
        rw [h0, mul_zero] at this
        exact zero_ne_one this
      exact mul_ne_zero (star_ne_zero.mpr h3) h4 h2
    · intro i _ hi
      rw [hs2 j i hi, map_zero, star_zero, zero_mul]
    · simp
  exact ⟨Equiv.ofBijective s0 (Finite.injective_iff_bijective.mp hinj), hs1, fun i j hij => hs2 j i hij⟩

end Stab

section Main

variable {X : Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))}

open Classical in

def nzFr (pos : Equiv.Perm (Fin n)) {r : ℕ} (i0 : Fin n) (hi : i0.val < r) (w1 : SG) : GLG X.E n SG := fun w =>
  if w = w1 then (nzA _ i0 hi)⁻¹ * permGL _ pos⁻¹ else permGL _ pos⁻¹

theorem nz_stab_perm (hX : X.Ok) (pos : Equiv.Perm (Fin n)) {r : ℕ} (bl : List ℕ) (i0 : Fin n) (hi : i0.val < r)
    (w1 w2 : SG) (hne : w2 ≠ w1) {g1 g2 : ℕ} (hg1 : g1.Prime) (hg2 : g2.Prime)
    (hgw1 : (g1 : 𝓞 X.E) ∈ w1.1.asIdeal) (hgw2 : (g2 : 𝓞 X.E) ∈ w2.1.asIdeal) (hb1 : 2 * X.f + 1 < g1)
    (hb2 : 2 * X.f + 1 < g2) (γ : UF X.E n) (h : GLG X.E n SG) (h2 : h w2 ∈ uniUT n _ r bl)
    (h1 : h w1 ∈ blockUT n _ r bl) (e : (γ, h) • nzPt (nzFr pos i0 hi w1) = nzPt (nzFr pos i0 hi w1)) :
    ∃ s : Equiv.Perm (Fin n), (∀ b : Fin n, b.val < r → s b = b) ∧
      (∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) ∧
      ufGL X.E n γ = permGL X.E (pos * s * pos⁻¹) ∧ ∀ w, h w = permGL _ s := by
  obtain ⟨G, hG, hh⟩ := nz_stab _ γ h e
  obtain ⟨s0, hs1, hs2⟩ := nz_monomial hX.conjE G (nz_unitary γ G hG)
  set s : Equiv.Perm (Fin n) := pos⁻¹ * s0 * pos with hs
  have hsa : ∀ a b : Fin n, a = s b ↔ pos a = s0 (pos b) := by
    intro a b
    rw [hs, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.eq_inv_iff_eq]
  set z : Fin n → 𝓞 X.E := fun b => G (s0 (pos b)) (pos b) with hz
  have hzu : ∀ b, star ((z b : 𝓞 X.E) : X.E) * ((z b : 𝓞 X.E) : X.E) = 1 := fun b => hs1 (pos b)
  have hGz : ∀ a b, G (pos a) (pos b) = if a = s b then z b else 0 := by
    intro a b
    by_cases hab : a = s b
    · rw [if_pos hab, hz]
      show G (pos a) (pos b) = G (s0 (pos b)) (pos b)
      rw [(hsa a b).mp hab]
    · rw [if_neg hab]
      exact hs2 _ _ fun hc => hab ((hsa a b).mpr hc)

  let Gh : ∀ w : SG, GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal) := fun w =>
    permGL _ pos⁻¹ * ((nzFr pos i0 hi w1 w)⁻¹ * h w * nzFr pos i0 hi w1 w) * (permGL _ pos⁻¹)⁻¹
  have hGh : ∀ (w : SG) (a b : Fin n), (Gh w).1 a b = if a = s b then Ideal.Quotient.mk w.1.asIdeal (z b) else 0 := by
    intro w a b
    have e1 : ((nzFr pos i0 hi w1 w)⁻¹ * h w * nzFr pos i0 hi w1 w).1 = G.map (Ideal.Quotient.mk w.1.asIdeal) := by
      rw [mul_assoc, Units.val_mul, Units.val_mul, hh w, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    have e2 : (Gh w).1 = pM _ pos⁻¹ * G.map (Ideal.Quotient.mk w.1.asIdeal) * pM _ pos := by
      show (permGL _ pos⁻¹ * ((nzFr pos i0 hi w1 w)⁻¹ * h w * nzFr pos i0 hi w1 w) * (permGL _ pos⁻¹)⁻¹).1 = _
      rw [Units.val_mul, Units.val_mul, e1, ← map_inv, inv_inv]
      rfl
    rw [e2, mul_pM_apply, pM_mul_apply, inv_inv, Matrix.map_apply, hGz]
    split_ifs <;> simp
  have hGh2 : Gh w2 = h w2 := by
    show permGL _ pos⁻¹ * ((nzFr pos i0 hi w1 w2)⁻¹ * h w2 * nzFr pos i0 hi w1 w2) * (permGL _ pos⁻¹)⁻¹ = h w2
    have : nzFr (X := X) pos i0 hi w1 w2 = permGL _ pos⁻¹ := if_neg hne
    rw [this]
    group
  have hne0 : ∀ (w : SG) (b : Fin n), Ideal.Quotient.mk w.1.asIdeal (z b) ≠ 0 := fun w b hc =>
    nz_unit_notMem (hzu b) w.1 (Ideal.Quotient.eq_zero_iff_mem.mp hc)
  obtain ⟨hfix, hu1, hco⟩ := nz_uni s (fun b => Ideal.Quotient.mk w2.1.asIdeal (z b)) (hne0 w2) (Gh w2) (hGh w2)
    (by rw [hGh2]; exact h2)
  have hone : ∀ (w : SG) (b : Fin n), Ideal.Quotient.mk w.1.asIdeal (z b) = 1 → z b - 1 ∈ w.1.asIdeal := by
    intro w b hb
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hb, map_one, sub_self]
  have hz1 : ∀ b : Fin n, b.val < r → z b = 1 := fun b hb =>
    nz_root_one hX w2.1 hg2 hgw2 hb2 (hzu b) (hone w2 b (hu1 b hb))
  have hA : (nzA _ i0 hi) * h w1 = Gh w1 * nzA _ i0 hi := by
    show _ = permGL _ pos⁻¹ * ((nzFr pos i0 hi w1 w1)⁻¹ * h w1 * nzFr pos i0 hi w1 w1) * (permGL _ pos⁻¹)⁻¹ * _
    have : nzFr (X := X) pos i0 hi w1 w1 = (nzA _ i0 hi)⁻¹ * permGL _ pos⁻¹ := if_pos rfl
    rw [this]
    group
  have hz2 : ∀ b : Fin n, r ≤ b.val → z b = 1 := fun b hb =>
    nz_root_one hX w1.1 hg1 hgw1 hb1 (hzu b) (hone w1 b
      (permutation_scalars_eq_one (bl := bl) i0 hi s (fun b => Ideal.Quotient.mk w1.1.asIdeal (z b)) hfix (by rw [hz1 i0 hi, map_one]) (Gh w1).1
        (hGh w1) (h w1) h1 (congrArg Units.val hA) b hb))
  have hzall : ∀ b, z b = 1 := fun b => by
    by_cases hb : b.val < r
    · exact hz1 b hb
    · exact hz2 b (Nat.not_lt.mp hb)
  have hGp : ∀ w : SG, Gh w = permGL _ s := by
    intro w
    apply Units.ext
    ext a b
    rw [hGh, hzall, map_one]
    rfl
  refine ⟨s, hfix, hco, ?_, fun w => ?_⟩
  · apply Units.ext
    ext i j
    rw [nz_ufGL_apply, ← hG, permGL_val, pM_apply]
    have h3 := hGz (pos⁻¹ i) (pos⁻¹ j)
    rw [show pos (pos⁻¹ i) = i by simp, show pos (pos⁻¹ j) = j by simp, hzall] at h3
    rw [h3]
    have h4 : pos⁻¹ i = s (pos⁻¹ j) ↔ i = (pos * s * pos⁻¹) j := by
      show pos⁻¹ i = s (pos⁻¹ j) ↔ i = pos (s (pos⁻¹ j))
      exact Equiv.Perm.inv_eq_iff_eq
    by_cases h5 : pos⁻¹ i = s (pos⁻¹ j)
    · rw [if_pos h5, if_pos (h4.mp h5), map_one]
    · rw [if_neg h5, if_neg (fun hc => h5 (h4.mpr hc)), map_zero]
  · by_cases hw : w = w1
    · subst hw
      rw [hGp, nz_comm i0 hi s hfix] at hA
      exact mul_left_cancel hA
    · rw [← hGp w]
      show h w = permGL _ pos⁻¹ * ((nzFr pos i0 hi w1 w)⁻¹ * h w * nzFr pos i0 hi w1 w) * (permGL _ pos⁻¹)⁻¹
      have : nzFr (X := X) pos i0 hi w1 w = permGL _ pos⁻¹ := if_neg hw
      rw [this]
      group

end Main

end Formalism.L2.Col
