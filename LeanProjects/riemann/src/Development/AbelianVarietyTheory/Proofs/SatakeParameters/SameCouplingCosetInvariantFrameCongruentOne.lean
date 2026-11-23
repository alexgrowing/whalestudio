import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetLoc

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  unfold qOf
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact P.ne_bot

theorem intAt_qOf_pow (P : HeightOneSpectrum (𝓞 E)) (t : ℕ) : IntAt P ((qOf P : E) ^ t) := by
  simpa using IntAt.coe P ((qOf P : 𝓞 E) ^ t)

theorem congr_of_sub_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (D a k : ℕ) (hak : a + k ≤ D)
    (hg : ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (g z - z) ∈ stdAt E n P)
    (y0 x : Sp E n) (hy : ∀ l, IntAt P ((qOf P : E) ^ a * y0 l))
    (hx : ∀ l, IntAt P (((qOf P : E) ^ k)⁻¹ * (x - y0) l)) :
    ∀ l, IntAt P (((qOf P : E) ^ k)⁻¹ * (g x - y0) l) := by
  have hc : (qOf P : E) ≠ 0 := qOf_ne_zero P
  have hxa : ∀ l, IntAt P ((qOf P : E) ^ a * x l) := fun l => by
    have e : (qOf P : E) ^ a * x l = (qOf P : E) ^ a * y0 l + (qOf P : E) ^ (a + k) * (((qOf P : E) ^ k)⁻¹ * (x - y0) l) := by
      simp only [Pi.sub_apply]
      rw [pow_add]
      field_simp
      ring
    rw [e]
    exact (hy l).add ((intAt_qOf_pow P _).mul (hx l))
  have hz : (qOf P : E) ^ a • x ∈ stdAt E n P := (mem_localization_standardLattice P _).2 fun l => by simpa using hxa l
  have h1 := (mem_localization_standardLattice P _).1 (hg _ hz)
  obtain ⟨t, ht⟩ : ∃ t, D = t + (a + k) := ⟨D - (a + k), by omega⟩
  intro l
  have e : ((qOf P : E) ^ k)⁻¹ * (g x - y0) l = ((qOf P : E) ^ k)⁻¹ * (x - y0) l +
      (qOf P : E) ^ t * ((((qOf P : E) ^ D)⁻¹ • (g ((qOf P : E) ^ a • x) - (qOf P : E) ^ a • x)) l) := by
    rw [map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ht]
    simp only [pow_add]
    field_simp
    ring
  rw [e]
  exact (hx l).add ((intAt_qOf_pow P t).mul (h1 l))

theorem symm_sub_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) (D : ℕ) (hk : κ ∈ GLint E n P)
    (hg : ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ z - z) ∈ stdAt E n P) :
    ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ.symm z - z) ∈ stdAt E n P := by
  intro z hz
  have hk' : ∀ x, κ x ∈ stdAt E n P ↔ x ∈ stdAt E n P := hk
  have hz' : κ.symm z ∈ stdAt E n P := (hk' _).1 (by simpa using hz)
  have h := hg _ hz'
  rw [LinearEquiv.apply_symm_apply] at h
  have e : ((qOf P : E) ^ D)⁻¹ • (κ.symm z - z) = -(((qOf P : E) ^ D)⁻¹ • (z - κ.symm z)) := by
    rw [← smul_neg, neg_sub]
  rw [e]
  exact (stdAt E n P).neg_mem h

end Local

end GlobalTheory.CosetLoc

namespace GlobalTheory.CosetLoc

open Classical in

theorem sameCoset_symm_iff : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) {n : ℕ} (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (y0 : Sp X.E n), cst.Ok →
  κ ∈ GLint X.E n P.1 → (∀ w ∈ stdAt X.E n P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E n P.1) →
  (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) →
  (P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) * y0 l)) → (P.1 ∉ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y0 l)) →
  ∀ w, SameCoset sel mu cst P (κ.symm w) y0 ↔ SameCoset sel mu cst P w y0 := by
  intro X Pr sel S mu cst P n κ y0 hc hk hg hD hy1 hy2 w
  have hg' := symm_sub_one κ (cst.D P) hk hg

  obtain ⟨a, hak, hy⟩ : ∃ a, a + (if P.1 ∈ Pr.vGs then 0 else cst.M) ≤ cst.D P ∧ ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ a * y0 l) := by
    by_cases hP : P.1 ∈ Pr.vGs
    · refine ⟨1, ?_, fun l => by simpa using hy1 hP l⟩
      rw [if_pos hP]
      simpa using hc.D_pos P
    · refine ⟨cst.M, ?_, hy2 hP⟩
      rw [if_neg hP]
      have := hD hP
      omega
  unfold SameCoset
  constructor
  · intro h
    have := congr_of_sub_one κ (cst.D P) a _ hak hg y0 (κ.symm w) hy h
    simpa using this
  · intro h
    exact congr_of_sub_one κ.symm (cst.D P) a _ hak hg' y0 w hy h

end GlobalTheory.CosetLoc
