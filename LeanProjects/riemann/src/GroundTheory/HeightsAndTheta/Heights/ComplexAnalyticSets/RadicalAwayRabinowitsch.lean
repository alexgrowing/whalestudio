import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadicalAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {R : Type*} [CommRing R] {ι : Type*}

def rabinowitschIdeal (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    Ideal (MvPolynomial (Option ι) R) :=
  K.map (rename (R := R) some).toRingHom ⊔ Ideal.span {X none * rename some g - 1}

theorem rabinowitschIdeal_map {R' : Type*} [CommRing R'] (φ : R →+* R')
    (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    (rabinowitschIdeal K g).map (MvPolynomial.map φ) =
      rabinowitschIdeal (K.map (MvPolynomial.map φ)) (MvPolynomial.map φ g) := by
  have h : (MvPolynomial.map φ).comp (rename (R := R) (some : ι → Option ι)).toRingHom =
      (rename (R := R') (some : ι → Option ι)).toRingHom.comp (MvPolynomial.map φ) :=
    RingHom.ext fun p => by simp [map_rename]
  simp only [rabinowitschIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_map, Set.image_singleton,
    map_sub, map_mul, map_one, map_X, h]
  simp [map_rename]

theorem pow_sub_one_mem_span (g : MvPolynomial ι R) (k : ℕ) :
    (X none * rename some g) ^ k - 1 ∈
      (Ideal.span {X none * rename some g - 1} : Ideal (MvPolynomial (Option ι) R)) := by
  rw [Ideal.mem_span_singleton]
  simpa using sub_dvd_pow_sub_pow (X none * rename some g : MvPolynomial (Option ι) R) 1 k

def rabinowitschEval (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    MvPolynomial (Option ι) R →+* Localization.Away (Ideal.Quotient.mk K g) :=
  eval₂Hom ((algebraMap (MvPolynomial ι R ⧸ K) _).comp ((Ideal.Quotient.mk K).comp C))
    fun o => Option.elim o (IsLocalization.Away.invSelf (Ideal.Quotient.mk K g))
      fun i => algebraMap (MvPolynomial ι R ⧸ K) _ (Ideal.Quotient.mk K (X i))

theorem rabinowitschEval_rename (K : Ideal (MvPolynomial ι R)) (g p : MvPolynomial ι R) :
    rabinowitschEval K g (rename some p) =
      algebraMap (MvPolynomial ι R ⧸ K) _ (Ideal.Quotient.mk K p) := by
  have h : (rabinowitschEval K g).comp (rename (R := R) (some : ι → Option ι)).toRingHom =
      (algebraMap (MvPolynomial ι R ⧸ K) (Localization.Away (Ideal.Quotient.mk K g))).comp
        (Ideal.Quotient.mk K) :=
    MvPolynomial.ringHom_ext (fun r => by simp [rabinowitschEval]) (fun i => by simp [rabinowitschEval])
  exact congrArg (fun f => f p) h

theorem rabinowitschIdeal_le_ker (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    rabinowitschIdeal K g ≤ RingHom.ker (rabinowitschEval K g) := by
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    simp [RingHom.mem_ker, rabinowitschEval_rename, Ideal.Quotient.eq_zero_iff_mem.2 hp]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_one, rabinowitschEval_rename]
    rw [show rabinowitschEval K g (X none) = IsLocalization.Away.invSelf (Ideal.Quotient.mk K g) by
      simp [rabinowitschEval], mul_comm, IsLocalization.Away.mul_invSelf, sub_self]

theorem rename_mem_rabinowitschIdeal_iff (K : Ideal (MvPolynomial ι R)) (g f : MvPolynomial ι R) :
    rename some f ∈ rabinowitschIdeal K g ↔ ∃ k : ℕ, g ^ k * f ∈ K := by
  constructor
  · intro hf
    have h0 := rabinowitschIdeal_le_ker K g hf
    rw [RingHom.mem_ker, rabinowitschEval_rename,
      IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk K g))] at h0
    obtain ⟨⟨m, k, rfl⟩, hm⟩ := h0
    refine ⟨k, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simpa using hm
  · rintro ⟨k, hk⟩
    have e : (rename some f : MvPolynomial (Option ι) R) =
        X none ^ k * rename some (g ^ k * f) -
          rename some f * ((X none * rename some g) ^ k - 1) := by
      simp only [map_mul, map_pow]; ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left ?_))
      (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (pow_sub_one_mem_span g k)))
    exact Ideal.mem_map_of_mem _ hk

theorem exists_pow_mul_sub_rename_mem (g : MvPolynomial ι R) (h : MvPolynomial (Option ι) R) :
    ∃ (N : ℕ) (f : MvPolynomial ι R), rename some g ^ N * h - rename some f ∈
      (Ideal.span {X none * rename some g - 1} : Ideal (MvPolynomial (Option ι) R)) := by
  induction h using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp⟩
  | add p q hp hq =>
    obtain ⟨N₁, f₁, h₁⟩ := hp
    obtain ⟨N₂, f₂, h₂⟩ := hq
    refine ⟨N₁ + N₂, g ^ N₂ * f₁ + g ^ N₁ * f₂, ?_⟩
    have e : rename some g ^ (N₁ + N₂) * (p + q) - rename some (g ^ N₂ * f₁ + g ^ N₁ * f₂) =
        rename some g ^ N₂ * (rename some g ^ N₁ * p - rename some f₁) +
          rename some g ^ N₁ * (rename some g ^ N₂ * q - rename some f₂) := by
      simp only [map_add, map_mul, map_pow]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
  | mul_X p j hp =>
    obtain ⟨N, f, hf⟩ := hp
    cases j with
    | none =>
      refine ⟨N + 1, f, ?_⟩
      have e : rename some g ^ (N + 1) * (p * X none) - rename some f =
          (rename some g ^ N * p - rename some f) +
            rename some g ^ N * p * (X none * rename some g - 1) := by ring
      rw [e]
      exact Ideal.add_mem _ hf (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    | some i =>
      refine ⟨N, f * X i, ?_⟩
      have e : rename some g ^ N * (p * X (some i)) - rename some (f * X i) =
          (rename some g ^ N * p - rename some f) * X (some i) := by
        simp only [map_mul, rename_X]; ring
      rw [e]
      exact Ideal.mul_mem_right _ _ hf

theorem isRadicalAway_iff_isRadical_rabinowitschIdeal (K : Ideal (MvPolynomial ι R))
    (g : MvPolynomial ι R) : IsRadicalAway K g ↔ (rabinowitschIdeal K g).IsRadical := by
  constructor
  · intro hK h ⟨m, hm⟩
    obtain ⟨N, f, hf⟩ := exists_pow_mul_sub_rename_mem g h
    have hf' : rename some g ^ N * h - rename some f ∈ rabinowitschIdeal K g := Ideal.mem_sup_right hf

    have hfm : rename some (f ^ m) ∈ rabinowitschIdeal K g := by
      have hd : (rename some g ^ N * h) ^ m - rename some f ^ m ∈ rabinowitschIdeal K g := by
        obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (rename some g ^ N * h) (rename some f) m
        rw [hc]
        exact Ideal.mul_mem_right _ _ hf'
      have hp : (rename some g ^ N * h) ^ m ∈ rabinowitschIdeal K g := by
        rw [mul_pow]
        exact Ideal.mul_mem_left _ _ hm
      rw [map_pow]
      simpa using Ideal.sub_mem _ hp hd
    obtain ⟨k, hk⟩ := (rename_mem_rabinowitschIdeal_iff K g _).1 hfm

    have hrad : g ^ k * f ∈ K.radical := by
      refine ⟨m + 1, ?_⟩
      have e : (g ^ k * f) ^ (m + 1) = (g ^ (k * m) * f) * (g ^ k * f ^ m) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hk
    obtain ⟨j, hj⟩ := hK _ hrad
    have hfK : rename some f ∈ rabinowitschIdeal K g :=
      (rename_mem_rabinowitschIdeal_iff K g f).2 ⟨j + k, by rw [pow_add, mul_assoc]; exact hj⟩
    have hgh : rename some g ^ N * h ∈ rabinowitschIdeal K g := by
      simpa using Ideal.add_mem _ hf' hfK
    have e : h = X none ^ N * (rename some g ^ N * h) -
        h * ((X none * rename some g) ^ N - 1) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hgh)
      (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (pow_sub_one_mem_span g N)))
  · intro hR f ⟨m, hm⟩
    have h1 : rename some f ∈ rabinowitschIdeal K g := by
      refine hR ⟨m, ?_⟩
      rw [← map_pow]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hm)
    exact (rename_mem_rabinowitschIdeal_iff K g f).1 h1

end

end GroundTheory.Heights₂.Heights
