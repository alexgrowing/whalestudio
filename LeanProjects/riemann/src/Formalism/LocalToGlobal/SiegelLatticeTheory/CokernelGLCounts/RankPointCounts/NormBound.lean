import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.NormalIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

section Frac

variable (Λ : Submodule (𝓞 D.host.E) (VS D).V) (X : Submodule D.host.E (VS D).V) (y0 : (VS D).V)
  (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
  (hiso : ∀ x ∈ X, ∀ x' ∈ X, brS (VS D) x x' = 0) (horth : ∀ x ∈ X, brS (VS D) y0 x = 0)
  (hy0 : y0 ∈ Λ) (c0 : 𝓞 D.host.E) (hc0 : (c0 : D.host.E) = brS (VS D) y0 y0) (hc0ne : c0 ≠ 0)

include hy0 in
theorem one_mem_J : (1 : D.host.E) ∈ Jsub Λ X y0 := by
  change (1 : D.host.E) • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E)
  rw [one_smul]
  exact Submodule.mem_sup_left hy0

include hun hiso horth hy0 hc0 hc0ne in
theorem isFractional_J : IsFractional (nonZeroDivisors (𝓞 D.host.E)) (Jsub Λ X y0) := by
  refine ⟨c0, mem_nonZeroDivisors_of_ne_zero hc0ne, fun b hb => ?_⟩
  obtain ⟨c, hc⟩ := pair_int (Λ := Λ) (X := X) (y0 := y0) hun hiso horth hb (one_mem_J Λ X y0 hy0)
  refine ⟨c, ?_⟩
  rw [Algebra.smul_def]
  show (c : D.host.E) = (c0 : D.host.E) * b
  rw [hc, hc0]
  simp only [brS, one_smul, map_smul, smul_eq_mul]
  ring

def Jfrac : FI := ⟨Jsub Λ X y0, isFractional_J Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne⟩

theorem mem_Jfrac {l : D.host.E} : l ∈ Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne ↔ l • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E) := Iff.rfl

theorem Jfrac_ne_zero : Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne ≠ 0 := by
  intro h
  have h1 : (1 : D.host.E) ∈ Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne :=
    (mem_Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne).2 (by rw [one_smul]; exact Submodule.mem_sup_left hy0)
  rw [h, FractionalIdeal.mem_zero_iff] at h1
  exact one_ne_zero h1

theorem normZ_cO (d : 𝓞 D.host.E) :
    Algebra.norm ℤ (TorsionTotientBound.cO D.host.E d) = Algebra.norm ℤ d := by
  exact Algebra.norm_eq_of_algEquiv (TorsionTotientBound.cO D.host.E).toIntAlgEquiv d

theorem norm_bound :
    (1 : ℝ) ≤ ((FractionalIdeal.absNorm (Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne) : ℚ) : ℝ) ^ 2 *
      |((Algebra.norm ℚ (c0 : D.host.E) : ℚ) : ℝ)| := by
  classical
  have key : ∀ l ∈ Jsub Λ X y0, ∀ m ∈ Jsub Λ X y0,
      ∃ c : 𝓞 D.host.E, (c : D.host.E) = star m * l * c0 := by
    intro l hl m hm
    obtain ⟨c, hc⟩ := pair_int (Λ := Λ) (X := X) (y0 := y0) hun hiso horth hl hm
    refine ⟨c, ?_⟩
    rw [hc, hc0]
    simp only [brS, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    ring
  set J := Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne with hJ
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (c0 : D.host.E) * J ≤ 1 := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hx
    obtain ⟨c, hc⟩ := key l hl 1 (one_mem_J Λ X y0 hy0)
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨c, ?_⟩
    show (c : D.host.E) = (c0 : D.host.E) * l
    rw [hc, star_one, one_mul, mul_comm]
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hmemI : ∀ i : 𝓞 D.host.E, i ∈ I → ∃ l ∈ Jsub Λ X y0, (i : D.host.E) = c0 * l := by
    intro i hi
    have h1 : algebraMap (𝓞 D.host.E) D.host.E i ∈
        (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      FractionalIdeal.mem_coeIdeal_of_mem (S := nonZeroDivisors (𝓞 D.host.E)) hi
    rw [hI, FractionalIdeal.mem_singleton_mul] at h1
    obtain ⟨l, hl, h⟩ := h1
    exact ⟨l, hl, h⟩
  have hc0I : c0 ∈ I := by
    have h1 : (c0 : D.host.E) ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [hI, FractionalIdeal.mem_singleton_mul]
      exact ⟨1, one_mem_J Λ X y0 hy0, (mul_one _).symm⟩
    rw [FractionalIdeal.mem_coeIdeal] at h1
    obtain ⟨x', hx', hx'e⟩ := h1
    have hx'c : x' = c0 := IsFractionRing.injective (𝓞 D.host.E) D.host.E hx'e
    rw [← hx'c]
    exact hx'
  set e := TorsionTotientBound.cO D.host.E with he
  have hcoe : ∀ d : 𝓞 D.host.E, ((e d : 𝓞 D.host.E) : D.host.E) = star (d : D.host.E) := fun d => rfl
  have hA : Ideal.span {c0} * (I * Ideal.map e I) ≤ Ideal.span {c0 * e c0} := by
    rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    refine Submodule.mul_induction_on hz (fun r hr s hs => ?_) (fun a b ha hb => ?_)
    · obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv e s).1 hs
      obtain ⟨l, hl, hrl⟩ := hmemI r hr
      obtain ⟨m, hm, hxm⟩ := hmemI x hx
      obtain ⟨c, hc⟩ := key l hl m hm
      rw [Ideal.mem_span_singleton']
      refine ⟨c, IsFractionRing.injective (𝓞 D.host.E) D.host.E ?_⟩
      show ((c * (c0 * e c0) : 𝓞 D.host.E) : D.host.E) = ((c0 * (r * e x) : 𝓞 D.host.E) : D.host.E)
      push_cast
      show (c : D.host.E) * ((c0 : D.host.E) * star (c0 : D.host.E)) =
        (c0 : D.host.E) * ((r : D.host.E) * star (x : D.host.E))
      rw [hc, hrl, hxm, star_mul']
      ring
    · rw [mul_add]
      exact Ideal.add_mem _ ha hb
  have hIne : I ≠ ⊥ := by
    intro h
    rw [h] at hc0I
    exact hc0ne ((Submodule.mem_bot _).1 hc0I)
  have hNIc : Ideal.absNorm (Ideal.map e I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv I (Ideal.map e I) e rfl).toEquiv.symm
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hA
  rw [map_mul, map_mul, hNIc, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton, map_mul,
    normZ_cO, Int.natAbs_mul] at hdvd
  have hn0 : (Algebra.norm ℤ c0).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Algebra.norm_ne_zero_iff.2 hc0ne
  have ha0 : Ideal.absNorm I ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hIne
  have hna : (Algebra.norm ℤ c0).natAbs ≤ Ideal.absNorm I * Ideal.absNorm I := by
    have h1 := Nat.le_of_dvd (by positivity) hdvd
    have h2 : (Algebra.norm ℤ c0).natAbs * (Algebra.norm ℤ c0).natAbs ≤
        (Algebra.norm ℤ c0).natAbs * (Ideal.absNorm I * Ideal.absNorm I) := by
      calc _ ≤ _ := h1
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left h2 (Nat.pos_of_ne_zero hn0)
  have hJn : ((Ideal.absNorm I : ℕ) : ℚ) = |Algebra.norm ℚ (c0 : D.host.E)| * FractionalIdeal.absNorm J := by
    rw [← FractionalIdeal.coeIdeal_absNorm (K := D.host.E), hI, map_mul, FractionalIdeal.absNorm_span_singleton]
  have hq : |Algebra.norm ℚ (c0 : D.host.E)| = (((Algebra.norm ℤ c0).natAbs : ℕ) : ℚ) := by
    rw [← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs]
  set q := |Algebra.norm ℚ (c0 : D.host.E)| with hqdef
  set j := FractionalIdeal.absNorm J with hjdef
  have hqpos : 0 < q := by
    rw [hq]
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hmain : (1 : ℚ) ≤ j ^ 2 * q := by
    have h3 : (((Algebra.norm ℤ c0).natAbs : ℕ) : ℚ) ≤ ((Ideal.absNorm I : ℕ) : ℚ) * ((Ideal.absNorm I : ℕ) : ℚ) := by
      exact_mod_cast hna
    rw [← hq, hJn] at h3
    have h4 : q * 1 ≤ q * (j ^ 2 * q) := by nlinarith
    exact le_of_mul_le_mul_left h4 hqpos
  have hmainR : ((1 : ℚ) : ℝ) ≤ ((j ^ 2 * q : ℚ) : ℝ) := by exact_mod_cast hmain
  rw [hqdef] at hmainR
  push_cast at hmainR
  exact hmainR

end Frac

end Formalism.L2.SG.NGCut.NormalIntegrality
