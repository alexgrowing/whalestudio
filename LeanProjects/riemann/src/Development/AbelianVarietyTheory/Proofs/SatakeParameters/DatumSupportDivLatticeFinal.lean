import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.WeightedChainData

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory.SuppTop

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_nat (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) : IntAt P (c : E) := by
  simpa using IntAt.coe P (c : 𝓞 E)

theorem intAt_sum {ι : Type} (P : HeightOneSpectrum (𝓞 E)) (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) (by simpa using intAt_nat P 0) h

theorem smul_mem_of_inFr {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    (hf : ∀ y, f y ∈ localization₂ P.asIdeal N ↔ y ∈ stdAt E a P) (hf' : ∀ y, f' y ∈ localization₂ P.asIdeal N' ↔ y ∈ stdAt E b P)
    (c : ℕ) (x : HomE E a b) (h : ∀ s l, IntAt P ((c : E) * inFr f f' x (Pi.single s 1) l)) :
    ∀ y ∈ localization₂ P.asIdeal N, (c : E) • x y ∈ localization₂ P.asIdeal N' := by
  intro y hy
  have hv : f.symm y ∈ stdAt E a P := (hf _).1 (by simpa using hy)
  have hv' : ∀ i, IntAt P (f.symm y i) := (mem_localization_standardLattice P _).1 hv
  have e : (c : E) • x y = f' ((c : E) • inFr f f' x (f.symm y)) := by simp [inFr]
  rw [e, hf']
  refine (mem_localization_standardLattice P _).2 fun l => ?_
  have e2 : inFr f f' x (f.symm y) = ∑ s, f.symm y s • inFr f f' x (Pi.single s 1) := by
    conv_lhs => rw [pi_eq_sum_univ' (f.symm y)]
    simp only [map_sum, map_smul]
  rw [e2]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine intAt_sum P _ _ fun s _ => ?_
  rw [mul_left_comm]
  exact (hv' s).mul (h s l)

theorem entB_zero {N' N : ℕ} (q k₀ c' n' n : ℕ) (hc : c' = 0) (ex' ex : ℕ → ℕ) (x : HomE E N' N) (p p' : ℕ) (hp : p < n)
    (hp' : p' < n') :
    LocE.entB q k₀ c' n' 0 n ex' ex x p p' = Loc.atN (x (Loc.eN E N' p')) p := by
  subst hc
  have h1 : ∀ m s, LocE.fIdx k₀ 0 m s = s := by
    intro m s
    unfold LocE.fIdx
    split_ifs <;> omega
  simp [LocE.entB, h1, LocE.scE, hp, hp']

end General

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem intAt_of_phiTop (sharp : Bool) (m2 : ℕ) (hm : R.m = m2 + 2) (P : HeightOneSpectrum (𝓞 X.E))
    (z : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) (hz : PhiTop Ch mu sharp m2 P z ≠ 0)
    (p p' : ℕ) (hp : p < R.N R.m - 1) (hp' : p' < R.N (m2 + 1)) :
    IntAt P (Loc.atN (z (Loc.eN X.E _ p')) p) := by
  have hc : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  have ha : p' < R.r + (R.m - 1) * R.t := by
    have : R.m - 1 = m2 + 1 := by omega
    unfold Ranks.N at hp'
    unfold Ranks.r
    rw [this]
    have : (m2 + 1) * (R.t + 1) = (m2 + 1) * R.t + (m2 + 1) := by ring
    omega
  unfold PhiTop at hz
  split_ifs at hz
  · unfold LocE.PhiGS at hz
    simp only at hz
    split_ifs at hz with h
    · have := h.1 p p' hp ha
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz
  · unfold LocE.PhiG at hz
    simp only at hz
    split_ifs at hz with h
    · have := h.1 p p' hp ha
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz
  · unfold LocE.PhiQ at hz
    split_ifs at hz with h
    · have := h.1 p p' hp (by omega)
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz

theorem intAt_of_ftY {n : ℕ} (P : rowSG Pr sel mu) (η : Sp X.E n →ₗ[X.E] X.E) (y' : Sp X.E n)
    (h : ftY sel mu cst P η y' ≠ 0) (s : Fin n) : IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single s 1)) := by
  unfold ftY at h
  split_ifs at h with h1 h2 h3
  · have := (intAt_nat P.1 (qOf P.1 ^ cst.M)).mul (h2 s)
    simpa using this
  · exact absurd rfl h
  · exact h3 s
  · exact absurd rfl h

end Chain

end GlobalTheory.SuppTop
