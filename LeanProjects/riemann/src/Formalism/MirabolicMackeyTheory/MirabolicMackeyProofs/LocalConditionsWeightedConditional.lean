import Formalism.MirabolicMackeyTheory.StatementLoc
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.GlobalBoundRefinements
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues Formalism.HermitianLatticesTheory

section Gen

def lenQ {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (X Y : Submodule R W) : ℕ :=
  (Module.length R (↥X ⧸ Y.comap X.subtype)).toNat

theorem locLen_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {A A' C C' : Submodule R W} (hA : localization₂ p A = localization₂ p A') (hC : localization₂ p C = localization₂ p C') :
    locLen p A C = locLen p A' C' := by
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [hA, hC]

private theorem mem_localization_iff_exists_smul_mem {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

private theorem locP_locP' {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (A : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.localization₂ p A) = Formalism.HermitianLatticesTheory.localization₂ p A := by
  ext x
  rw [mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [mem_localization_iff_exists_smul_mem] at h
    obtain ⟨t, ht, h⟩ := h
    exact ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact h⟩
  · intro hx
    exact ⟨1, p.primeCompl.one_mem, by rw [one_smul, mem_localization_iff_exists_smul_mem]; exact hx⟩

private theorem locP_inf' {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (A B : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ p (A ⊓ B) = Formalism.HermitianLatticesTheory.localization₂ p A ⊓ Formalism.HermitianLatticesTheory.localization₂ p B := by
  ext x
  rw [Submodule.mem_inf, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [Submodule.mem_inf] at h
    exact ⟨⟨s, hs, h.1⟩, ⟨s, hs, h.2⟩⟩
  · rintro ⟨⟨s, hs, h1⟩, ⟨t, ht, h2⟩⟩
    refine ⟨t * s, p.primeCompl.mul_mem ht hs, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [mul_smul]
      exact A.smul_mem t h1
    · rw [mul_comm, mul_smul]
      exact B.smul_mem s h2

theorem lidx_locP {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (A B : Submodule R W) : lidx p A B = lidx p (localization₂ p A) (localization₂ p B) := by
  have e1 := locP_locP' p A
  have e3 := locP_locP' p B
  have e2 : Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.localization₂ p A ⊓ Formalism.HermitianLatticesTheory.localization₂ p B) = Formalism.HermitianLatticesTheory.localization₂ p (A ⊓ B) := by
    rw [locP_inf', locP_locP', locP_locP', locP_inf']
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [locLen_congr p e1.symm e2.symm, locLen_congr p e3.symm e2.symm]

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem lix_locP {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] (w : HeightOneSpectrum (𝓞 K))
    (A B : Submodule (𝓞 K) Z) :
    lix w A B = lix w (localization₂ w.asIdeal A) (localization₂ w.asIdeal B) := by
  unfold lix
  exact lidx_locP _ A B

theorem locP {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
    (w : HeightOneSpectrum (𝓞 K)) (A X₃ X₄ : Submodule (𝓞 K) Z)
    (h : localization₂ w.asIdeal X₃ ≤ localization₂ w.asIdeal X₄) :
    lix w A (X₃ ⊓ X₄) = lix w A X₃ := by
  rw [lix_locP w A (X₃ ⊓ X₄), lix_locP w A X₃, locP_inf', inf_eq_left.mpr h]

end Gen

theorem local_conditions_weighted_at_place : LocalConditionsWeightedAtPlace := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ X₃ hM hTh1 hTh hThK h1le hle hFG hEig
    hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 X _ _ _ _ θ' eX pr Mt hc hpr h4 h34 ε hTW d φ hinj hrng
    Mj Tj hMj hTj
  exact local_conditions_weighted K Z w P ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ
    (X₃ ⊓ (Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K)))
    hM hTh1 hTh hThK h1le hle hFG hEig hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J
    (idxRules_inf_lat h3 h4) X θ' eX pr Mt hc hpr h4 inf_le_right ε
    (by rw [locP w _ _ _ h34]; exact hTW) d φ hinj hrng Mj Tj hMj hTj

section Instance

variable (K : Type) [Field K] [NumberField K] [StarRing K]

end Instance

end Formalism.EigenvalueLevelCeiling
