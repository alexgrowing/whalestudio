import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.SplitDegOne

theorem exists_unique_other {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℕ) (a : ι)
    (hpos : ∀ i, 1 ≤ g i) (hsum : ∑ i, g i = 2) (ha : g a = 1) :
    ∃ b, b ≠ a ∧ g b = 1 ∧ ∀ c, c = a ∨ c = b := by
  have h1 : ∑ i ∈ Finset.univ.erase a, g i = 1 := by
    have := Finset.add_sum_erase Finset.univ g (Finset.mem_univ a)
    omega
  have hcard : (Finset.univ.erase a).card ≤ 1 := by
    have := Finset.card_nsmul_le_sum (Finset.univ.erase a) g 1 (fun i _ => hpos i)
    rw [smul_eq_mul, mul_one] at this
    exact this.trans h1.le
  have hne : (Finset.univ.erase a).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at h1
    omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.1 (le_antisymm hcard hne.card_pos)
  have hbm : b ∈ Finset.univ.erase a := hb ▸ Finset.mem_singleton_self b
  refine ⟨b, Finset.ne_of_mem_erase hbm, by rw [hb, Finset.sum_singleton] at h1; exact h1, fun c => ?_⟩
  by_cases hc : c = a
  · exact Or.inl hc
  · right
    have : c ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩
    rw [hb] at this
    exact Finset.mem_singleton.1 this

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) ∧
    (Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E)))).card = 2 ∧
    ∀ w' ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E))),
      Ideal.absNorm w'.asIdeal = Ideal.absNorm w.asIdeal ∧
        w'.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
  intro E _ _ _ w hf he
  classical
  let v := w.under (𝓞 (maximalRealSubfield E))
  have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hv0 : v.asIdeal ≠ ⊥ := v.ne_bot
  have hfw : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal w.asIdeal
    rw [hf] at this
    exact (mul_eq_one.1 this.symm).2
  have hew : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal w.asIdeal
    rw [he] at this
    exact (mul_eq_one.1 this.symm).2
  have h2 : Module.finrank (𝓞 (maximalRealSubfield E)) (𝓞 E) = 2 := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
    exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E))
      (maximalRealSubfield E) (𝓞 E) E).symm
  let _ : Fintype (v.asIdeal.primesOver (𝓞 E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rw [h2] at hsum
  let a : v.asIdeal.primesOver (𝓞 E) := ⟨w.asIdeal, w.isPrime, hwv⟩
  obtain ⟨b, hba, hb1, hall⟩ := exists_unique_other (fun q : v.asIdeal.primesOver (𝓞 E) =>
      q.1.ramificationIdx (𝓞 (maximalRealSubfield E)) * q.1.inertiaDeg (𝓞 (maximalRealSubfield E))) a
    (fun q => by
      have : q.1.IsPrime := q.2.1
      exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 _).ne'
        (Ideal.inertiaDeg_pos q.1 _).ne'))
    hsum (by simp only [a, hew, hfw, mul_one])
  have hbl : b.1.LiesOver v.asIdeal := b.2.2
  let B : HeightOneSpectrum (𝓞 E) := ⟨b.1, b.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot hv0 b.1⟩
  have hB : B.under (𝓞 (maximalRealSubfield E)) = v :=
    HeightOneSpectrum.ext (Ideal.over_def b.1 v.asIdeal).symm
  have hwB : w ≠ B := fun h => hba (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h).symm)

  have hmem : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 (maximalRealSubfield E)) = v → u = w ∨ u = B := by
    intro u hu
    have hul : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hu]; rfl⟩
    rcases hall ⟨u.asIdeal, u.isPrime, hul⟩ with h | h
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val h))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val h))
  have hB1 := mul_eq_one.1 hb1
  have hnorm : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 (maximalRealSubfield E)) = v →
      Ideal.absNorm u.asIdeal = Ideal.absNorm v.asIdeal ∧ u.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    intro u hu
    have hul : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hu]; rfl⟩
    have hf1 : u.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield E)) = 1 ∧
        u.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
      rcases hmem u hu with rfl | rfl
      · exact ⟨hfw, hew⟩
      · exact ⟨hB1.2, hB1.1⟩
    refine ⟨?_, hf1.2⟩
    rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal u.asIdeal, hf1.1, pow_one]
  refine ⟨GlobalTheory.LFun.isSplit_iff.2 ⟨w, B, hwB, rfl, hB⟩, ?_, fun u hu => ?_⟩
  · rw [Finset.card_eq_two]
    refine ⟨w, B, hwB, Finset.ext fun u => ?_⟩
    rw [GlobalTheory.LFun.mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hmem u, by rintro (rfl | rfl); exacts [rfl, hB]⟩
  · have hu' := GlobalTheory.LFun.mem_aboveF.1 hu
    exact ⟨(hnorm u hu').1.trans (hnorm w rfl).1.symm, (hnorm u hu').2⟩

end GlobalTheory.SplitDegOne
