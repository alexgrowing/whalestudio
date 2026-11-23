import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralEqTsumFd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EqZeroOfFourierCoefficientsVanish
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {r : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem poisson_herm : ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∀ f : hermA D r → ℂ, Continuous f → (∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ K, ‖f (b + c.1)‖ ≤ u c) → Integrable f lam ∧ (Summable (fun t : ratHerm D r => ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) → ∑' c : ratHerm D r, f c.1 = ∑' t : ratHerm D r, ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
  intro D r ψ hψ lam 𝓖 h𝓖 f hf hu
  obtain ⟨hH, hD, hD1⟩ := h𝓖
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : LocallyCompactSpace (hermA D r) :=
    (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  haveI : Countable D.host.E := GlobalTheory.CompanionTheory.FourierComplete.countable_numberField D.host.E
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  have hmem : ∀ q : ratHerm D r, q.1.1 ∈ ratMx D r r := fun q => AddSubgroup.mem_comap.1 q.2
  haveI : Countable (ratHerm D r) := by
    choose g hg using fun q : ratHerm D r => mem_ratMx.1 (hmem q)
    exact Function.Injective.countable (f := g) fun a b h =>
      Subtype.ext (Subtype.ext (by rw [← hg a, ← hg b, h]))
  haveI := hH
  obtain ⟨-, K, hK, hKx⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := r)
  let ι : ratHerm D r →+ hermA D r := (ratHerm D r).subtype
  have hι : Function.Injective ι := Subtype.val_injective
  have hr : ι.range = ratHerm D r := AddSubgroup.range_subtype _
  have hD' : IsAddFundamentalDomain ι.range 𝓖 lam := by
    rw [hr]
    exact hD
  have hc : ∀ x : hermA D r, ∃ l ∈ ratHerm D r, x - l ∈ K := fun x => by
    obtain ⟨γ, hγ, h⟩ := hKx x
    refine ⟨-γ, neg_mem hγ, ?_⟩
    rwa [sub_neg_eq_add, add_comm]
  have hx : ∀ x : hermA D r, ∃ a, x - ι a ∈ K := fun x => by
    obtain ⟨l, hl, h⟩ := hc x
    exact ⟨⟨l, hl⟩, h⟩
  let Eh : ratHerm D r → hermA D r → ℂ := fun t b => chi ψ t.1.1 b
  have hEc : ∀ t, Continuous (Eh t) := fun t => continuous_chi hψ t.1.1
  have hEn : ∀ t b, ‖Eh t b‖ = 1 := fun t b => hψ.2.1 _
  have hEp : ∀ t x c, Eh t (x + ι c) = Eh t x := fun t x c => by
    show chi ψ t.1.1 (x + c.1) = chi ψ t.1.1 x
    rw [chi_add_right, chi_rat hψ (hmem t) c, mul_one]
  have hE0 : ∀ t, Eh t 0 = 1 := fun t => chi_zero_right ψ t.1.1
  have hself : ∀ t x, Eh t x * Eh (-t) x = 1 := fun t x => by
    show chi ψ t.1.1 x * chi ψ (-t.1.1) x = 1
    rw [← chi_add_left, add_neg_cancel, chi_zero_left]
  have horth : ∀ s t, t ≠ s → ∫ x in 𝓖, Eh t x * Eh (-s) x ∂lam = 0 := fun s t hts => by
    obtain ⟨a, ha⟩ := exists_chi_ne hψ (t - s) (sub_ne_zero.2 hts)
    have hm : t.1.1 + -s.1.1 = (t - s).1.1 := by
      rw [← sub_eq_add_neg]
      rfl
    have he : ∀ x, Eh t x * Eh (-s) x = chi ψ (t - s).1.1 x := fun x => by
      rw [← hm, chi_add_left]
      rfl
    simp only [he]
    exact Formalism.IndefR.Tow.fd_setIntegral_char_eq_zero hD (a := a)
      (fun x y => chi_add_right ψ _ x y) (fun g hg => chi_rat hψ (hmem (t - s)) ⟨g, hg⟩) ha
  have hcomp : ∀ g : hermA D r → ℂ, Continuous g → (∀ x c, g (x + ι c) = g x) →
      (∀ t, ∫ b in 𝓖, g b * Eh (-t) b ∂lam = 0) → ∀ x, g x = 0 := fun g hg hp hz x => by
    refine GlobalTheory.CompanionTheory.FourierComplete.eq_zero_of_coeffs_vanish (ratHerm D r) lam hD hK hc (T := ratHerm D r)
      Eh hEc (fun t x l hl => hEp t x ⟨l, hl⟩) (fun y => chi_zero_left ψ y) (fun s t y => chi_add_left ψ _ _ y)
      (fun t y => ?_) (fun a b hab => ?_) g hg (fun y l hl => hp y ⟨l, hl⟩) hz x
    · show star (ψ _) = chi ψ (-t.1.1) y
      rw [star_psi' hψ, chi_neg_left]
    · refine rat_of_chi hψ _ fun t => ?_
      have h1 := chi_add_right ψ t.1.1 (-a) b
      have h2 := chi_add_right ψ t.1.1 (-a) a
      rw [neg_add_cancel, chi_zero_right] at h2
      have h3 : chi ψ t.1.1 a = chi ψ t.1.1 b := hab t
      rw [h1, ← h3, ← h2]
  have hu' : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable ι f := hu
  have main := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.poisson_gen (V := hermA D r) (C := ratHerm D r) (ι := ι) hι
    (μ := lam) hD' hD1 hK hx (E := Eh) hEc hEn hEp hE0 hself horth hcomp hf hu'
  have hneg : ∀ (t : ratHerm D r) b, Eh (-t) b =
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) := fun t b => chi_neg_left ψ t.1.1 b
  simp only [hneg] at main
  exact main

end GlobalTheory.CompanionTheory.HermPoisson
