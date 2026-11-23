import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLattice
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfHermEBijective
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.CompanionTheory.HermPoisson

theorem hermCocompact (D : D7) (r : ℕ) :
    ∃ K : Set (hermA D r), IsCompact K ∧ ∀ x, ∃ l ∈ ratHerm D r, x - l ∈ K := by
  obtain ⟨-, K, hK, hKx⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := r)
  refine ⟨K, hK, fun x => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hKx x
  refine ⟨-γ, neg_mem hγ, ?_⟩
  rwa [sub_neg_eq_add, add_comm]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem hermFourierZero (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (lam : Measure (hermA D r)) (hH : lam.IsAddHaarMeasure) (𝓖 : Set (hermA D r))
    (h𝓖 : IsAddFundamentalDomain (ratHerm D r) 𝓖 lam) (φ : hermA D r → ℂ) (hφ : Continuous φ)
    (hper : ∀ x, ∀ l ∈ ratHerm D r, φ (x + l) = φ x)
    (hco : ∀ β : HermE D r,
      ∫ b in 𝓖, φ b * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) ∂lam = 0) :
    ∀ x, φ x = 0 := by
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
  obtain ⟨K, hK, hc⟩ := hermCocompact D r
  intro x
  refine GlobalTheory.CompanionTheory.FourierComplete.eq_zero_of_coeffs_vanish (ratHerm D r) lam h𝓖 hK hc (T := ratHerm D r)
    (fun t b => chi ψ t.1.1 b) (fun t => continuous_chi hψ t.1.1) ?_ ?_ ?_ ?_ ?_ φ hφ hper ?_ x
  · intro t y l hl
    show chi ψ t.1.1 (y + l) = chi ψ t.1.1 y
    rw [chi_add_right, chi_rat hψ (hmem t) ⟨l, hl⟩, mul_one]
  · intro y
    exact chi_zero_left ψ y
  · intro s t y
    exact chi_add_left ψ s.1.1 t.1.1 y
  · intro t y
    show star (chi ψ t.1.1 y) = chi ψ (-t.1.1) y
    rw [chi_neg_left]
    exact star_psi' hψ _
  · intro a b hab
    refine rat_of_chi hψ (-a + b) fun t => ?_
    have h1 : chi ψ t.1.1 a * chi ψ t.1.1 (-a) = 1 := by
      rw [← chi_add_right, add_neg_cancel, chi_zero_right]
    rw [chi_add_right, ← hab t, mul_comm]
    exact h1
  · intro t
    obtain ⟨β, hβ⟩ := (ofHermE_bijective (D := D) (r := r)).2 t
    have h1 : ∀ b : hermA D r, chi ψ (-t).1.1 b =
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) := fun b => by
      show chi ψ (-t.1.1) b = _
      rw [chi_neg_left, ← hβ, ofHermE_val]
    simp only [h1]
    exact hco β

end PositivityTheory.Rg.Sw.Glob
