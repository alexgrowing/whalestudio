import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemOrth

theorem idemAt_orth {D : D7} {a b : AE D} {i j : Formalism.L2.DIV.Pl D.host.E} {n : ℕ} (ha : Formalism.L2.NTheta.IsIdemAt a i)
    (hb : Formalism.L2.NTheta.IsIdemAt b j) (hi : ((n : ℕ) : 𝓞 D.host.E) ∈ i.asIdeal)
    (hj : ((n : ℕ) : 𝓞 D.host.E) ∉ j.asIdeal) : (a + cA D a) * (b + cA D b) = 0 := by
  obtain ⟨⟨a1, a2, v, ε, hε, a3⟩, a4⟩ := ha
  obtain ⟨⟨b1, b2, v', ε', hε', b3⟩, b4⟩ := hb
  by_cases hv : v = v'
  · exfalso
    rw [← hv] at hε'
    have hab : a + cA D a = b + cA D b := a3.trans (GlobalTheory.PlaceDatum.placeIdem_eq hε hε' ▸ b3.symm)
    have hn : ((n : ℕ) : 𝓞 D.host.E) ≠ 0 := fun h => hj (h ▸ zero_mem _)
    have h1 := not_not.1 (mt (b4 _ hn).2 hj)
    have h2 := GlobalTheory.MovedIdem.finPart_conj_mem h1
    have hs : star ((((n : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹) = (((n : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹ := by
      rw [star_inv₀]
      congr 1
      exact star_natCast (R := D.host.E) n
    rw [hs] at h2
    have h3 := not_not.1 (mt (a4 1 one_ne_zero).2 ((Ideal.ne_top_iff_one _).1 i.isPrime.ne_top))
    have h4 : incA D (((1 : 𝓞 D.host.E) : D.host.E)⁻¹) = 1 := by
      rw [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one]
    rw [h4, mul_one] at h3
    have h5 := GlobalTheory.SplitLatBasis.mul_mem_intAE D h3 (add_mem h1 h2)
    rw [← RingHom.map_add, ← RingHom.map_mul, ← add_mul, ← mul_assoc, ← hab, mul_add, a1, a2, add_zero] at h5
    exact (a4 _ hn).1 hi h5
  · rw [a3, b3, ← RingHom.map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε hε' hv, RingHom.map_zero]

theorem sum_orth {R ι : Type} [CommRing R] (c : R →+* R) (p q : ι → R) (s t : Finset ι)
    (h : ∀ i ∈ s, ∀ j ∈ t, (p i + c (p i)) * (q j + c (q j)) = 0) :
    (∑ i ∈ s, p i + c (∑ i ∈ s, p i)) * (∑ j ∈ t, q j + c (∑ j ∈ t, q j)) = 0 := by
  rw [map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h i hi j hj

theorem idemSum_orth : ∀ (D : D7) (e e' : AE D) (P P' : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ), IsIdemSum e P → IsIdemSum e' P' → (∀ PP ∈ P, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ P', ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (e + cA D e) * (e' + cA D e') = 0 := by
  rintro D e e' P P' n ⟨⟨es, hes, rfl⟩, -⟩ ⟨⟨fs, hfs, rfl⟩, -⟩ hP hP'
  exact sum_orth (R := AE D) (cA D) es fs P P' fun i hi j hj =>
    idemAt_orth (hes i hi) (hfs j hj) (hP i hi) (hP' j hj)

end GlobalTheory.IdemOrth
