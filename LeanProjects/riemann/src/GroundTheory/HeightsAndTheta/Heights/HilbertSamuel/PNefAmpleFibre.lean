import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefAmpleFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKleimanScheme
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

set_option linter.unusedSectionVars false

namespace NefAmpleFibreAlt

section Reduction

variable {K : Type} {ι : K → Type} (p : ℕ)

abbrev red : MRing ι →+* MRingOver (ZMod p) ι := MvPolynomial.map (Int.castRingHom (ZMod p))

theorem red_surjective : Function.Surjective (red (ι := ι) p) :=
  MvPolynomial.map_surjective _ (fun x => ZMod.intCast_surjective x)

theorem ker_red_le {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    RingHom.ker (red (ι := ι) p) ≤ J := by
  rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.span_le,
    Set.singleton_subset_iff]
  simpa using hp

theorem mem_map_red_iff {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (g : MRing ι) :
    red p g ∈ J.map (red p) ↔ g ∈ J := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (red_surjective p), sup_eq_left.mpr]
  rw [← RingHom.ker_eq_comap_bot]
  exact ker_red_le p hp

theorem ringKrullDim_red {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    ringKrullDim (MRingOver (ZMod p) ι ⧸ J.map (red p)) = ringKrullDim (MRing ι ⧸ J) := by
  have e : J = RingHom.ker ((Ideal.Quotient.mk (J.map (red p))).comp (red p)) := by
    ext g
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_map_red_iff p hp]
  exact (ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq e).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp (red_surjective p))))).symm

end Reduction

section Homog

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {R S : Type} [CommRing R] [CommRing S]

theorem map_weightedHomogeneousComponent (f : R →+* S) (w : (Σ k, ι k) → K → ℕ) (b : K → ℕ)
    (g : MRingOver R ι) :
    weightedHomogeneousComponent w b (MvPolynomial.map f g) =
      MvPolynomial.map f (weightedHomogeneousComponent w b g) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_map, coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem isMultiHomogIdeal_map (f : R →+* S) {V : Ideal (MRingOver R ι)} (hV : IsMultiHomogIdeal V) :
    IsMultiHomogIdeal (V.map (MvPolynomial.map f)) := by
  obtain ⟨T, hT, rfl⟩ := hV
  refine ⟨MvPolynomial.map f '' T, ?_, by rw [Ideal.map_span]⟩
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨a, ha⟩ := hT g hg
  exact ⟨a, fun m hm => ha m (support_map_subset _ _ hm)⟩

theorem isMultiHomogIdeal_comap (f : R →+* S) {W : Ideal (MRingOver S ι)} (hW : IsMultiHomogIdeal W) :
    IsMultiHomogIdeal (W.comap (MvPolynomial.map f)) := by
  classical
  have hW' := (Bridge.isMultiHomogIdeal_iff (R := S) W).mpr hW
  refine (Bridge.isMultiHomogIdeal_iff (R := R) _).mp fun g hg b => ?_
  rw [Ideal.mem_comap, ← map_weightedHomogeneousComponent]
  exact hW' _ hg b

end Homog

section Nef

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem nefOnF_map_red (ℓ : ℕ) [Fact ℓ.Prime] (hGeo : GeoNumStatement ι) {I : IFamily (ZMod ℓ) ι}
    (hI : IsFieldIntersection I) {P : Ideal (MRing ι)} {α : K → ℤ} (hN : NefOnFibres P α) :
    KH.NefOnF I (P.map (red ℓ)) α := by
  intro W' hW' hle
  obtain ⟨⟨hW'p, hW'h, hW'r⟩, hW'd⟩ := hW'
  set W := W'.comap (red ℓ) with hWdef
  have hmap : W.map (red ℓ) = W' := Ideal.map_comap_of_surjective _ (red_surjective ℓ) W'
  have hpW : ((ℓ : ℕ) : MRing ι) ∈ W := by
    have h0 : ((ℓ : ℕ) : MRingOver (ZMod ℓ) ι) = 0 := by
      rw [← map_natCast (C : ZMod ℓ →+* MRingOver (ZMod ℓ) ι), ZMod.natCast_self, map_zero]
    rw [hWdef, Ideal.mem_comap, map_natCast, h0]
    exact W'.zero_mem
  have hWm : IsMultiProjPrime W := by
    refine ⟨Ideal.comap_isPrime _ W', isMultiHomogIdeal_comap _ hW'h, fun k => ?_⟩
    obtain ⟨i, hi⟩ := hW'r k
    refine ⟨i, ?_⟩
    rw [hWdef, Ideal.mem_comap, map_X]
    exact hi
  have hPW : P ≤ W := Ideal.map_le_iff_le_comap.mp hle
  have hdim : ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← ringKrullDim_red ℓ hpW, hmap, hW'd]
  have hchar : charOf W ≠ 0 := by
    intro h0
    have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 := Int.natAbs_eq_zero.mp h0
    have hmem : ((ℓ : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, map_natCast]
      exact hpW
    rw [← Submodule.IsPrincipal.span_singleton_generator (W.comap (C : ℤ →+* MRing ι)), hg,
      Ideal.mem_span_singleton, zero_dvd_iff] at hmem
    exact (Fact.out : ℓ.Prime).ne_zero (by exact_mod_cast hmem)
  have hWp : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))) 1 := by
    show IsProjVarF (W.map (red ℓ)) 1
    rw [hmap]
    exact ⟨⟨hW'p, hW'h, hW'r⟩, hW'd⟩
  have h := hN W hWm hPW hchar hdim
  rw [hGeo ℓ I hI W 1 _ hWm hpW hWp] at h
  change 0 ≤ I (W.map (red ℓ)) 1 (fun _ => α) at h
  rw [hmap] at h
  convert h using 2
  funext j
  fin_cases j
  rfl

end Nef

end NefAmpleFibreAlt

open NefAmpleFibreAlt in

theorem NefAmpleFibre.proof (hK : KleimanScheme.Statement)
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    NefAmpleFibre.Statement := by
  intro K _ _ ι _ _ Ω _ y D α b a ℓ hP hN hb ha hℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨I, hI, -⟩ := hR4 (ZMod ℓ) K ι
  have e : ((b : ℤ) • α + fun _ => (a : ℤ)) = (b • α + fun _ => (a : ℤ)) := by
    rw [natCast_zsmul]
  rw [e]
  exact hK (ZMod ℓ) K ι I (fibreIdeal ℓ y) α b a hI (isMultiHomogIdeal_map _ hP.2.1.2.1)
    (nefOnF_map_red ℓ (hGeo K ι) hI hN) hb ha

end GroundTheory.Heights₂.Heights.HilbertSamuel
