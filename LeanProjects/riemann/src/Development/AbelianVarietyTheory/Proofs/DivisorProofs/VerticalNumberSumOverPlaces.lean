import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfLnSymUpdateSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.LocM
open GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open GlobalTheory.PairTerm
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairTerm

theorem natCast_mem_asIdeal_of_stalk {R : Type} [CommRing R] {Z X : Scheme.{0}} (i : Z ⟶ X) (q : X ⟶ Sp R) (z : Z)
    (p : ℕ) (h : ((p : ℕ) : Z.presheaf.stalk z) = 0) : ((p : ℕ) : R) ∈ (q (i z)).asIdeal := by
  rw [← Scheme.Hom.comp_apply]
  set f := i ≫ q
  have hnu : ¬ IsUnit ((p : ℕ) : (Sp R).presheaf.stalk (f z)) := by
    intro hu
    have h2 := (isUnit_map_iff (f.stalkMap z).hom ((p : ℕ) : (Sp R).presheaf.stalk (f z))).2 hu
    rw [map_natCast, h] at h2
    exact not_isUnit_zero h2
  haveI : (f z).asIdeal.IsPrime := PrimeSpectrum.isPrime (f z)
  let e := (Spec.stalkIso (CommRingCat.of R) (f z)).commRingCatIsoToRingEquiv
  have hl : ¬ IsUnit (algebraMap R (Localization.AtPrime (f z).asIdeal) ((p : ℕ) : R)) := by
    intro hu
    apply hnu
    have h3 := hu.map e.symm
    rwa [map_natCast, map_natCast] at h3
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime (f z).asIdeal) (f z).asIdeal] at hl
  simpa [Ideal.primeCompl] using hl

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem natCast_mem_of_vertNum_ne_zero (p : ℕ) [Fact p.Prime] (V : Cover Y) (n : ℕ) (N : Fin n → HermLB V.p)
    (y : V.X) (h : vertNum p V n N y ≠ 0) : ((p : ℕ) : 𝓞 F) ∈ (V.p y).asIdeal := by
  by_cases hne : Nonempty (VertSub p V.X n y)
  · obtain ⟨S⟩ := hne
    letI := S.alg
    haveI := S.int
    have hΓ : ((p : ℕ) : Γ(S.Z, ⊤)) = 0 := by
      rw [← map_natCast (algebraMap (ZMod p) Γ(S.Z, ⊤)), ZMod.natCast_self, map_zero]
    have hs : ((p : ℕ) : S.Z.presheaf.stalk (genericPoint S.Z)) = 0 := by
      rw [← map_natCast (S.Z.presheaf.germ ⊤ (genericPoint S.Z) trivial).hom, hΓ, map_zero]
    have := natCast_mem_asIdeal_of_stalk S.i V.p (genericPoint S.Z) p hs
    rwa [S.gen] at this
  · exact absurd (by simp only [vertNum, dif_neg hne]) h

end GlobalTheory.PairTerm

namespace GlobalTheory.PairTerm

open Classical in

theorem finsum_vertNum_eq_sum_places : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (Y : Var D.what₂.LL) (V : Cover Y) (n : ℕ) (N : Fin n → HermLB V.p)
    (g : V.X → ℝ), (Function.support g).Finite →
    ∑ᶠ y, g y * vertNum p V n N y = (letI := Formalism.L2.Geo.finPl D p;
      ∑ la : Formalism.L2.Geo.PlL D p, ∑ᶠ y, if LiesOverPl V la.1 y then g y * vertNum p V n N y else 0) := by
  intro D p _ Y V n N g hg
  letI := Formalism.L2.Geo.finPl D p
  have hfin : ∀ la ∈ (Finset.univ : Finset (Formalism.L2.Geo.PlL D p)),
      Function.HasFiniteSupport fun y => if LiesOverPl V la.1 y then g y * vertNum p V n N y else 0 := by
    intro la _
    refine hg.subset fun y hy => ?_
    intro h0
    apply hy
    simp [h0]
  rw [← finsum_sum_comm Finset.univ _ hfin]
  refine finsum_congr fun y => ?_
  by_cases hc : g y * vertNum p V n N y = 0
  · simp [hc]
  have hv : vertNum p V n N y ≠ 0 := right_ne_zero_of_mul hc
  have hm := natCast_mem_of_vertNum_ne_zero p V n N y hv
  have hp0 : ((p : ℕ) : 𝓞 D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  let v : HeightOneSpectrum (𝓞 D.what₂.LL) :=
    ⟨(V.p y).asIdeal, PrimeSpectrum.isPrime _, fun hb => hp0 (by rw [hb] at hm; simpa using hm)⟩
  let la0 : Formalism.L2.Geo.PlL D p := ⟨v, hm⟩
  rw [Finset.sum_eq_single la0]
  · exact (if_pos rfl).symm
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Subtype.ext (HeightOneSpectrum.ext h.symm))
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.PairTerm
