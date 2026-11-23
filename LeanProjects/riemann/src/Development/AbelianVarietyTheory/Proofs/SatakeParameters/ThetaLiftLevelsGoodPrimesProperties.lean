import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodPrimes

theorem isConjPl_iff {D : D7} {P P' : Pl D.host.E} : Formalism.IndefR.Lev.IsConjPl P P' ↔ P' = Formalism.DivisionValues.conjPl P := by
  constructor
  · intro h
    apply HeightOneSpectrum.ext
    refine ((Formalism.DivisionValues.conjPl P).isMaximal.eq_of_le P'.isPrime.ne_top ?_).symm
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    obtain ⟨c', h1, h2⟩ := h c hc
    have : Formalism.DivisionValues.cO _ c = c' := RingOfIntegers.ext h2.symm
    show Formalism.DivisionValues.cO _ c ∈ P'.asIdeal
    rwa [this]
  · rintro rfl
    exact fun c hc => ⟨Formalism.DivisionValues.cO _ c, Ideal.mem_map_of_mem _ hc, rfl⟩

theorem eq_or_conj_of_under_eq {D : D7} {P Q : Pl D.host.E} (h : Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) :
    Q = P ∨ Q = Formalism.DivisionValues.conjPl P := by
  have hsub : (Q.asIdeal : Set (𝓞 D.host.E)) ⊆ P.asIdeal ∪ (Formalism.DivisionValues.conjPl P).asIdeal := by
    intro x hx
    have hfix : star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E) := by
      rw [star_mul', star_star, mul_comm]
    obtain ⟨y, hy⟩ := (D.sp.cm.fixed ((x : D.host.E) * star (x : D.host.E))).1 hfix
    have hint : IsIntegral ℤ y := by
      rw [← isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective]
      have e : algebraMap D.host.F D.host.E y = ((x * Formalism.DivisionValues.cO _ x : 𝓞 D.host.E) : D.host.E) := hy
      rw [e]
      exact (x * Formalism.DivisionValues.cO _ x).isIntegral_coe
    have hn : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ = x * Formalism.DivisionValues.cO _ x := RingOfIntegers.ext hy
    have h1 : (⟨y, hint⟩ : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
      rw [hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [h] at h1
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ ∈ P.asIdeal := h1
    rw [hn] at h2
    refine (P.isPrime.mem_or_mem h2).imp id fun h3 => ?_
    have h4 : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ h3
    have e : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) = x := RingOfIntegers.ext (star_star (x : D.host.E))
    rw [e] at h4
    exact h4
  exact (Ideal.subset_union.1 hsub).imp
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h))
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (Formalism.DivisionValues.conjPl P).isPrime.ne_top h))

theorem offS_iff {D : D7} (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : Pl D.host.E) :
    OffS D S P ↔ P.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hP
    obtain ⟨x, hx, hy⟩ := h _ hP
    exact hy (algebraMap _ _ x) rfl hx
  · intro h v hv
    by_contra hc
    push Not at hc
    apply h
    have : v = P.under (𝓞 D.host.F) := by
      refine HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top fun x hx => ?_)
      obtain ⟨y, h1, h2⟩ := hc x hx
      have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x = y := RingOfIntegers.ext h1.symm
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal
      rwa [e]
    rwa [← this]

theorem good_primes : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.Q A.μ0 = ∅ ∧ (∀ t P, Good R t P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ Good R t (Formalism.DivisionValues.conjPl P) ∧ Good R A.μ0 P) ∧ (∀ SF, IsSF R SF → ∀ P, OffS D SF P ↔ Good R A.μ0 P) ∧ (R.IsFam → ∀ t, ∀ P ∈ A.ok t, Good R t (R.pl P) ∧ Formalism.DivisionValues.conjPl (R.pl P) ≠ R.pl P ∧ A.q P = Ideal.absNorm (R.pl P).asIdeal) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL
  have hQ : R.Q A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP h => ?_
    refine (hL.Q_ram A.μ0 PP).2 (Or.inl h) ?_
    rw [hL.xi_base]
    exact fun x _ => rfl
  have hcc := fun w : Pl D.host.E => Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl w
  refine ⟨hQ, fun t P hP => ⟨fun hg => ?_, fun PP h => ?_, fun PP h => ?_⟩, fun SF hSF P => ?_, fun hF t P hP => ?_⟩
  · have hk : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
      rw [Nat.cast_mul] at hg
      rcases P.isPrime.mem_or_mem hg with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨k, hk⟩ := hk
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D R.C.P k P hk with h | ⟨w', h, hw⟩
    · exact (hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩))).1 rfl
    · refine (hP w' (Or.inl ((hL.Pg w').2 ⟨k, h⟩))).2 (isConjPl_iff.2 ?_)
      rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hw
      rw [HeightOneSpectrum.ext hw, hcc]
  · obtain ⟨h1, h2⟩ := hP PP h
    rw [isConjPl_iff] at h2 ⊢
    refine ⟨fun e => h2 (by rw [e, hcc]), fun e => h1 ?_⟩
    rw [← hcc PP, ← e, hcc]
  · rw [hQ] at h
    exact hP PP (Or.inl (h.resolve_right (Finset.notMem_empty _)))
  · rw [offS_iff]
    constructor
    · intro h PP hPP
      rw [hQ] at hPP
      have hPP' := hPP.resolve_right (Finset.notMem_empty _)
      have key : PP.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) := fun e =>
        h ((hSF _).2 ⟨PP, hPP', by rw [← e]; rfl⟩)
      exact ⟨fun e => key (by rw [e]), fun e => key (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩
    · intro h hm
      obtain ⟨PP, hPP, e⟩ := (hSF _).1 hm
      obtain ⟨h1, h2⟩ := h PP (Or.inl hPP)
      have e' : P.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) := HeightOneSpectrum.ext e.symm
      rcases eq_or_conj_of_under_eq e' with h3 | h3
      · exact h1 h3.symm
      · exact h2 (isConjPl_iff.2 h3)
  · obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
    obtain ⟨h1, h2, h3⟩ := (hT.ok t P).1 hP
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at h1 h3
    refine ⟨fun PP h => ?_, fun e => h1 (by rw [e]), ?_⟩
    · have hm : PP ∈ (R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E)) :=
        h.imp (fun h => hF.Sb h) id
      refine ⟨fun e => h2 (e ▸ hm), fun hc => h3 PP hm ?_⟩
      rw [isConjPl_iff.1 hc, hcc]
    · rw [hT.q P, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.GoodPrimes
