import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLifts

theorem prime_eq_of_mem {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (h1 : (p : 𝓞 K) ∈ P.asIdeal) (h2 : (q : 𝓞 K) ∈ P.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact P.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem places_apart {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (h : L.Is μ0) (t : T) :
    (∀ PP ∈ L.Pg, ∀ PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q t → ¬ Lev.IsConjPl PP PP') ∧ Disjoint L.Pg (L.Q t) := by
  have hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hP k hk
    obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := h.Q_pl t PP hP
    have h1 : (q : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← hc]
      exact Ideal.absNorm_mem PP.asIdeal
    exact hne k (prime_eq_of_mem PP hq (D.host.g_prime k) h1 hk)
  refine ⟨fun PP hP PP' hP' hc => ?_, Finset.disjoint_left.2 fun PP hP hP' => ?_⟩
  · rcases hP' with hP' | hP'
    · exact GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg h.Pg PP hP PP' hP' hc
    · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
      obtain ⟨c, hc', e⟩ := hc _ (L.C.P.overP hk)
      have e' : c = ((D.host.g k : ℕ) : 𝓞 D.host.E) := RingOfIntegers.ext (by rw [e]; simp)
      exact hQ PP' hP' k (e' ▸ hc')
  · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    exact hQ PP hP' k (L.C.P.overP hk)

theorem lifts_exist : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m), (∀ (t : T) (g0 : G0 R.Pg D.R.r), ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ) ∧ ∀ g0 : G0 R.Pg D.R.r, ∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h i
  obtain ⟨c, hc⟩ := h.βV i
  obtain ⟨c', hc'⟩ := h.βW i
  refine ⟨fun t => ?_, ?_⟩
  · exact GlobalTheory.ParahoricLift.liftsExist (Vc D i) (R.βV i) (R.datVt i t) _ _ hc (places_apart _ h t).1 (places_apart _ h t).2
  · refine GlobalTheory.ParahoricLift.liftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) _ _ hc' (fun PP hP PP' hP' => ?_)
      (Finset.disjoint_empty_right _)
    exact (places_apart _ h A.μ0).1 PP hP PP' (hP'.imp id fun h0 => absurd h0 (Finset.notMem_empty _))

end GlobalTheory.StepLifts
