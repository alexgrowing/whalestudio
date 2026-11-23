import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR.Links
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)

variable {D : D7}

abbrev Place (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E)

abbrev ModHost (D : D7) : Type := ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E

def conjIdeal (H : ModHost D) (I : Ideal (𝓞 D.host.E)) : Ideal (𝓞 D.host.E) :=
  I.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)

def PrimeToAA (D : D7) (P : Place D) : Prop := FractionalIdeal.count D.host.E P D.host.AA = 0

structure IsDesignLevel (P : Formalism.L2.Host.PiBar D.host) (H : ModHost D) (l : Level H) : Prop where
  root : (H.rt : D.host.E) = D.host.sqrtMinusD
  level : l.M = D.host.g 0 * D.host.g 1
  half : l.Mb = ∏ k, (P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

structure TwistGuard (D : D7) (Q : Finset (Place D)) : Prop where
  onePrime : ∀ P ∈ Q, ∀ P' ∈ Q, ∀ q : ℕ, q.Prime → (q : 𝓞 D.host.E) ∈ P.asIdeal → (q : 𝓞 D.host.E) ∈ P'.asIdeal →
    P.under (𝓞 D.host.K) = P'.under (𝓞 D.host.K)
  primeToC : ∀ P ∈ Q, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

structure IsCoverHalf {H : ModHost D} (l : Level H) (Q : Finset (Place D)) (n : ℕ) (I : Ideal (𝓞 D.host.E))
    (l₂ : Level H) : Prop where
  squarefree : Squarefree n
  primes : ∀ q : ℕ, q.Prime → (q ∣ n ↔ ∃ P ∈ Q, (q : 𝓞 D.host.E) ∈ P.asIdeal)
  coprime : Nat.Coprime n l.M
  level : l₂.M = l.M * n
  aux : l₂.A = l.A
  half : l₂.Mb = l.Mb * I
  norm : I * conjIdeal H I = Ideal.span {(n : 𝓞 D.host.E)}
  conj_coprime : I ⊔ conjIdeal H I = ⊤
  places_dvd : ∀ P ∈ Q, P.asIdeal ∣ I

def AAPrimeToLevel {H : ModHost D} (l : Level H) : Prop :=
  ∀ P : Place D, (P.asIdeal ∣ l.Mb ∨ P.asIdeal ∣ conjIdeal H l.Mb) → PrimeToAA D P

def HalvesAt {H : ModHost D} (l : Level H) (Pg Q : Finset (Place D)) : Prop :=
  l.Mb = ∏ P ∈ Pg, P.asIdeal ∧
    ∃ (n : ℕ) (I : Ideal (𝓞 D.host.E)) (l₂ : Level H), IsCoverHalf l Q n I l₂ ∧ AAPrimeToLevel l₂

def HalfOfLevelAndCover : Prop :=
  ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 →
    ∀ (H : ModHost D) (l : Level H), IsDesignLevel L.C.P H l →
      ∀ t : T, TwistGuard D (L.Q t) → HalvesAt l L.Pg (L.Q t)

def HalfOfLevelAndCoverReal : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 →
    ∀ C : Core D, LawsM C → C.pb = R.C.P.pb →
      ∀ t : T, TwistGuard D (R.Q t) → HalvesAt C.Q.l R.Pg (R.Q t)

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  intro hz
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at hz
  rcases mul_eq_zero.mp hz with h1 | h1
  · rw [FractionalIdeal.coeIdeal_eq_zero] at h1
    unfold Formalism.BasicNotions.Host.ccE at h1
    rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h1
    exact D.host.ccK_ne_bot h1
  · rw [inv_eq_zero, FractionalIdeal.coeIdeal_eq_zero] at h1
    have h2 := D.host.𝔟_spec.2
    rw [h1] at h2
    simp at h2

theorem IsCoverHalf.dvd {H : ModHost D} {l l₂ : Level H} {Q : Finset (Place D)} {n : ℕ} {I : Ideal (𝓞 D.host.E)}
    (h : IsCoverHalf l Q n I l₂) : l.Dvd l₂ := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.Dvd
  refine ⟨⟨n, h.level⟩, ?_, ?_⟩
  · rw [h.half]
    intro x hx
    exact (Submodule.mem_inf.mp (Ideal.mul_le_inf hx)).1
  · rw [h.aux]

end GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign
