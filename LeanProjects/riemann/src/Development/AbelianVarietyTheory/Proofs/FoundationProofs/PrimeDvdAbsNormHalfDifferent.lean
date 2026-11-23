import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.HalfNorm
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistCoverDesign
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum

noncomputable section

namespace GlobalTheory.HalfCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level Coeff Moduli)

variable {D : D7}

abbrev badInt (D : D7) : ℕ := D.host.QS * D.host.q * Ideal.absNorm D.host.ccK

theorem exists_prime_under {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ∀ N : ℕ, (N : 𝓞 K) ∈ P.asIdeal ↔ p ∣ N := by
  haveI := P.isPrime
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨ringChar (𝓞 K ⧸ P.asIdeal), CharP.char_is_prime (𝓞 K ⧸ P.asIdeal) _, fun N => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]

theorem mem_of_dvd {R : Type} [CommRing R] {J : Ideal R} {p N : ℕ} (hp : (p : R) ∈ J) (h : p ∣ N) : (N : R) ∈ J := by
  obtain ⟨c, rfl⟩ := h
  push_cast
  exact J.mul_mem_right _ hp

theorem not_mem_of_coprime {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {a b : ℕ}
    (h : Nat.Coprime a b) (hb : (b : 𝓞 K) ∈ P.asIdeal) : (a : 𝓞 K) ∉ P.asIdeal := by
  intro ha
  obtain ⟨p, hp, hP⟩ := exists_prime_under P
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h ((hP a).1 ha) ((hP b).1 hb))

theorem exists_place_of_dvd_absNorm {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (J : Ideal (𝓞 K))
    (h : p ∣ Ideal.absNorm J) : ∃ P : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ P.asIdeal ∧ P.asIdeal ∣ J := by
  obtain ⟨P, hP, hu, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp J h
  have hm : (p : 𝓞 K) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [hu]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨P, hP.isPrime, ?_⟩, hm, hd⟩
  rintro rfl
  exact hp.ne_zero (by simpa using hm)

theorem exists_place_over {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ P.asIdeal := by
  have h : p ∣ Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) := by
    rw [Ideal.absNorm_span_natCast]
    exact dvd_pow_self _ Module.finrank_pos.ne'
  exact (exists_place_of_dvd_absNorm hp _ h).imp fun _ h => h.1

theorem prime_dvd_absNorm_halfDifferent (D : D7) {p : ℕ} (hp : p.Prime) :
    p ∣ Ideal.absNorm D.host.𝔟 ↔ p ∣ D.host.QS * D.host.q :=
  D.host.prime_dvd_absNorm_half_iff hp

theorem coprime_ccK (D : D7) : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.host.QS * D.host.q) :=
  Nat.Coprime.mul_right D.host.ccK_coprimeS (D.host.ccK_coprime _ (by simp))

theorem ccE_ne_bot (D : D7) : D.host.ccE ≠ ⊥ := fun h =>
  D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)

theorem absNorm_ccK_mem {P : Place D} (h : P.asIdeal ∣ D.host.ccE) :
    ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
  rw [map_natCast] at this
  exact Ideal.le_of_dvd h this

theorem two_q_mem {P : Place D} (h : P.asIdeal ∣ D.host.𝔟) : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  obtain ⟨p, hp, hP⟩ := exists_prime_under P
  exact (hP _).2 ((prime_dvd_absNorm_halfDifferent D hp).1 ((hP _).1 (Ideal.le_of_dvd h (Ideal.absNorm_mem _))))

theorem primeToAA_iff (P : Place D) : PrimeToAA D P ↔ ¬ P.asIdeal ∣ D.host.ccE ∧ ¬ P.asIdeal ∣ D.host.𝔟 := by
  classical
  have hb := D.host.half_ne_bot
  have hc := ccE_ne_bot D
  have hnot : ¬ (P.asIdeal ∣ D.host.ccE ∧ P.asIdeal ∣ D.host.𝔟) := fun h =>
    not_mem_of_coprime P (coprime_ccK D) (two_q_mem h.2) (absNorm_ccK_mem h.1)
  unfold PrimeToAA Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  rw [FractionalIdeal.count_mul _ _ (FractionalIdeal.coeIdeal_ne_zero.2 hc)
    (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)), FractionalIdeal.count_inv,
    FractionalIdeal.count_coe _ _ hc, FractionalIdeal.count_coe _ _ hb]
  rw [← Associates.count_ne_zero_iff_dvd hc P.irreducible, ← Associates.count_ne_zero_iff_dvd hb P.irreducible] at hnot ⊢
  omega

theorem primeToAA_of_not_mem {P : Place D} (h : ((badInt D : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) : PrimeToAA D P :=
  (primeToAA_iff P).2 ⟨fun hc => h (mem_of_dvd (absNorm_ccK_mem hc) (Dvd.intro_left _ rfl)),
    fun hb => h (mem_of_dvd (two_q_mem hb) (Dvd.intro _ rfl))⟩

section Lev

variable {H : ModHost D}

def LevelClauses (l : Level H) (pd : ℕ) (I : Ideal (𝓞 D.host.E)) (l₂ : Level H) : Prop :=
  l.Dvd l₂ ∧ l₂.M = l.M * pd ∧ Nat.Coprime pd l.M ∧ l₂.Mb = l.Mb * I ∧
    I ⊔ I.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤

theorem LevelClauses.norm {l l₂ : Level H} {pd : ℕ} {I : Ideal (𝓞 D.host.E)} (h : LevelClauses l pd I l₂) :
    I * conjIdeal H I = Ideal.span {(pd : 𝓞 D.host.E)} := by
  have h2 := l₂.prod
  rw [h.2.2.2.1, h.2.1, Ideal.map_mul, mul_mul_mul_comm, l.prod, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton] at h2
  refine mul_left_cancel₀ ?_ h2
  have := l.three_le
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
  omega

theorem conj_sup_span (I : Ideal (𝓞 D.host.E)) (n : ℕ) :
    conjIdeal H (I ⊔ Ideal.span {(n : 𝓞 D.host.E)}) = conjIdeal H I ⊔ Ideal.span {(n : 𝓞 D.host.E)} := by
  rw [conjIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, conjIdeal]

theorem sup_span_norm {I : Ideal (𝓞 D.host.E)} {pd n : ℕ} (h : I * conjIdeal H I = Ideal.span {(pd : 𝓞 D.host.E)})
    (hc : I ⊔ conjIdeal H I = ⊤) (hn : n ∣ pd) :
    (I ⊔ Ideal.span {(n : 𝓞 D.host.E)}) * conjIdeal H (I ⊔ Ideal.span {(n : 𝓞 D.host.E)}) =
      Ideal.span {(n : 𝓞 D.host.E)} := by
  rw [conj_sup_span]
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, h]
    exact sup_le (sup_le (Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hn)) Ideal.mul_le_right)
      Ideal.mul_le_left
  · conv_lhs => rw [← Ideal.mul_top (Ideal.span {(n : 𝓞 D.host.E)}), ← hc, Ideal.mul_sup]
    refine sup_le ?_ (Ideal.mul_mono le_sup_right le_sup_left)
    rw [mul_comm]
    exact Ideal.mul_mono le_sup_left le_sup_right

def cutLevel {l l₂ : Level H} {pd : ℕ} {I : Ideal (𝓞 D.host.E)} (h : LevelClauses l pd I l₂) {n : ℕ} (hn : n ∣ pd) :
    Level H where
  M := l.M * n
  three_le := by
    have h3 := l₂.three_le
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [h.2.1, zero_dvd_iff.1 hn] at h3
      omega
    exact l.three_le.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn0))
  odd := l₂.odd.of_dvd_nat (by rw [h.2.1]; exact Nat.mul_dvd_mul_left _ hn)
  Mb := l.Mb * (I ⊔ Ideal.span {(n : 𝓞 D.host.E)})
  fromK := by
    refine le_antisymm ?_ (Ideal.span_le.2 fun a ha => ha.1)
    conv_lhs => rw [Ideal.mul_sup, ← h.2.2.2.1, l₂.fromK, l.fromK, Ideal.span_mul_span']
    refine sup_le (Ideal.span_mono fun a ha => ⟨?_, ha.2⟩) (Ideal.span_mono ?_)
    · have h1 := ha.1
      rw [h.2.2.2.1] at h1
      exact Ideal.mul_mono_right le_sup_left h1
    · rintro _ ⟨a, ha, b, rfl, rfl⟩
      exact ⟨Ideal.mul_mem_mul ha.1 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)),
        Subalgebra.mul_mem _ ha.2 (natCast_mem _ n)⟩
  prod := by
    have h1 := sup_span_norm h.norm h.2.2.2.2 hn
    rw [conjIdeal] at h1
    rw [Ideal.map_mul, mul_mul_mul_comm, l.prod, h1, Nat.cast_mul, Ideal.span_singleton_mul_span_singleton]
  coprime := by
    have hle : l₂.Mb ≤ l.Mb * (I ⊔ Ideal.span {(n : 𝓞 D.host.E)}) := by
      rw [h.2.2.2.1]; exact Ideal.mul_mono_right le_sup_left
    exact top_le_iff.1 (l₂.coprime.ge.trans (sup_le_sup hle (Ideal.map_mono hle)))
  A := l.A
  A_pos := l.A_pos

end Lev

def HalfAt (Pg Q : Finset (Place D)) (Mb I : Ideal (𝓞 D.host.E)) : Prop :=
  Mb = ∏ P ∈ Pg, P.asIdeal ∧ (∀ P ∈ Q, I ≤ P.asIdeal) ∧
    ∀ P, P ∈ Pg ∨ P ∈ Q → ((badInt D : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

def GuardAt (Q : Finset (Place D)) : Prop :=
  (∀ P ∈ Q, ∀ P' ∈ Q, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ P.asIdeal ∧ (p : 𝓞 D.host.E) ∈ P'.asIdeal) →
    P.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧
  ∀ P ∈ Q, ((badInt D : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

def CoverWithHalf {H : ModHost D} (l : Level H) (Pg Q : Finset (Place D)) : Prop :=
  ∃ (pd : ℕ) (I : Ideal (𝓞 D.host.E)) (l₂ : Level H), LevelClauses l pd I l₂ ∧ l₂.A = l.A ∧ HalfAt Pg Q l.Mb I

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Rec

def RowAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 →
    ∀ C : Core D, LawsM C → C.pb = R.C.P.pb → QGuard R → ∀ t : T,
      ∃ (pd : ℕ) (I : Ideal (𝓞 D.host.E)) (l₂ : Level C.Q.H),
        LevelClauses C.Q.l pd I l₂ ∧ l₂.A = C.Q.l.A ∧ HalfIs R t C.Q.l.Mb I

def RowEach : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 →
    ∀ C : Core D, LawsM C → C.pb = R.C.P.pb → ∀ t : T, GuardAt (R.Q t) →
      ∃ (pd : ℕ) (I : Ideal (𝓞 D.host.E)) (l₂ : Level C.Q.H),
        LevelClauses C.Q.l pd I l₂ ∧ l₂.A = C.Q.l.A ∧ HalfIs R t C.Q.l.Mb I

def RowChoices : Prop :=
  ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 →
    ∀ (H : ModHost D) (l : Level H), IsDesignLevel L.C.P H l →
      (∀ t, GuardAt (L.Q t)) → ∀ t : T, CoverWithHalf l L.Pg (L.Q t)

def RealAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 →
    ∀ C : Core D, LawsM C → C.pb = R.C.P.pb →
      (∀ t, TwistGuard D (R.Q t)) → ∀ t : T, HalvesAt C.Q.l R.Pg (R.Q t)

def restrict {T T' : Type} (L : LevCh D T) (f : T' → T) : LevCh D T' :=
  { L with xiH := fun t => L.xiH (f t), xi := fun t => L.xi (f t), Q := fun t => L.Q (f t), xiR := fun t => L.xiR (f t) }

end GlobalTheory.HalfCompare
