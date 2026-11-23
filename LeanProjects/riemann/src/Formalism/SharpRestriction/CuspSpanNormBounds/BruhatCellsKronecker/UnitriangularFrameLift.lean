import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ClauseAOfIdentityFlag

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def EqualFlagsScalar : Prop :=
  ∀ (K E : Type) [Field K] [Field E] [NumberField E] [StarRing E] [Algebra K E] (S : HSpace E) (r : ℕ) (T : E)
    (F F' : FlagG S r T), T ≠ 0 →
    (∀ x : E, algebraMap K E (Algebra.trace K E x) = x + star x) →
    (∀ j, F'.Xa j = F.Xa j) → F'.Xplus = F.Xplus → Relevant K F F' →
    ∃ c : E, c * star c = 1 ∧ (∀ a, F'.e a - c • F.e a ∈ F.Xa a.val) ∧ F'.z - c • F.z ∈ F.X

def ScalarRootOfUnity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E) (Λ : Submodule (𝓞 E) S.V)
    (F F' : LFlag S r T) (c : E), StarConj E →
    F'.fl.z ∈ Λ → (∀ d : E, d • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = d) →
    c * star c = 1 → F'.fl.z - c • F.fl.z ∈ Xsp F → F'.fl.X = F.fl.X →
    ∃ o : 𝓞 E, (o : E) = c ∧ ∃ N : ℕ, 0 < N ∧ o ^ N = 1

def ScalarCongruentOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ)
    (F F' : LFlag S r (T : E)) (o : 𝓞 E),
    Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → F.fl.z ∈ Λ → IsAdmissible Λ g F F' →
    F'.fl.z - (o : E) • F.fl.z ∈ Xsp F →
    ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → (T : 𝓞 E) ∉ P.asIdeal → o - 1 ∈ P.asIdeal

def RootsOfUnityFormal : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ζ : R) (N : ℕ) (g1 g2 : ℕ) (P1 P2 : Ideal R), 0 < N → ζ ^ N = 1 →
    g1.Prime → g2.Prime → g1 ≠ g2 → P1 ≠ ⊤ → P2 ≠ ⊤ → (g1 : R) ∈ P1 → (g2 : R) ∈ P2 → ζ - 1 ∈ P1 → ζ - 1 ∈ P2 → ζ = 1

def ExistsPrimeAbove : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ∃ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal

def UnitriangularFrameLift (D : D7) : Prop :=
  ∀ (T : D.host.E) (Λ : Submodule (𝓞 D.host.E) (hS D).V) (F F' : LFlag (hS D) D.R.rS T),
    FixedHyp D Λ F → IsLift Λ F' → IsFixedConv Λ (gS D) F' →
    (∀ a, F'.fl.e a - F.fl.e a ∈ Xflag F a.val) → F'.fl.z - F.fl.z ∈ Xsp F →
    ∃ n ∈ NLam Λ F, ∀ a, n (F.fl.e a) = F'.fl.e a

theorem id_coprime_notMem {R : Type} [CommRing R] (P : Ideal R) (hP : P ≠ ⊤) (a b : ℕ) (h : Nat.Coprime a b)
    (ha : (a : R) ∈ P) : (b : R) ∉ P := by
  intro hb
  apply hP
  rw [Ideal.eq_top_iff_one]
  have h' : ((Nat.gcd a b : ℕ) : ℤ) = (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b := Nat.gcd_eq_gcd_ab a b
  rw [Nat.Coprime.gcd_eq_one h] at h'
  have h'' : (1 : R) = (a : R) * (Nat.gcdA a b : R) + (b : R) * (Nat.gcdB a b : R) := by
    have := congrArg (fun z : ℤ => (z : R)) h'
    push_cast at this
    exact this
  rw [h'']
  exact P.add_mem (P.mul_mem_right _ ha) (P.mul_mem_right _ hb)

theorem cIdFlag_of_steps (h1 : EqualFlagsScalar) (h2 : ScalarRootOfUnity) (h3 : ScalarCongruentOne) (h4 : RootsOfUnityFormal) (h5 : ExistsPrimeAbove) {D : D7}
    (X : TermTie D) (hL : UnitriangularFrameLift D)
    (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1) : UnitaryVolumeMass.cIdFlag D X := by
  rintro u t ⟨hXa, hXp⟩ hrel
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (tie_Tu_pos D u).ne'
  obtain ⟨c, hcc, he, hz⟩ := h1 D.host.F D.host.E (hS D) D.R.rS _ (X.fl t).fl (X.fl' t).fl hT0 (tie_trace D.sp.cm)
    hXa hXp ((X.rel_iff t).1 hrel)
  have hX : (X.fl' t).fl.X = (X.fl t).fl.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa]; exact hXa _
  obtain ⟨o, ho, N, hN, hoN⟩ := h2 D.host.E (hS D) D.R.rS _ (X.abelian₂ t) (X.fl t) (X.fl' t) c (p_starConj D)
    (X.lift' t).1 (X.fixed t).2.2.2.2 hcc hz hX
  have hcong : ∀ i : Fin 2, ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      o - 1 ∈ P.asIdeal := by
    intro i P hP
    refine h3 D.host.E (hS D) D.R.rS (Tu D u) (X.abelian₂ t) (gS D) (X.fl t) (X.fl' t) o (X.fixed t).2.1
      (X.fixed t).2.2.1.1 (X.adm t) (by rw [ho]; exact hz) P ?_ ?_
    · unfold gS
      rw [Nat.cast_mul]
      fin_cases i
      · exact P.asIdeal.mul_mem_right _ hP
      · exact P.asIdeal.mul_mem_left _ hP
    · refine id_coprime_notMem P.asIdeal P.isPrime.ne_top _ _ ?_ hP
      refine (Nat.coprime_primes (D.host.g_prime i) (D.mem u).A.T_prime).2 ?_
      fin_cases i
      · exact (hTg u).1.symm
      · exact (hTg u).2.symm
  obtain ⟨P1, hP1⟩ := h5 D.host.E _ (D.host.g_prime 0)
  obtain ⟨P2, hP2⟩ := h5 D.host.E _ (D.host.g_prime 1)
  have ho1 : o = 1 := h4 (𝓞 D.host.E) o N _ _ P1.asIdeal P2.asIdeal hN hoN (D.host.g_prime 0) (D.host.g_prime 1)
    D.host.g_ne P1.isPrime.ne_top P2.isPrime.ne_top hP1 hP2 (hcong 0 P1 hP1) (hcong 1 P2 hP2)
  have hc1 : c = 1 := by rw [← ho, ho1]; rfl
  subst hc1
  simp only [one_smul] at he hz
  obtain ⟨n, hn, hne⟩ := hL _ (X.abelian₂ t) (X.fl t) (X.fl' t) (X.fixed t) (X.lift' t) (X.conv' t) he hz
  refine (X.isId_iff t).2 ⟨n, hn, hne, ?_⟩
  have hzo : (X.fl t).fl.z ∈ orth (hS D) (Xsp (X.fl t)) := by
    rw [p_mem_orth]
    exact tie_X_le_ker _ _ (X.fl t).fl.z_orth
  have h3' := hn.2.2 _ hzo
  have : n (X.fl t).fl.z - (X.fl' t).fl.z =
      (n (X.fl t).fl.z - (X.fl t).fl.z) - ((X.fl' t).fl.z - (X.fl t).fl.z) := by abel
  rw [this]
  exact Submodule.sub_mem _ h3' hz

end Formalism.MainNotions.BridgeLemma

end
