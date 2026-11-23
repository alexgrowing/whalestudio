import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FirstLengthLePrimeBound
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Formalism.PeriodIntegrals.LengthPoleInLift

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

abbrev Mon (d k : ℕ) : Type := ↥(Finset.Nat.antidiagonalTuple d k)

def Fk (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (T k : ℕ) :
    Submodule (Op X la G.N) (WK X la G.w wF (a0 D j T)) :=
  Submodule.span (Op X la G.N) ((toWK X la G.w wF (a0 D j T)) ''
    (((Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) :
      Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) : Set ↥(HK X la G.w wF)))

abbrev Vk (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : ℕ) : Type :=
  Mon (WeightFamilies.dimY D j) k → SectionSheafQuotient X la G.w wF

def Pk (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (m : PtsG G la → ℕ) (k : ℕ) :
    Submodule (Op X la G.N) (Vk G la k) :=
  Submodule.pi Set.univ fun _ => ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + (m ζ : ℤ))

def Qk (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (k : ℕ) :
    Submodule (Op X la G.N) (Vk G la k) :=
  Submodule.pi Set.univ fun _ => Q.A0

def FiltStep : Prop :=
  ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (F : ℕ → Submodule R W) (a : ℕ),
    Antitone F → F 0 = ⊤ → F a = ⊥ →
    ∀ (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module R (V k)] (φ : ∀ k, ↥(F k) →ₗ[R] V k),
      (∀ k, ∀ x : ↥(F k), φ k x = 0 → (x : W) ∈ F (k + 1)) →
      ∀ (M N : Submodule R W) (P Q : ∀ k, Submodule R (V k)), N ≤ M →
        (∀ k < a, (M.comap (F k).subtype).map (φ k) ≤ P k) →
        (∀ k < a, Q k ≤ (N.comap (F k).subtype).map (φ k)) →
        Module.length R (↥M ⧸ N.comap M.subtype) ≤
          ∑ k ∈ Finset.range a, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype)

def MonCount : Prop :=
  ∀ d T : ℕ, d < T →
    ∑ k ∈ Finset.range (T - d), (Finset.Nat.antidiagonalTuple d k).card = Nat.choose (T - 1) d

def FiltOk (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (T : ℕ) : Prop :=
  Antitone (Fk G la T) ∧ Fk G la T 0 = ⊤ ∧ Fk G la T (a0 D j T) = ⊥

def GradedCoef (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (T : ℕ) (m : PtsG G la → ℕ) :
    Prop :=
  ∃ ψ : ∀ k, ↥(Fk G la T k) →ₗ[Op X la G.N] Vk G la k,
    (∀ k, ∀ x : ↥(Fk G la T k), ψ k x = 0 → (x : WK X la G.w wF (a0 D j T)) ∈ Fk G la T (k + 1)) ∧
    (∀ k < a0 D j T, ((Q.AAp T m).comap (Fk G la T k).subtype).map (ψ k) ≤ Pk G la Q m k) ∧
    (∀ k < a0 D j T, Qk G la Q k ≤ ((Q.AA T).comap (Fk G la T k).subtype).map (ψ k))

def PiBallLen (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (m : PtsG G la → ℕ) : Prop :=
  ∀ k, Module.length (Op X la G.N) (↥(Pk G la Q m k) ⧸ (Qk G la Q k).comap (Pk G la Q m k).subtype) =
    (((Finset.Nat.antidiagonalTuple (WeightFamilies.dimY D j) k).card * ∑ᶠ ζ, m ζ * fdeg ζ : ℕ) : ℕ∞)

def Steps : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T e : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) → Q.InLift T →
    FiltOk G la T ∧ GradedCoef G la Q T (Q.mm S T e) ∧ PiBallLen G la Q (Q.mm S T e)

end PI.PoleLengthCount
