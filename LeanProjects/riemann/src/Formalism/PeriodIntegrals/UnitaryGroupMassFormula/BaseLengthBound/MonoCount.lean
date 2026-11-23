import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FirstLengthLePrimeBound
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ReductionUniformizerSmulMem

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

def FiltLenGr : Prop :=
  ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (F : ℕ → Submodule R W) (a : ℕ),
    Antitone F → F 0 = ⊤ → F a = ⊥ →
    ∀ (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module R (V k)] (φ : ∀ k, ↥(F k) →ₗ[R] V k),
      (∀ k (x : ↥(F k)), φ k x = 0 → (x : W) ∈ F (k + 1)) →
      ∀ (M N : Submodule R W) (P Q : ∀ k, Submodule R (V k)), N ≤ M →
        (∀ k < a, ∀ x : ↥(F k), (x : W) ∈ M → φ k x ∈ P k) →
        (∀ k < a, ∀ v ∈ Q k, ∃ x : ↥(F k), (x : W) ∈ N ∧ φ k x = v) →
        Module.length R (↥M ⧸ N.comap M.subtype) ≤
          ∑ k ∈ Finset.range a, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype)

def MonoCount : Prop :=
  ∀ D T : ℕ, D < T →
    ∑ k ∈ Finset.range (T - D), (Finset.Nat.antidiagonalTuple D k).card = Nat.choose (T - 1) D

def LenPiU : Prop :=
  ∀ (R E V : Type) [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup V] [Module R V]
    (ι : Type) [Fintype ι] (A B : Submodule R E) (U : (ι → E) →ₗ[R] V), Function.Injective U →
    Module.length R (↥((Submodule.pi Set.univ fun _ => A).map U) ⧸
        ((Submodule.pi Set.univ fun _ => B).map U).comap ((Submodule.pi Set.univ fun _ => A).map U).subtype) =
      (Fintype.card ι : ℕ∞) * Module.length R (↥A ⧸ B.comap A.subtype)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def Fk (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (T k : ℕ) :
    Submodule (Op X la G.N) (WK X la G.w wF (a0 D j T)) :=
  Submodule.span (Op X la G.N) ((toWK X la G.w wF (a0 D j T)) ''
    ((Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) : Submodule _ _) : Set ↥(HK X la G.w wF)))

abbrev Vg (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Type :=
  Fin G.N × (Fin (WeightFamilies.dimY D j) → ℕ) → SectionSheafQuotient X la G.w wF

abbrev mon (D : D7) (j k : ℕ) : Finset (Fin (WeightFamilies.dimY D j) → ℕ) := Finset.Nat.antidiagonalTuple (WeightFamilies.dimY D j) k

def FkFilt : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (T : ℕ),
    Antitone (Fk G la T) ∧ Fk G la T 0 = ⊤ ∧ Fk G la T (a0 D j T) = ⊥

def GrBound : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ i, G.th' i ∈ B.Mlat j wF) → (∀ k, G.w k ∈ X.WWc S.sW wL) → Q.Ila ≠ ⊤ →
    ∃ (φ : ∀ k, ↥(Fk G la T k) →ₗ[Op X la G.N] Vg G la) (Pk Qk : ℕ → Submodule (Op X la G.N) (Vg G la)),
      (∀ k (x : ↥(Fk G la T k)), φ k x = 0 → (x : WK X la G.w wF (a0 D j T)) ∈ Fk G la T (k + 1)) ∧
      (∀ k < a0 D j T, ∀ x : ↥(Fk G la T k), (x : WK X la G.w wF (a0 D j T)) ∈ Q.AA T → φ k x ∈ Pk k) ∧
      (∀ k < a0 D j T, ∀ v ∈ Qk k, ∃ x : ↥(Fk G la T k),
        (x : WK X la G.w wF (a0 D j T)) ∈ firstLength_le_prime_bound G la T ⊓ Q.AA T ∧ φ k x = v) ∧
      (∀ k < a0 D j T, Module.length (Op X la G.N) (↥(Pk k) ⧸ (Qk k).comap (Pk k).subtype) ≤
        (((mon D j k).card * Q.Ila.toNat : ℕ) : ℕ∞))

end PoleLengthBounds
