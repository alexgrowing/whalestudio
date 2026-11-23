import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalCharacter
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HarmTop
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.ClozelCohomologicalOf

noncomputable section

open NumberField Matrix MeasureTheory Finset
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GKCoh GlobalTheory.WigAlg
open PositivityTheory.Rg.BcB (thetaA)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open scoped InnerProductSpace ComplexConjugate Classical

namespace UpperTheory.V.Z.GSp4Splitting

abbrev Un (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

section Abs

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def isoSp (σ : Un n →* (V →ₗ[ℂ] V)) (E : KMod n) : Submodule ℂ V := ⨆ t : invA σ E, LinearMap.range t.1

def IsAvg [MeasurableSpace (Un n)] (ν : Measure (Un n)) (σ : Un n →* (V →ₗ[ℂ] V)) (E : KMod n) (T : E.V →L[ℂ] E.V)
    (P : Module.End ℂ V) : Prop :=
  ∀ v w : V, ⟪w, P v⟫_ℂ =
    ∫ κ, LinearMap.trace ℂ E.V ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) * ⟪w, σ κ v⟫_ℂ ∂ν

structure IsK (σ : Un n →* (V →ₗ[ℂ] V)) : Prop where
  iso : ∀ k (x y : V), ⟪σ k x, σ k y⟫_ℂ = ⟪x, y⟫_ℂ
  fin : ∀ v : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ v ∈ S ∧ ∀ k, ∀ w ∈ S, σ k w ∈ S
  cont : ∀ v w : V, Continuous fun k => ⟪w, σ k v⟫_ℂ

structure IsLoc (χ : Inf n) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Un n →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V) : Prop where
  pair : IsPair E1 E2
  ch1 : ∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (χ true) m • x
  ch2 : ∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (χ false) m • x
  der : IsDerivK σ (kF E1 E2)
  isK : IsK σ
  Asq : A * A = 1
  Aiso : ∀ x y : V, ⟪A x, A y⟫_ℂ = ⟪x, y⟫_ℂ
  Aσ : ∀ k, A * σ k = σ k * A
  AE : ∀ a b, A * E1 a b = E2 a b * A

def AdjComm (σ : Un n →* (V →ₗ[ℂ] V)) (B : Module.End ℂ V) : Prop :=
  ∃ B' : Module.End ℂ V, (∀ x y, ⟪B x, y⟫_ℂ = ⟪x, B' y⟫_ℂ) ∧ ∀ k, B * σ k = σ k * B ∧ B' * σ k = σ k * B'

end Abs

def MultiFac : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : Type) [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F] [Nontrivial F]
    (𝔞 : ι → Subalgebra ℂ (Module.End ℂ F)) (Θ : Module.End ℂ F),
    (∀ i j, i ≠ j → ∀ a ∈ 𝔞 i, ∀ b ∈ 𝔞 j, Commute a b) →
    (∀ W : Submodule ℂ F, (∀ i, ∀ a ∈ 𝔞 i, ∀ x ∈ W, a x ∈ W) → W = ⊥ ∨ W = ⊤) →
    Θ * Θ = 1 → (∀ i, ∀ a ∈ 𝔞 i, Θ * a * Θ ∈ 𝔞 i) →
    ∃ (Fi : ι → Submodule ℂ F) (s : ℂ), (s = 1 ∨ s = -1) ∧
      (∀ i, Fi i ≠ ⊥ ∧ (∀ a ∈ 𝔞 i, ∀ x ∈ Fi i, a x ∈ Fi i) ∧ (∀ x ∈ Fi i, Θ x ∈ Fi i) ∧
        ∀ W ≤ Fi i, (∀ a ∈ 𝔞 i, ∀ x ∈ W, a x ∈ W) → W = ⊥ ∨ W = Fi i) ∧
      ∀ a : ι → Module.End ℂ F, (∀ i, a i ∈ 𝔞 i) →
        LinearMap.trace ℂ F (((univ : Finset ι).toList.map a).prod * Θ) = s * ∏ i, trOn (Fi i) (a i * Θ)

def LieStab : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Un n →* (V →ₗ[ℂ] V))
    (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf → ∀ N : Submodule ℂ V, (∀ a b, ∀ x ∈ N, Kf a b x ∈ N) →
      ∀ k, ∀ x ∈ N, σ k x ∈ N

def ProjEx : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Un n →* (V →ₗ[ℂ] V)), IsK σ → ∀ E : KMod n,
    ∃ e : Module.End ℂ V, (∀ x y, ⟪e x, y⟫_ℂ = ⟪x, e y⟫_ℂ) ∧ (∀ x, e x ∈ isoSp σ E) ∧ (∀ x ∈ isoSp σ E, e x = x) ∧
      (∀ k, e * σ k = σ k * e) ∧ (∀ B, AdjComm σ B → e * B = B * e) ∧
      ∀ N : Submodule ℂ V, (∀ k, ∀ x ∈ N, σ k x ∈ N) → ∀ x ∈ N, e x ∈ N

def AvgEx : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (σ : Un n →* (V →ₗ[ℂ] V)), IsK σ → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), ∃ P, IsAvg ν σ E T P

def AvgFacts : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (σ : Un n →* (V →ₗ[ℂ] V)), IsK σ → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V) (P : Module.End ℂ V),
    (∀ k, T * E.ρ k = E.ρ k * T) → IsAvg ν σ E T P →
      (∀ x, P x ∈ isoSp σ E) ∧ AdjComm σ P ∧ (∀ B, AdjComm σ B → P * B = B * P) ∧
      (∀ N : Submodule ℂ V, (∀ k, ∀ x ∈ N, σ k x ∈ N) → ∀ x ∈ N, P x ∈ N) ∧
      ∃ P' : Module.End ℂ V, (∀ x y, ⟪P x, y⟫_ℂ = ⟪x, P' y⟫_ℂ) ∧ ∀ B, AdjComm σ B → P' * B = B * P'

def AvgTr : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure], ν Set.univ = 1 →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Un n →* (V →ₗ[ℂ] V)), IsK σ →
    ∀ (E : KMod n) (T : E.V →L[ℂ] E.V) (P A : Module.End ℂ V), (∀ k, T * E.ρ k = E.ρ k * T) → IsAvg ν σ E T P →
      (∀ k, A * σ k = σ k * A) → FiniteDimensional ℂ (isoSp σ E) →
      FiniteDimensional ℂ (invA σ E) ∧ (isoSp σ E ≠ ⊥ → invA σ E ≠ ⊥) ∧
        trOn (isoSp σ E) (P * A) = trOn (invA σ E) (flipA E A T)

def OnePlace : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    ∀ [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure], ν Set.univ = 1 →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
      (σ : Un n →* (V →ₗ[ℂ] V)) (A P : Module.End ℂ V), IsLoc (infOf lam) E1 E2 σ A → IsAvg ν σ E T P →
      ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → S ≠ ⊥ → S ≤ isoSp σ E → (∀ x ∈ S, A x ∈ S) →
        (∀ a ∈ alg E1 E2, ∀ x ∈ S, a x ∈ isoSp σ E → a x ∈ S) →
        (∀ x ∈ S, ∀ y ∈ S, x ≠ 0 → ∃ a ∈ alg E1 E2, a x = y) →
        trOn S (P * A) = 2 ^ n ∨ trOn S (P * A) = -2 ^ n

def AbsGlob : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (lam : ι → Fin n → ℤ), (∀ i, Antitone (lam i)) → ∀ (E : ι → KMod n)
    (T : ∀ i, (E i).V →L[ℂ] (E i).V), (∀ i, IsLefK (lam i) (E i) (T i)) →
    ∀ [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure], ν Set.univ = 1 →
    ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (E1 E2 : ι → Fin n → Fin n → Module.End ℂ U)
      (σ : ι → Un n →* (U →ₗ[ℂ] U)) (Θ : Module.End ℂ U) (P : ι → Module.End ℂ U) (J : Type) (R : J → Module.End ℂ U),
      (∀ i, IsLoc (infOf (lam i)) (E1 i) (E2 i) (σ i) Θ) → (∀ i, IsAvg ν (σ i) (E i) (T i) (P i)) →
      (∀ i j, i ≠ j → ∀ a b, (∀ c d, Commute (E1 i a b) (E1 j c d) ∧ Commute (E1 i a b) (E2 j c d) ∧ Commute (E2 i a b) (E2 j c d)) ∧
        ∀ k, Commute (E1 i a b) (σ j k) ∧ Commute (E2 i a b) (σ j k)) →
      (∀ i j, i ≠ j → ∀ k k', σ i k * σ j k' = σ j k' * σ i k) →
      (∀ j i, (∀ a b, Commute (R j) (E1 i a b) ∧ Commute (R j) (E2 i a b)) ∧ ∀ k, Commute (R j) (σ i k)) →
      (∀ j, ∃ j', ∀ x y, ⟪R j x, y⟫_ℂ = ⟪x, R j' y⟫_ℂ) → (∀ j, ∃ j', Θ * R j = R j' * Θ) → Θ * Θ = 1 →
      (∀ W : Submodule ℂ U, (∀ i a b, ∀ x ∈ W, E1 i a b x ∈ W ∧ E2 i a b x ∈ W) → (∀ j, ∀ x ∈ W, R j x ∈ W) → W = ⊥ ∨ W = ⊤) →
      Nontrivial U → FiniteDimensional ℂ (⨅ i, isoSp (σ i) (E i) : Submodule ℂ U) → (∀ i, isoSp (σ i) (E i) ≠ ⊥) →
      ∃ (Y : Submodule ℂ U) (c : ℂ), c ≠ 0 ∧ FiniteDimensional ℂ Y ∧ Y ≠ ⊥ ∧ (∀ j, ∀ y ∈ Y, R j y ∈ Y) ∧ (∀ y ∈ Y, Θ y ∈ Y) ∧
        (∀ W ≤ Y, (∀ j, ∀ y ∈ W, R j y ∈ W) → W = ⊥ ∨ W = Y) ∧
        (∀ x, ((univ : Finset ι).toList.map P).prod x ∈ (⨅ i, isoSp (σ i) (E i) : Submodule ℂ U)) ∧
        ∀ j, trOn (⨅ i, isoSp (σ i) (E i)) (((univ : Finset ι).toList.map P).prod * R j * Θ) = c * trOn Y (R j * Θ)

def DiracP : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Un n →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V), IsLoc (infOf lam) E1 E2 σ A →
      ∀ ν : Fin n → ℝ, hwSp E1 E2 ν ≠ ⊥ → LSq lam ≤ spinSq ν

def LowIso : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
      (σ : Un n →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V), IsLoc (infOf lam) E1 E2 σ A →
      (∃ ν : Fin n → ℝ, hwSp E1 E2 ν ≠ ⊥ ∧ inCone (fun a => (a : ℕ)) (m0 lam - ν)) → isoSp σ E ≠ ⊥

section Conc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def IsPet (π : CuspSub E n) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) : Prop :=
  (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) ∧ (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) ∧
  (∀ (X : Lie E n) φ ψ, H (lieOp π X φ) ψ + H φ (lieOp π X ψ) = 0) ∧
  (∀ (g : GA E n) (φ ψ φ' ψ' : π.V), (∀ x, φ'.1.1 x = φ.1.1 (x * g)) → (∀ x, ψ'.1.1 x = ψ.1.1 (x * g)) → H φ' ψ' = H φ ψ) ∧
  ∀ φ ψ φ' ψ' : π.V, (∀ x, φ'.1.1 x = φ.1.1 (thetaA E n x)) → (∀ x, ψ'.1.1 x = ψ.1.1 (thetaA E n x)) → H φ' ψ' = H φ ψ

structure Rl (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) [MeasurableSpace (GL (Fin n) (Af E))]
    (μf : Measure (GL (Fin n) (Af E))) : Type 1 where
  U : Type
  [nacg : NormedAddCommGroup U]
  [ips : InnerProductSpace ℂ U]
  i : U →ₗ[ℂ] π.V
  inj : Function.Injective i
  rng : ∀ ψ : π.V, (∃ u, i u = ψ) ↔ ∀ k ∈ K, finRep E n k ψ.1 = ψ.1
  H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ
  pet : IsPet π H
  inner_eq : ∀ x y : U, ⟪x, y⟫_ℂ = H (i x) (i y)
  E1 : InfinitePlace E → Fin n → Fin n → Module.End ℂ U
  E2 : InfinitePlace E → Fin n → Fin n → Module.End ℂ U
  σ : InfinitePlace E → Un n →* (U →ₗ[ℂ] U)
  Θ : Module.End ℂ U
  R : {h : GL (Fin n) (Af E) → ℂ // IsHeckeF K h} → Module.End ℂ U
  hE1 : ∀ w a b u, (i (E1 w a b u)).1 = eopW w true a b (i u).1
  hE2 : ∀ w a b u, (i (E2 w a b u)).1 = -eopW w false b a (i u).1
  hσ : ∀ w k u g, (i (σ w k u)).1.1 g = along w g (i u).1.1 k.1
  hΘ : ∀ u g, (i (Θ u)).1.1 g = (i u).1.1 (thetaA E n g)
  hR : ∀ h u, (i (R h u)).1.1 = heckeOp μf h.1 (i u).1.1

attribute [instance] Rl.nacg Rl.ips

end Conc

def PetEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, ThetaFix π →
  ∃ H, IsPet π H

def HeckeMem : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n)
  (K : Subgroup (GL (Fin n) (Af E))), IsOpen (K : Set (GL (Fin n) (Af E))) → IsCompact (K : Set (GL (Fin n) (Af E))) →
  ∀ [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))] (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure],
    ∀ h, IsHeckeF K h → ∀ ψ : π.V, ∃ (s : Finset (GL (Fin n) (Af E))) (c : GL (Fin n) (Af E) → ℂ) (ψ' : π.V),
      ψ'.1 = ∑ g ∈ s, c g • finRep E n g ψ.1 ∧ ψ'.1.1 = heckeOp μf h ψ.1.1 ∧ ∀ k ∈ K, finRep E n k ψ'.1 = ψ'.1

def ForRl (P : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E)))
    [MeasurableSpace (GL (Fin n) (Af E))] (μf : Measure (GL (Fin n) (Af E))), Rl π K μf → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, ThetaFix π →
    ∀ K : Subgroup (GL (Fin n) (Af E)), IsOpen (K : Set (GL (Fin n) (Af E))) → IsCompact (K : Set (GL (Fin n) (Af E))) →
    (∀ k ∈ K, thetaF E n k ∈ K) → ∀ [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
      (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (D : Rl π K μf), P E n π K μf D

def ChAt {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : CuspSub E n) (w : InfinitePlace E) (lam : Fin n → ℤ) : Prop :=
  HasInfCharGL π.V w.embedding (Multiset.map (infOf lam true) Finset.univ.val) ∧
    HasInfCharGL π.V (ComplexEmbedding.conjugate w.embedding) (Multiset.map (infOf lam false) Finset.univ.val)

def RlEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, ThetaFix π →
  ∀ K : Subgroup (GL (Fin n) (Af E)), IsOpen (K : Set (GL (Fin n) (Af E))) → IsCompact (K : Set (GL (Fin n) (Af E))) →
    (∀ k ∈ K, thetaF E n k ∈ K) → ∀ [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
      (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure], Nonempty (Rl π K μf)

def RlPair : Prop := ForRl fun _ _ _ _ _ _ _ _ _ D => ∀ w, IsPair (D.E1 w) (D.E2 w)

def RlChar : Prop := ForRl fun _ _ _ _ _ π _ _ _ D => ∀ w lam, ChAt π w lam →
  (∀ m x, gelA (D.E1 w) m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x) ∧
    ∀ m x, gelA (barF (D.E2 w)) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x

def RlK : Prop := ForRl fun _ _ _ _ _ _ _ _ _ D => ∀ w, IsK (D.σ w) ∧ IsDerivK (D.σ w) (kF (D.E1 w) (D.E2 w))

def RlTheta : Prop := ForRl fun _ _ _ _ _ _ _ _ _ D => D.Θ * D.Θ = 1 ∧ (∀ x y, ⟪D.Θ x, D.Θ y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
  ∀ w, (∀ k, D.Θ * D.σ w k = D.σ w k * D.Θ) ∧ ∀ a b, D.Θ * D.E1 w a b = D.E2 w a b * D.Θ

def RlComm : Prop := ForRl fun _ _ _ _ _ _ _ _ _ D =>
  (∀ i j, i ≠ j → ∀ a b, (∀ c d, Commute (D.E1 i a b) (D.E1 j c d) ∧ Commute (D.E1 i a b) (D.E2 j c d) ∧ Commute (D.E2 i a b) (D.E2 j c d)) ∧
    ∀ k, Commute (D.E1 i a b) (D.σ j k) ∧ Commute (D.E2 i a b) (D.σ j k)) ∧
  (∀ i j, i ≠ j → ∀ k k', D.σ i k * D.σ j k' = D.σ j k' * D.σ i k) ∧
  ∀ h i, (∀ a b, Commute (D.R h) (D.E1 i a b) ∧ Commute (D.R h) (D.E2 i a b)) ∧ ∀ k, Commute (D.R h) (D.σ i k)

def RlHecke : Prop := ForRl fun E _ _ _ n _ _ _ _ D => (∀ h, ∃ h', ∀ x y, ⟪D.R h x, y⟫_ℂ = ⟪x, D.R h' y⟫_ℂ) ∧
  ∀ h, ∃ h', h'.1 = (fun g => h.1 (thetaF E n g)) ∧ D.Θ * D.R h = D.R h' * D.Θ

def RlSimple : Prop := ForRl fun _ _ _ _ _ _ _ _ _ D => ∀ W : Submodule ℂ D.U,
  (∀ i a b, ∀ x ∈ W, D.E1 i a b x ∈ W ∧ D.E2 i a b x ∈ W) → (∀ h, ∀ x ∈ W, D.R h x ∈ W) → W = ⊥ ∨ W = ⊤

def RlFin : Prop := ForRl fun E _ _ _ n _ _ _ _ D => ∀ M : InfinitePlace E → KMod n,
  FiniteDimensional ℂ (⨅ w, isoSp (D.σ w) (M w) : Submodule ℂ D.U)

def LowType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg →
  ∀ w lam, Antitone lam → ChAt π w lam → ∃ (ν : Fin n → ℝ) (ψ : Sm E n), ψ ∈ π.V ∧ ψ ≠ 0 ∧
    Formalism.REAL.KHighest (fun _ => true) (fun a b => eopW w true a b - eopW w false b a) ν ψ ∧ inCone (fun a => (a : ℕ)) (m0 lam - ν)

def RlLow : Prop := ForRl fun _ _ _ _ n π _ _ _ D => (CG.mk π).IsRegAlg → Nontrivial D.U → ∀ w lam, Antitone lam → ChAt π w lam →
  ∃ ν : Fin n → ℝ, hwSp (D.E1 w) (D.E2 w) ν ≠ ⊥ ∧ inCone (fun a => (a : ℕ)) (m0 lam - ν)

def LocAct : Prop := ForRl fun _ _ _ _ n π _ _ _ D => ∀ w lam, ChAt π w lam →
  ∀ [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure], ν Set.univ = 1 →
  ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μC : Measure (G n)) [μC.IsHaarMeasure] (M : KMod n) (T : M.V →L[ℂ] M.V)
    (P : Module.End ℂ D.U), IsAvg ν (D.σ w) M T P → ∀ k val T', IsMult μC M k val T' → ∀ u g,
      ∫ y : G n, phiOf M T k y * along w g (D.i u).1.1 y.val ∂μC = val (infOf lam) * (D.i (P u)).1.1 g

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH in

def OpForm : Prop := ForRl fun E _ _ _ n π K _ μf D => ∀ lam : InfinitePlace E → Fin n → ℤ, (∀ w, ChAt π w (lam w)) →
  ∀ [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure], ν Set.univ = 1 →
  ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μC : Measure (G n)) [μC.IsHaarMeasure]
    (μ : Measure (PositivityTheory.Rg.BcB.E.H E n 0)) [μ.IsHaarMeasure] (P : InfinitePlace E → Module.End ℂ D.U),
    (∀ w, IsAvg ν (D.σ w) (lefE n (lam w)) (lefT n (lam w)) (P w)) → ∃ c : ℂ, c ≠ 0 ∧
      ∀ (k : ∀ w, Mat n → ((lefE n (lam w)).V →L[ℂ] (lefE n (lam w)).V)) (val : InfinitePlace E → Inf n → ℂ) (T : InfinitePlace E → ℝ),
        (∀ w, IsMult μC (lefE n (lam w)) (k w) (val w) (T w)) → ∀ h, IsHeckeF K h → ∀ (ψ : π.V) (u : D.U),
          (D.i u).1.1 = heckeOp μf h ψ.1.1 → ∀ x, ∫ y, phiProd lam k h y * ψ.1.1 (x * y.1) ∂μ =
            c * (∏ w, val w (infOf (lam w))) * (D.i (((univ : Finset (InfinitePlace E)).toList.map P).prod u)).1.1 x

end UpperTheory.V.Z.GSp4Splitting
