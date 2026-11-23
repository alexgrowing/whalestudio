import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn heckePol)

namespace UpperTheory.Gal.Mod

def IsFibre {p n : ℕ} {O K : Type} [CommRing O] [Field K] [Algebra O K] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O))
    (T : Fin (n + 1) → crystallineComparison.Corr p Y) (H : HTower K) (γ : Fin (n + 1) → H.Γ) : Prop :=
  ∃ e : H.Z ⟶ Y, IsPullback e H.q g (sp (algebraMap O K)) ∧ ∀ j, ∃ u : H.Y (γ j) ⟶ (T j).Z,
    IsPullback u (H.s (γ j)) (T j).p e ∧ u ≫ (T j).r = H.t (γ j) ≫ e

def CorrOpEq : Prop := ∀ (l : ℕ) [Fact l.Prime] {S : Scheme.{0}} (c : TranscendenceTraces.Corr S S) [Etale c.p], c.w = Wt.const _ 1 →
  IsUnit (l : Γ(S, ⊤)) → ∀ T, IsCorrOp l c.p c.f T → T = DirectSum.lmap fun k : ℤ => c.opQ l k 0

def ESTot : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (p f n : ℕ), p.Prime →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ¬ IsUnit (p : O) →
  ∀ (K : Type) [Field K] [Algebra O K] (κ : Type) [Field κ] [Algebra O κ], (p : K) ≠ 0 → algebraMap O κ ϖ = 0 →
    (∀ a : κ, a ^ p ^ f = a) →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (V : ValuationSubring Ω)
    (hV : ∀ a : O, algebraMap K Ω (algebraMap O K a) ∈ V)
    (kb : Type) [Field kb] [IsAlgClosed kb] [Algebra κ kb] (r : V →+* kb), Function.Surjective r →
    (∀ a : O, r ⟨_, hV a⟩ = algebraMap κ kb (algebraMap O κ a)) → IsUnit (l : kb) →
  ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of O)) [Smooth g] [IsProper g] (T : Fin (n + 1) → crystallineComparison.Corr p Y),
    (∀ j, (T j).r ≫ g = (T j).p ≫ g) → PtId p (p ^ f) n (fn g ϖ) T →
  ∀ (H : HTower K) (γ : Fin (n + 1) → H.Γ), IsFibre g T H γ → (∀ j, ∃ A, IsCorrOp l (H.sΩ Ω (γ j)) (H.tΩ Ω (γ j)) A) →
  ∀ (σ : Ω ≃ₐ[K] Ω) (hσ : ∀ v ∈ V, σ v ∈ V),
    ((∀ v : V, r ⟨σ v, hσ v v.2⟩ = r v) → galTotRep l Ω H.q σ = 1) ∧
    ((∀ v : V, r ⟨σ v, hσ v v.2⟩ = r v ^ p ^ f) → ∑ j : Fin (n + 1), ((co (p ^ f) j : ℤ) : ℚ_[l]) •
      ((hop l H Ω (γ j) : Module.End ℚ_[l] (Htot l (sch.obj (H.geomZ Ω)))) * galTotRep l Ω H.q σ⁻¹ ^ (n - j)) = 0)

def SubqKill : Prop := ∀ (L G J : Type) [Field L] [Group G] [Fintype J] (M : Type 1) [AddCommGroup M] [Module L M]
  (ρ : Representation L G M) (U : Submodule L M) [FiniteDimensional L U] (A : J → Module.End L M) (θ c : J → L) (e : J → ℕ) (Φ : G),
  (∀ s, ∀ x ∈ U, ρ s x ∈ U) → (∀ j, ∀ x ∈ U, A j x ∈ U) → (∀ i j, ∀ x ∈ U, A i (A j x) = A j (A i x)) →
  (∀ j s, ∀ x ∈ U, A j (ρ s x) = ρ s (A j x)) → (∀ j, U ≤ (A j).maxGenEigenspace (θ j)) →
  (∀ x ∈ U, ∑ j, c j • A j ((ρ Φ ^ e j) x) = 0) →
  ∀ W₁ W₂ : Submodule L M, W₁ ≤ W₂ → W₂ ≤ U → (∀ s, ∀ x ∈ W₁, ρ s x ∈ W₁) → (∀ s, ∀ x ∈ W₂, ρ s x ∈ W₂) →
    (∀ W : Submodule L M, W₁ ≤ W → W ≤ W₂ → (∀ s, ∀ x ∈ W, ρ s x ∈ W) → W = W₁ ∨ W = W₂) →
    ∀ x ∈ W₂, ∑ j, (c j * θ j) • (ρ Φ ^ e j) x ∈ W₁

end UpperTheory.Gal.Mod

end
