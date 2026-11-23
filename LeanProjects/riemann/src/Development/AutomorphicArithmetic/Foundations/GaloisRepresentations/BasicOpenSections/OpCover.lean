import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.CorrOpEq

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn)

namespace UpperTheory.Gal.Mod

def IsCover {p n : ℕ} {O K : Type} [CommRing O] [Field K] [Algebra O K] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O))
    (T : Fin (n + 1) → crystallineComparison.Corr p Y) (H : HTower K) (γ : Fin (n + 1) → H.Γ) (δ : Fin (n + 1) → ℕ) : Prop :=
  ∃ e : H.Z ⟶ Y, IsPullback e H.q g (sp (algebraMap O K)) ∧ ∀ j, ∃ u : H.Y (γ j) ⟶ pullback (T j).p e,
    u ≫ pullback.snd _ _ = H.s (γ j) ∧ u ≫ pullback.fst _ _ ≫ (T j).r = H.t (γ j) ≫ e ∧ IsFinite u ∧ Etale u ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ pullback (T j).p e), (fib u x).ncard = δ j

def OpCover : Prop := ∀ (l : ℕ) [Fact l.Prime] {S S' : Scheme.{0}} (c c' : TranscendenceTraces.Corr S S') (u : c.Z ⟶ c'.Z) [IsFinite u] (δ : ℕ),
  c.w = Wt.const _ 1 → c'.w = Wt.const _ 1 → u ≫ c'.p = c.p → u ≫ c'.f = c.f → IsUnit (l : Γ(S, ⊤)) →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ c'.Z), (fib u x).ncard = δ) →
  ∀ k i : ℤ, c.opQ l k i = (δ : ℚ_[l]) • c'.opQ l k i

def ESCov : Prop :=
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
  ∀ (H : HTower K) (γ : Fin (n + 1) → H.Γ) (δ : Fin (n + 1) → ℕ), (∀ j, δ j ≠ 0) → IsCover g T H γ δ → (∀ j, ∃ A, IsCorrOp l (H.sΩ Ω (γ j)) (H.tΩ Ω (γ j)) A) →
  ∀ (σ : Ω ≃ₐ[K] Ω) (hσ : ∀ v ∈ V, σ v ∈ V),
    ((∀ v : V, r ⟨σ v, hσ v v.2⟩ = r v) → galTotRep l Ω H.q σ = 1) ∧
    ((∀ v : V, r ⟨σ v, hσ v v.2⟩ = r v ^ p ^ f) → ∑ j : Fin (n + 1), (((co (p ^ f) j : ℤ) : ℚ_[l]) / (δ j : ℚ_[l])) •
      ((hop l H Ω (γ j) : Module.End ℚ_[l] (Htot l (sch.obj (H.geomZ Ω)))) * galTotRep l Ω H.q σ⁻¹ ^ (n - j)) = 0)

end UpperTheory.Gal.Mod

end
