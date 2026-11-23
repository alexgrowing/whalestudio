import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SpecGood
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)

namespace UpperTheory.Gal.Mod

def IsBC {p : ℕ} {Y S B : Scheme.{0}} (T : crystallineComparison.Corr p Y) (w : Wt T.Z) (s : S ⟶ Y) (bS : S ⟶ B) (c : TranscendenceTraces.Corr S S) : Prop :=
  ∃ v : c.Z ⟶ T.Z, IsPullback v c.p T.p s ∧ c.f ≫ s = v ≫ T.r ∧ c.f ≫ bS = c.p ≫ bS ∧ c.w = w.comap v

def FrobTors : Prop := ∀ (m : ℕ) [NeZero m] (X : Scheme.{0}) (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0),
  IsUnit (m : Γ(X, ⊤)) → ∀ (k : ℤ) (x : Ht m (sch.obj X) k 0), pull _ (sch.map (absFrob X p f hp h)) _ k x = x

def FrobQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0),
  IsUnit (l : Γ(X, ⊤)) → ∀ k : ℤ, pullHQ l (sch.map (absFrob X p f hp h)) k 0 = LinearMap.id

def BaseFacts : Prop := ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
  (p : O) ≠ 0 → ¬ IsUnit (p : O) → ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of O)) [Smooth g],
    LocNml Y ∧ (∀ y : Y, TranscendenceTraces.GenPt y → y ∈ Y.basicOpen (p : Γ(Y, ⊤))) ∧
    (∀ y : Y, ∃ η ∈ Y.basicOpen (p : Γ(Y, ⊤)), η ⤳ y) ∧ ∀ y ∈ Y.basicOpen (p : Γ(Y, ⊤)), y ∈ Y.basicOpen (fn g ϖ)

def DenseGen : Prop := ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
  ∀ (k : Type) [Field k] (β : O →+* k), β ϖ = 0 → ∀ (Y S : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of O)) (s : S ⟶ Y) (bS : S ⟶ gp k),
    IsPullback s bS g (sp β) → Dense {x : S | crystallineComparison.GenPt (fn g ϖ) (s x)}

def FrEx : Prop := ∀ (p f : ℕ) (hp : p.Prime) (κ kb : Type) [Field κ] [Field kb] [Algebra κ kb], (∀ a : κ, a ^ p ^ f = a) →
  ∀ (X : Scheme.{0}) (t : X ⟶ Spec (CommRingCat.of κ)) (h : (p : Γ(geom kb t, ⊤)) = 0) (τ : kb ≃ₐ[κ] kb), (∀ a, τ a = a ^ p ^ f) →
    ∃ Fr : geom kb t ⟶ geom kb t, Fr ≫ pullback.snd _ _ = pullback.snd _ _ ∧ Fr ≫ galMap kb t τ = absFrob _ p f hp h ∧
      ∀ (Ω : Type) [Field Ω] (φ : Ω →+* Ω), (∀ a, φ a = a ^ p ^ f) → ∀ x : gp Ω ⟶ geom kb t,
        x ≫ Fr ≫ pullback.fst _ _ = sp φ ≫ x ≫ pullback.fst _ _

def CorrPull : Prop := ∀ (p : ℕ) {Y S B O : Scheme.{0}} (g : Y ⟶ O) (s : S ⟶ Y) (bS : S ⟶ B) (β : B ⟶ O), IsPullback s bS g β →
  ∀ (T : crystallineComparison.Corr p Y) (w : Wt T.Z), IsWt T.p w → T.r ≫ g = T.p ≫ g → ∃ c, IsBC T w s bS c

def CorrComm : Prop := ∀ (l : ℕ) [Fact l.Prime] (p : ℕ) {Y S S' B B' O : Scheme.{0}} (g : Y ⟶ O) (s : S ⟶ Y) (bS : S ⟶ B) (β : B ⟶ O),
  IsPullback s bS g β → ∀ (i : S' ⟶ S) (bS' : S' ⟶ B') (γ : B' ⟶ B), i ≫ bS = bS' ≫ γ → IsUnit (l : Γ(S, ⊤)) →
  ∀ (T : crystallineComparison.Corr p Y) (w : Wt T.Z) (c : TranscendenceTraces.Corr S S) (c' : TranscendenceTraces.Corr S' S'), IsBC T w s bS c → IsBC T w (i ≫ s) bS' c' →
    ∀ k j : ℤ, pullHQ l (sch.map i) k j ∘ₗ c.opQ l k j = c'.opQ l k j ∘ₗ pullHQ l (sch.map i) k j

def ESGen : Prop :=
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
  ∀ c : Fin (n + 1) → TranscendenceTraces.Corr (geom Ω (pullback.snd g (sp (algebraMap O K)))) (geom Ω (pullback.snd g (sp (algebraMap O K)))),
    (∀ j, IsBC (T j) (Wt.const _ 1) (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (c j)) →
  ∀ (σ : Ω ≃ₐ[K] Ω) (hσ : ∀ v ∈ V, σ v ∈ V) (k : ℤ),
    ((∀ v : V, r ⟨σ v, hσ v v.2⟩ = r v) → galHQ l Ω (pullback.snd g (sp (algebraMap O K))) k 0 σ = 1) ∧
    ((∀ v : V, r ⟨σ v, hσ v v.2⟩ = r v ^ p ^ f) → ∑ j : Fin (n + 1), ((co (p ^ f) j : ℤ) : ℚ_[l]) •
      ((c j).opQ l k 0 * galHQ l Ω (pullback.snd g (sp (algebraMap O K))) k 0 σ⁻¹ ^ (n - j)) = 0)

end UpperTheory.Gal.Mod

end
