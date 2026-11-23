import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.OpCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod

def piG {k L : Type} [Field k] [Field L] {H : HTower k} {θ : H.Γ → L} {O : Type} [CommRing O] [Algebra O k] (C : Cover H θ O)
    (Ω : Type) [Field Ω] [Algebra k Ω] : H.geomZ Ω ⟶ geom Ω (pullback.snd C.p (sp (algebraMap O k))) :=
  geomMap Ω H.q (pullback.lift C.π H.q C.ov) (pullback.lift_snd _ _ _)

def GalEx : Prop := ∀ {Y S : Scheme.{0}} (s : Y ⟶ S) (d : ℕ), FEt s d →
  ∃ (W : Scheme.{0}) (c : W ⟶ S) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (σ : Fin d → (W ⟶ Y)),
    IsGalois c G a ∧ Splits s c σ

def HopOp : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω], IsUnit (l : Ω) →
  ∀ g d, FEt (H.s g) d → hop l H Ω g =
    DirectSum.lmap fun n : ℤ => trHQ l (H.sΩ Ω g) (Wt.const _ 1) n 0 ∘ₗ pullHQ l (sch.map (H.tΩ Ω g)) n 0

def BCEx : Prop := ∀ (p : ℕ) (O k Ω : Type) [CommRing O] [Field k] [Algebra O k] [Field Ω] [Algebra k Ω], (p : k) ≠ 0 →
  ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of O)) (T : crystallineComparison.Corr p Y), T.r ≫ g = T.p ≫ g →
    ∃ c : TranscendenceTraces.Corr (geom Ω (pullback.snd g (sp (algebraMap O k)))) (geom Ω (pullback.snd g (sp (algebraMap O k)))),
      IsBC T (Wt.const _ 1) (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) c

def LiesOp : Prop := ∀ (l : ℕ) [Fact l.Prime] (p : ℕ) (k L : Type) [Field k] [Field L] (H : HTower k) (θ : H.Γ → L) (O : Type)
  [CommRing O] [Algebra O k] (C : Cover H θ O) (Ω : Type) [Field Ω] [Algebra k Ω], IsUnit (l : Ω) →
  ∀ (T : crystallineComparison.Corr p C.Y) (g : H.Γ) (d m : ℕ), FEt (H.s g) d → C.Lies g T.p T.r m →
  ∀ c : TranscendenceTraces.Corr (geom Ω (pullback.snd C.p (sp (algebraMap O k)))) (geom Ω (pullback.snd C.p (sp (algebraMap O k)))),
    IsBC T (Wt.const _ 1) (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) c →
    hop l H Ω g ∘ₗ pullTot l (sch.map (piG C Ω)) =
      (m : ℚ_[l]) • (pullTot l (sch.map (piG C Ω)) ∘ₗ DirectSum.lmap fun n : ℤ => c.opQ l n 0)

def FixDesc : Prop := ∀ (l : ℕ) [Fact l.Prime] (k L : Type) [Field k] [Field L] [Algebra ℚ_[l] L] (H : HTower k) (θ : H.Γ → L) (O : Type)
  [CommRing O] [Algebra O k] (C : Cover H θ O) (Ω : Type) [Field Ω] [Algebra k Ω], IsUnit (l : Ω) →
  ∀ x ∈ piece l H Ω L θ, ∃ y, x = (pullTot l (sch.map (piG C Ω))).baseChange L y

def TowES : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (p f n : ℕ), p.Prime →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O], ¬ IsUnit (p : O) →
  ∀ (K : Type) [Field K] [Algebra O K], (p : K) ≠ 0 → (∀ a : IsLocalRing.ResidueField O, a ^ p ^ f = a) →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (V : ValuationSubring Ω)
    (hV : ∀ a : O, algebraMap K Ω (algebraMap O K a) ∈ V),
    (∀ a ∈ IsLocalRing.maximalIdeal O, V.valuation (algebraMap K Ω (algebraMap O K a)) < 1) → V.valuation (l : Ω) = 1 →
  ∀ (L : Type) [Field L] [Algebra ℚ_[l] L] (H : HTower K) (θ : H.Γ → L), Nice H → ∀ (C : Cover H θ O) (ϑ : ℕ → L), C.Cong p f n ϑ →
  (∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ piece l H Ω L θ, galV l H Ω L σ x ∈ piece l H Ω L θ) →
  ∀ σ : Ω ≃ₐ[K] Ω, (∀ v ∈ V, σ v ∈ V) → ∀ x ∈ piece l H Ω L θ,
    ((∀ v ∈ V, V.valuation (σ v - v) < 1) → galV l H Ω L σ x = x) ∧
    ((∀ v ∈ V, V.valuation (σ v - v ^ p ^ f) < 1) → ∑ j : Fin (n + 1), (((co (p ^ f) j : ℤ) : L) * ϑ j) •
      (galV l H Ω L σ⁻¹)^[n - j] x = 0)

def PlaceData : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
  (∀ a : Ow w, algebraMap E Ω (algebraMap (Ow w) E a) ∈ A) ∧
  (∀ a ∈ IsLocalRing.maximalIdeal (Ow w), A.valuation (algebraMap E Ω (algebraMap (Ow w) E a)) < 1) ∧
  (∀ a : IsLocalRing.ResidueField (Ow w), a ^ Ideal.absNorm w.asIdeal = a) ∧ normV w = Ideal.absNorm w.asIdeal ∧
  (∀ m : ℕ, (m : 𝓞 E) ∉ w.asIdeal → A.valuation (m : Ω) = 1) ∧ (∀ m : ℕ, (m : 𝓞 E) ∈ w.asIdeal → ¬ IsUnit (m : Ow w)) ∧
  (∀ s ∈ Ine (F := E) A, (∀ v ∈ A, s v ∈ A) ∧ ∀ v ∈ A, A.valuation (s v - v) < 1) ∧
  ∀ (q : ℕ) (σ : G E Ω), IsFrob A q σ → (∀ v ∈ A, σ v ∈ A) ∧ ∀ v ∈ A, A.valuation (σ v - v ^ q) < 1

def GrPass : Prop := ∀ (Γ L : Type) [Group Γ] [Field L] (d : ℕ) (ρ₀ ρ : Γ →* GL (Fin d) L), IsGr ρ₀ ρ → ∀ (g : Γ) (P : Polynomial L),
  Polynomial.aeval (ρ₀ g : Matrix (Fin d) (Fin d) L) P = 0 → Polynomial.aeval (ρ g : Matrix (Fin d) (Fin d) L) P = 0

end UpperTheory.Gal.Mod

end
