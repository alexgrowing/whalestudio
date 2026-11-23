import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpStepOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CoverOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8

universe u

namespace UpperTheory.Gal.G3

def TrBc : Prop := ∀ {B B' : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (g : B ⟶ B') {Z Y : Scheme.{0}} (p : Z ⟶ B')
  (q : Y ⟶ B') (s : Y ⟶ Z) [IsFinite s] [Etale s] (hs : s ≫ p = q) (tr : T.H (pullback.snd q g) →ₗ[R] T.H (pullback.snd p g)),
  T.IsTr (pullback.snd p g) (pullback.snd q g) (bcMap g s hs) tr → (T.bc g).IsTr p q s tr

def HodgeOpBc : Prop := ∀ (k F : Type) [Field k] [Field F] (φ : k →+* F) (H : HTower k) (g : H.Γ) [IsFinite (H.s g)] [Etale (H.s g)]
  (a b : ℕ), IsFinite ((bcAlong H φ).s g) ∧ Etale ((bcAlong H φ).s g) ∧
  ∃ tr, ((hodge F a b).bc (Spec.map (CommRingCat.ofHom φ))).IsTr H.q (H.s g ≫ H.q) (H.s g) tr ∧
    ∀ (_ : IsFinite ((bcAlong H φ).s g)) (_ : Etale ((bcAlong H φ).s g)) (x : hodgeH (bcAlong H φ).q a b),
      hodgeTrace (s := (bcAlong H φ).q) (s' := (bcAlong H φ).s g ≫ (bcAlong H φ).q) (f := (bcAlong H φ).s g) rfl a b
        (hodgePull (s := (bcAlong H φ).q) (s' := (bcAlong H φ).s g ≫ (bcAlong H φ).q) ((bcAlong H φ).comm g) a b x) =
      tr (((hodge F a b).bc (Spec.map (CommRingCat.ofHom φ))).pull (H.t g) (H.comm g) x)

def HopLies : Prop := ∀ (l : ℕ) [Fact l.Prime] {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k], (l : k) ≠ 0 →
  ∀ {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) (D : LowData C), Nice H → ∀ (Ω : Type) [Field Ω] [Algebra k Ω] (g : H.Γ),
  hop l H Ω g ∘ₗ (etG l k Ω).pull (piK C) (piK_snd C) =
    (D.m g : ℚ_[l]) • ((etG l k Ω).pull (piK C) (piK_snd C) ∘ₗ hop l (low D) Ω g)

def GenIso : Prop := ∀ {O O' k K : Type} [CommRing O] [CommRing O'] [Field k] [Field K] [Algebra O k] [Algebra O' K]
  (φ : O →+* O') (τ : k →+* K), (∀ x, algebraMap O' K (φ x) = τ (algebraMap O k x)) → ∀ {X : Scheme.{0}} (p : X ⟶ sp O),
  ∃ e : pullback (pullback.snd p (Spec.map (CommRingCat.ofHom φ))) (gen O' K) ≅
      pullback (pullback.snd p (gen O k)) (Spec.map (CommRingCat.ofHom τ)),
    e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
    e.hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _

def ModBc : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) {O : Type} [CommRing O] [IsNoetherianRing O]
  (φ : O →+* ↥(CrystallineSemistableComparison.OK l K.1)) {Y W : Scheme.{0}} (p : Y ⟶ sp O) (d : ℕ), SmoothOfRelativeDimension d p → IsProjOver p →
  ∀ (c : W ⟶ Y) [IsFinite c] [Etale c],
    (⟨_, pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))⟩ : CrystallineSemistableComparison.Model l K.1).Sm ∧
      SmoothOfRelativeDimension d (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ)))

def LowCov : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (H : HTower E) (θ : H.Γ → Qbar l) (w : HeightOneSpectrum (𝓞 E))
    (C : Cover H θ (Ow w)) (D : LowData C) (K : FinExt l) (τK : E →+* ↥K.1),
    (∀ x : Ow w, ‖(τK (x : E) : Qbar l)‖ ≤ 1) → HasGoodCovers (bcAlong (low D) τK) id

theorem matEx_of (h : RepEx) : MatEx := fun E Ω _ _ _ _ _ l _ H θ hN => by
  obtain ⟨d, ρ, -, -, ρ₀, h₀, -⟩ := h E Ω l H θ hN
  exact ⟨d, ρ₀, h₀⟩

theorem coverLow_of_cov (hC : CoverOf) (hL : LowCov) : CoverLow := fun hG E _ _ l _ H θ w C D K τK hτ n =>
  hC hG l K (bcAlong (low D) τK) id (hL E l H θ w C D K τK hτ) n

end UpperTheory.Gal.G3

end
