import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (w.adicCompletion E) → WD h}

def FieldG {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h') : Prop :=
  ∀ (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'),
    (∀ z, φ z ∈ A' ↔ z ∈ A) → (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → Continuous i →
    (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) →
    ∀ (n : ℕ) (π : IrrRep (GL (Fin n) (w.adicCompletion E))) (π' : IrrRep (GL (Fin n) (w'.adicCompletion E')))
      (e : π.V ≃ₗ[ℂ] π'.V), (∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) → Good (cls π) →
      ∃ (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = rc (cls π) ∧ WD.mk b' = rc' (cls π') ∧
        b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)) → b.ρ σ = b'.ρ σ'

def FieldGT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω')
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w')
    (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'),
    IsRecT h rc → IsRecT h' rc' → FieldG rc rc'

namespace Old

theorem twist (H : Laws a ha ε rc) : ∀ x χ hχ, Good x → rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ)) :=
  fun x χ hχ _ => H.twist x χ hχ

theorem central (H : Laws a ha ε rc) : ∀ (x : IrrGL (w.adicCompletion E)) ω, Good x → HasCentralChar x.rep ω →
    ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ) := fun x ω _ => H.central x ω

theorem absCentral (H : Laws a ha ε rc) : ∀ (x : IrrGL (w.adicCompletion E)) ω, HasCentralChar x.rep ω →
    ∀ σ, ‖((rc x).eig σ).prod‖ = ‖(ω (a σ) : ℂ)‖ := fun x ω hω σ => by rw [H.central x ω hω σ]

theorem dual (H : Laws a ha ε rc) : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Good (cls π) →
    Nonempty (π'.ρ.Equiv (contra π.ρ)) → rc (cls π') = (rc (cls π)).lpDual := fun n π π' _ => H.dual n π π'

theorem inj (H : Laws a ha ε rc) : ∀ x y, Good y → rc x = rc y → x = y := fun _ _ _ e => H.bij.1 e

theorem depth (H : Laws a ha ε rc) :
    ∀ x, Good x → fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ → IsTameWD (rc x) := fun x _ => (H.depth x).1

theorem type (hD : DepthZeroTypeInertia) (H : IsRec h rc) : TypeLaw h rc := by
  intro E' _ _ _ _ _ _ g _ w' h'
  exact hD E E' Ω g A w h w' h' rc H

theorem ex (hL : LocalLanglandsGL) (h : IsPlaceOver A w) : ∃ rc, IsRec h rc := (hL.1 E Ω A w h).exists

theorem uniq (hL : LocalLanglandsGL) {rc' : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) (H' : IsRec h rc') :
    ∀ x, Good x → rc x = rc' x := fun x _ => congrFun ((hL.1 E Ω A w h).unique H H') x

theorem field (hL : LocalLanglandsGL) {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    {rc' : IrrGL (w'.adicCompletion E') → WD h'} (H : IsRec h rc) (H' : IsRec h' rc') : FieldG rc rc' :=
  fun φ j i h1 h2 h3 h4 n π π' e he _ => hL.2 E Ω A w h E' Ω' A' w' h' rc rc' H H' φ j i h1 h2 h3 h4 n π π' e he

theorem abConv (hL : LocalLanglandsGL) (hD : DepthZeroTypeInertia) (H : IsRec h rc) : IsRecT h rc :=
  have _ := hL; isRecT_of_isRec hD H

end Old

namespace New

theorem type (_hD : DepthZeroTypeInertia) (H : IsRecT h rc) : TypeLaw h rc := H.choose_spec.choose_spec.type

theorem ex (hL : RecTExists) (h : IsPlaceOver A w) : ∃ rc, IsRecT h rc := hL E Ω A w h

theorem uniq (_hL : RecTExists) {rc' : IrrGL (w.adicCompletion E) → WD h} (H : IsRecT h rc) (H' : IsRecT h rc') :
    ∀ x, Good x → rc x = rc' x := recTUnique E Ω A w h rc rc' H H'

theorem abConv (_hL : RecTExists) (_hD : DepthZeroTypeInertia) (H : IsRecT h rc) : IsRecT h rc := H

theorem llOf : RecTExists → LocalConverseGL → DepthZeroCuspidalLL → DepthZeroInduction →
    BrauerDegreeZero → ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments →
    StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → RecTExists :=
  fun h _ _ _ _ _ _ _ _ _ _ _ _ => h

end New

end UpperTheory.One.M
