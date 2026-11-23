import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.BaseCase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Pointwise in
private theorem ine_restrict {K M Ω : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] (A : ValuationSubring Ω) (t : G M Ω) (ht : t ∈ Ine (F := M) A) :
    (AlgEquiv.restrictScalars K t : G K Ω) ∈ Ine (F := K) A := by
  obtain ⟨h1, h2⟩ := ht
  refine ⟨?_, fun x hx => h2 x hx⟩
  have h1' : t • A = A := h1
  show (AlgEquiv.restrictScalars K t : G K Ω) • A = A
  have : (AlgEquiv.restrictScalars K t : G K Ω) • A = t • A := by
    ext x
    simp only [ValuationSubring.mem_smul_pointwise_iff_exists]
    rfl
  rw [this, h1']

private theorem place_unique {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (A : ValuationSubring Ω)
    (v w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) : v = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [← h x, ← h' x]

private theorem le_closed (P₀ : Lbl → Prop) (hl : ∀ a l, P₀ a → P₀ (a.lift l)) {a b : Lbl} (h : a.Le b) (ha : P₀ a) : P₀ b := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih =>
    obtain ⟨l, _, rfl⟩ := hbc
    exact hl _ _ ih

theorem UpperTheory.Gal.InertialTypesAlt.lblOn :
    BaseCase → LiftsFix → PlaceEx → ResEmbEx → UnrOfIne → ∀ P₀ : Lbl → Prop, (∀ a l, P₀ a → P₀ (a.lift l)) → StepAt P₀ id → StepAt P₀ Not → LblOn P₀ := by
  intro hB hF hP hR hU P₀ hl hS hN E Ω _ _ _ n hn X Y hXY A Θ hΘ
  induction hXY using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ v w hv hw e e' he he' τ τ' hτ hτ' a _ hL
    obtain rfl := place_unique A v w hv hw
    exact ⟨a, Relation.ReflTransGen.refl, hB Y.K Ω n Y.π A Θ v e e' he he' τ τ' hτ hτ' a hL⟩
  | @head X Z hXZ hZY ih =>
    intro hI v w hv hw e e' he he' τ τ' hτ hτ' a ha hL
    obtain ⟨i1, i2, hGal, hpr, hW⟩ := hXZ
    obtain ⟨u, hu, τ₁, hτ₁⟩ := hP X.K Z.K Ω A v hv n Z.π
    obtain ⟨⟨e₁, he₁⟩, _⟩ := hR Z.K Ω A u hu
    have hIZ : ∀ t ∈ Ine (F := X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Z.K t := by
      intro t ht x
      obtain ⟨y, hy⟩ := hF E Ω n Z Y hZY x
      rw [← hy]
      exact hI t ht y
    obtain ⟨hund, hUnr, _⟩ := hU X.K Z.K Ω A v u hv hu hIZ
    let u' : PlacesOver Z.K v := ⟨u, ⟨by rw [← hund]; rfl⟩⟩
    have hb : ∃ b₁, a.Le b₁ ∧ HasLbl (Θ.comp e₁.toMonoidHom) τ₁.ρ b₁ := by
      by_cases hs : UpperTheory.ConvolutionTheory.GM.Split Z.K v
      · exact hS X.K Z.K Ω hpr n hn X.π Z.π hW A Θ hΘ v u' hs hUnr e e₁ he he₁ τ τ₁ hτ hτ₁ a ha hL
      · exact hN X.K Z.K Ω hpr n hn X.π Z.π hW A Θ hΘ v u' hs hUnr e e₁ he he₁ τ τ₁ hτ hτ₁ a ha hL
    obtain ⟨b₁, hab, hb₁⟩ := hb
    have hIZ' : ∀ t ∈ Ine (F := Z.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t := by
      intro t ht y
      exact hI _ (ine_restrict (K := X.K) A t ht) y
    obtain ⟨b, hbb, hbL⟩ := ih hIZ' u w hu hw e₁ e' he₁ he' τ₁ τ' hτ₁ hτ' b₁ (le_closed P₀ hl hab ha) hb₁
    exact ⟨b, hab.trans hbb, hbL⟩
