import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCuspOfVanishOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ChartEigFrame

open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.FlagMod GlobalTheory.Reg
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem tanPull_injective_of_chart {V K : Type} [CommRing V] [CommRing K] (ρ : V →+* K) (hρ : Function.Injective ρ)
    (M : MChart Y) {x : Sp V ⟶ Y.X} {x' : Sp K ⟶ Y.X} (e : spMap ρ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ M.U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ M.U) : Function.Injective (tanPull (G := Y.t.G) ρ e) := by
  intro u u' huu
  obtain ⟨cv, rfl⟩ := (vec M x h).surjective u
  obtain ⟨cv', rfl⟩ := (vec M x h).surjective u'
  rw [tanPull_vec M ρ e h h', tanPull_vec M ρ e h h'] at huu
  have := (vec M x' h').injective huu
  congr 1
  funext j
  exact hρ (congrFun this j)

theorem exists_eigFrame_of_top {X : FlagCover Y} {V K : Type} [CommRing V] [CommRing K] [Algebra c.F K]
    (ρ : V →+* K) (hρ : Function.Injective ρ) (φ : c.F →+* V) (hφ : ρ.comp φ = algebraMap c.F K)
    (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (hz' : ⊤ ≤ (spMap ρ ≫ q) ⁻¹ᵁ X.F.U k)
    (htop : ∀ σ, initSpan K (X.F.vecAt k (spMap ρ ≫ q) hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap ρ ≫ q) ≫ X.π) σ) :
    ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (tv (X.F.vecAt k q hz rfl τ i)).left := by
  have hx : ⊤ ≤ (q ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hz rfl
  have hx' : ⊤ ≤ ((spMap ρ ≫ q) ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hz' rfl
  have e : spMap ρ ≫ (q ≫ X.π) = (spMap ρ ≫ q) ≫ X.π := (Category.assoc _ _ _).symm
  have hinj := tanPull_injective_of_chart ρ hρ (X.F.M k).toMChart e hx hx'
  have hpull : ∀ τ i, tanPull ρ e (X.F.vecAt k q hz rfl τ i) = X.F.vecAt k (spMap ρ ≫ q) hz' rfl τ i :=
    fun τ i => X.F.tanPull_vecAt k ρ q hz hz' rfl rfl e τ i
  have hmem : ∀ τ i, X.F.vecAt k (spMap ρ ≫ q) hz' rfl τ i ∈ eigLie c ((spMap ρ ≫ q) ≫ X.π) τ := fun τ i => by
    rw [← htop τ]
    exact Submodule.subset_span ⟨i, i.2, rfl⟩
  have hsmul : ∀ (τ : E →+* ℂ) (a : 𝓞 E) (w : TanM (q ≫ X.π) Y.t.G),
      tanPull ρ e (φ (embK c τ a) • w) = algebraMap c.F K (embK c τ a) • tanPull ρ e w := fun τ a w => by
    rw [map_smulₛₗ, ← hφ]
    rfl
  refine ⟨GlobalTheory.ShFam.EigFrame.ofVec (fun τ i => X.F.vecAt k q hz rfl τ i) (fun τ i a => ?_) (fun τ w hw => ?_),
    fun τ i => rfl⟩
  · apply hinj
    rw [tanPull_actR, hsmul, hpull]
    exact hmem τ i a
  · have hw' : tanPull ρ e w ∈ eigLie c ((spMap ρ ≫ q) ≫ X.π) τ := fun a => by
      rw [← tanPull_actR, hw a, hsmul]
    rw [← htop τ] at hw'
    obtain ⟨a, -, ha⟩ := mem_initSpan.1 hw'
    obtain ⟨W, hW⟩ := X.F.uAt_split k q hz τ
    obtain ⟨cv, rfl⟩ := (vec (X.F.M k).toMChart (q ≫ X.π) hx).surjective w
    rw [X.F.sum_vecAt, tanPull_vec (X.F.M k).toMChart ρ e hx hx'] at ha
    have hc := (vec (X.F.M k).toMChart _ hx').injective ha
    rw [X.F.uAt_spMap k ρ q hz hz'] at hc
    have hWρ : W.map ρ * (X.F.uAt k q hz τ).map ρ = 1 := by
      rw [← Matrix.map_mul, hW, Matrix.map_one _ (map_zero _) (map_one _)]
    have ha2 : (W.map ρ).mulVec (fun j => ρ (cv j)) = a := by
      rw [← hc, Matrix.mulVec_mulVec, hWρ, Matrix.one_mulVec]
    refine ⟨W.mulVec cv, ?_, fun b hb => ?_⟩
    · show _ = ∑ i, _ • X.F.vecAt k q hz rfl τ i
      rw [X.F.sum_vecAt]
      congr 1
      funext j
      apply hρ
      rw [RingHom.map_mulVec]
      have : (ρ ∘ W.mulVec cv) = a := by
        rw [← ha2]
        funext i
        exact RingHom.map_mulVec ρ W cv i
      rw [this, hc]
    · have hb' : vec (X.F.M k).toMChart (q ≫ X.π) hx cv =
          vec (X.F.M k).toMChart (q ≫ X.π) hx ((X.F.uAt k q hz τ).mulVec b) := by
        rw [← X.F.sum_vecAt]
        exact hb
      have := (vec (X.F.M k).toMChart _ hx).injective hb'
      rw [this, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]

theorem exists_eigFrame_vecAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : FlagCover Y) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V), (algebraMap V K).comp φ = algebraMap c.F K → ∀ (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (yF : Sp K ⟶ Xo.XF c), yF ≫ pullback.snd _ _ = spMap (algebraMap c.F K) → (spMap (algebraMap V K) ≫ q) ≫ X.π = yF ≫ Y.j → ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (X.F.vecAt k q hz rfl τ i)).left := by
  intro E _ _ _ H Dw l Xo c O _ β Y X V K _ _ _ _ _ _ φ hφ q k hz yF hyF hpt
  have hz' : ⊤ ≤ (spMap (algebraMap V K) ≫ q) ⁻¹ᵁ X.F.U k := le_preimage_comp _ hz
  have key : ∀ (x'' : Sp K ⟶ Y.X) (hx : (spMap (algebraMap V K) ≫ q) ≫ X.π = x''),
      (∀ σ, initSpan K (X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap (algebraMap V K) ≫ q) ≫ X.π) σ := by
    rintro x'' rfl h
    exact h
  exact exists_eigFrame_of_top (algebraMap V K) (IsFractionRing.injective V K) φ hφ q k hz hz'
    (key _ hpt fun σ => X.top K yF hyF _ hpt k hz' σ)

end GlobalTheory.ChartEigFrame
