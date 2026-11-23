import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.FrameGenericValuation
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

theorem UpperTheory.eigenvariety_over_frame :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (B Y : Var F) (ρB : B.X ⟶ gen Z) (ρ : Y.X ⟶ gen Z) (f : Y.X ⟶ B.X) (φ : B.Fn →+* Y.Fn), IsOver e ρB ρ f φ → ρB ≫ genStr Z ≫ spMap e.toRingHom = B.str → ∀ (g : GenFrame e ρB) (g' g₁ : GenFrame e ρ), g.IsMap φ g' → ∀ (τ : E →+* ℂ) (XB X : Scheme.{0}) (jB : B.X ⟶ XB) (j : Y.X ⟶ X) (π : X ⟶ XB), j ≫ π = f ≫ jB → ∀ (M : XB.Modules) (hM : IsVB M (Dw.mult τ)) (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) B.Fn) (A' : Chart ((Scheme.Modules.pullback π).obj M) (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn), IsLie g τ jB dual A → IsLie g₁ τ j dual A' → IsPullCo jB π hM dual φ g' g₁ A A' → IsLat g τ jB dual A → IsLat g₁ τ j dual A' := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e B Y ρB ρ f φ h hρ g g' g₁ hg τ XB X jB j π hj M hM dual A A' hA hA' hP hL
  refine UpperTheory.frame_generic_valuation E H Dw l Xo c O β Z F e Y ρ (by rw [← h.1, Category.assoc, hρ, h.2.1]) g₁ τ X j _
    (hM.pullback π) dual A' hA' fun z => ?_
  obtain ⟨U, s, hU, hs⟩ := hM (π z)
  let ch : Chart M (Dw.mult τ) := ⟨U, s, hs⟩
  refine ⟨ch.pull hM π, hU, ?_⟩
  intro v _ ε y yt hyt hin φ' f' hf' a w hw
  let yB : AlgPt B := ⟨y.1 ≫ f, by rw [Category.assoc, h.2.1]; exact y.2⟩
  have hytB : spMap ε.O.subtype ≫ (yt ≫ π) = yB.1 ≫ jB := by
    rw [← Category.assoc, hyt, Category.assoc, hj, Category.assoc]
  have hinB : ⊤ ≤ (yt ≫ π) ⁻¹ᵁ ch.U := hin
  have hb : jB (f (below y.1)) ∈ ch.U := by
    have : (spMap ε.O.subtype ≫ yt ≫ π) (IsLocalRing.closedPoint _) ∈ ch.U := hinB (Set.mem_univ _)
    rwa [hytB] at this
  obtain ⟨φ₀, k, hk⟩ := hA.2 ch (f (below y.1)) hb
  obtain ⟨k₁, hm, hk₁⟩ := hk.pull h hg g₁
  rw [hP ch (gen_le jB hb), lieMat_mul, lieMat_lieMat _ (g₁.isUnit_det_co g' τ),
      lieMat_map _ _ (hA.1.1 ch (gen_le jB hb))] at hf'
  obtain rfl := hf'.φ_eq hk₁
  have hco : k₁.co f' τ = 1 := hk₁.co_eq (by rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one])
  have hv : ∀ i, f'.v τ i = k₁.v τ i := fun i => by
    have : f'.vec τ i = k₁.vec τ i := by
      refine (EigFrame.vec_eq k₁ f' τ i).trans (Eq.trans ?_ (EigFrame.vec_eq k₁ k₁ τ i).symm)
      rw [hco, EigFrame.co_self]
    exact congrArg (fun u => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv u).left) this
  have hval : valP ε yB = (valP ε y).comp (f.stalkMap (below y.1)).hom := by
    have := Scheme.stalkClosedPointTo_comp y.1 f
    exact congrArg (fun t => (ioOf (resP v) ε).comp (CommRingCat.Hom.hom t)) this
  have hx : spMap (valP ε yB) ≫ stalkPt B (below yB.1) ≫ ρB ≫ genι Z
      = spMap (valP ε y) ≫ stalkPt Y (below y.1) ≫ ρ ≫ genι Z := by
    have h₁ : spMap (valP ε yB) = spMap (valP ε y) ≫ spMap (f.stalkMap (below y.1)).hom := by
      rw [hval, ← Spec.map_comp]; rfl
    have h₂ := spMap_stalkMap f (below y.1)
    rw [← h.1, Category.assoc f, ← Category.assoc (stalkPt Y _), ← h₂, h₁]
    simp only [Category.assoc]
    rfl
  have key := hL ch v ε yB (yt ≫ π) hytB hinB φ₀ k hk a w
  rw [hx] at key
  refine key ?_
  have : (fun i => spMap (dualMap (valP ε yB)) ≫ k.v τ i) = fun i => spMap (dualMap (valP ε y)) ≫ f'.v τ i := by
    funext i
    rw [hv, hm, GlobalTheory.GradedPieces.dual_comp, hval]
    rfl
  rw [this]
  exact hw
