import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPrBPtMP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.Ar.ProdHolo

variable {k : Type} [CommRing k] {Z X : Scheme.{0}} {q : Z ⟶ Sp k} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem mem_ptsIn_preimage {π : Z ⟶ X} {z : CxPts q σ} {x : CxPts p σ} (h : z.1 ≫ π = x.1)
    {U : X.Opens} (hx : x ∈ ptsIn p σ U) : z ∈ ptsIn q σ (π ⁻¹ᵁ U) := by
  rw [mem_ptsIn] at hx ⊢
  rw [← h] at hx
  exact hx

theorem ev_appLE {π : Z ⟶ X} {z : CxPts q σ} {x : CxPts p σ} (h : z.1 ≫ π = x.1)
    {U : X.Opens} {W : Z.Opens} (e : W ≤ π ⁻¹ᵁ U) (hz : z ∈ ptsIn q σ W)
    (a : Γ(X, U)) :
    CxPts.ev q σ W ((π.appLE U W e).hom a) z = CxPts.ev p σ U a x := by
  have h1 := GlobalTheory.CxPts.ev_res (p := q) (σ := σ) e hz ((π.app U).hom a)
  refine Eq.trans ?_ (h1.trans ?_)
  · rfl
  · have h2 := GlobalTheory.Points.valR_comp z.1 π U a
    rw [h] at h2
    exact h2.symm

theorem differentiableOn_ev_prod : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) (σ : k →+* ℂ) {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] (T : Set E) (U : X.Opens) (V : Y.Opens), IsAffineOpen U → IsAffineOpen V →
  ∀ (s₁ : E → CxPts f σ) (s₂ : E → CxPts g σ) (s : E → CxPts (pullback.fst f g ≫ f) σ),
  (∀ v, (s v).1 ≫ pullback.fst f g = (s₁ v).1) → (∀ v, (s v).1 ≫ pullback.snd f g = (s₂ v).1) →
  (∀ v ∈ T, s₁ v ∈ ptsIn f σ U) → (∀ v ∈ T, s₂ v ∈ ptsIn g σ V) →
  (∀ a : Γ(X, U), DifferentiableOn ℂ (CxPts.ev f σ U a ∘ s₁) T) →
  (∀ b : Γ(Y, V), DifferentiableOn ℂ (CxPts.ev g σ V b ∘ s₂) T) →
  IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ∧
  (∀ v ∈ T, s v ∈ ptsIn (pullback.fst f g ≫ f) σ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) ∧
  ∀ t : Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V),
    DifferentiableOn ℂ (CxPts.ev (pullback.fst f g ≫ f) σ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) t ∘ s) T := by
  intro k _ X Y f g σ E _ _ T U V hU hV s₁ s₂ s h₁ h₂ m₁ m₂ d₁ d₂
  have H := IsPullback.of_hasPullback f g
  obtain ⟨hW, po⟩ := GlobalTheory.Conormal.isAffineOpen_and_isPushout H (U := ⊤) (T₀ := V) (W := U)
    (isAffineOpen_top _) hV hU le_top le_top
  have hin : ∀ v ∈ T, s v ∈ ptsIn (pullback.fst f g ≫ f) σ
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := fun v hv =>
    mem_ptsIn_inf.2 ⟨mem_ptsIn_preimage (h₁ v) (m₁ v hv), mem_ptsIn_preimage (h₂ v) (m₂ v hv)⟩
  refine ⟨hW, hin, fun t => ?_⟩
  have ht : t ∈ Subring.closure (Set.range (pullback.fst f g |>.appLE U
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_left).hom ∪
      Set.range (pullback.snd f g |>.appLE V
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_right).hom) := by
    rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout po]
    trivial
  induction ht using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact (d₁ a).congr fun v hv => ev_appLE (h₁ v) _ (hin v hv) a
    · exact (d₂ b).congr fun v hv => ev_appLE (h₂ v) _ (hin v hv) b
  | zero =>
    exact (differentiableOn_const 0).congr fun v hv => by
      simp only [Function.comp_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_zero]
  | one =>
    exact (differentiableOn_const 1).congr fun v hv => by
      simp only [Function.comp_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_one]
  | add x y _ _ hx hy =>
    exact (hx.add hy).congr fun v hv => by
      simp only [Function.comp_apply, Pi.add_apply, GlobalTheory.CxPts.ev_add]
  | neg x _ hx =>
    exact hx.neg.congr fun v hv => by
      simp only [Function.comp_apply, Pi.neg_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_neg]
  | mul x y _ _ hx hy =>
    exact (hx.mul hy).congr fun v hv => by
      simp only [Function.comp_apply, Pi.mul_apply, GlobalTheory.CxPts.ev_mul]

end GlobalTheory.CompanionTheory.Ar.ProdHolo
