import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase.Trans

open GlobalTheory.ShFam.Pad.Guard GlobalTheory.TangentOrigin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

theorem sp_epsMul_mul {K : Type} [CommRing K] (a b : K) :
    spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul (a * b)) := by
  rw [sp_comp]
  congr 1
  ext r <;> simp [epsMul, mul_comm]

theorem isEigTan_smul {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {τ : E →+* ℂ}
    {w : Sp (DualNumber K) ⟶ Z.t.G.left} (hw : IsEigTan Z φ x τ w) (a : K) :
    IsEigTan Z φ x τ (spMap (epsMul a) ≫ w) := by
  refine ⟨?_, fun b => ?_⟩
  · have hu : ∀ k : Fin 1, IsTanAtG Z.t x ((fun _ => w) k) := fun _ => hw.1
    exact comb_tan hu (comb_smul hu (isCombAtG_single Z.t x hu 0) a)
  · rw [Category.assoc, hw.2 b, ← Category.assoc, ← Category.assoc, sp_epsMul_mul, sp_epsMul_mul, mul_comm]

theorem norm_le_one {C : Type} [NormedField C] {φ : c.F →+* C} {x : Sp C ⟶ Z.X} {τ : E →+* ℂ} {r : ℕ}
    {u u' : Fin r → (Sp (DualNumber C) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) (hu' : IsEigBasis Z φ x τ u')
    {Λ : Set (Sp (DualNumber C) ⟶ Z.t.G.left)} {δ δ' : C} (h0 : δ ≠ 0) (hδ : ‖δ'‖ = ‖δ‖)
    (h : ∀ w, IsEigTan Z φ x τ w →
      ((∃ a : Fin r → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t x u a w) ↔ spMap (epsMul δ) ≫ w ∈ Λ))
    (h' : ∀ w, IsEigTan Z φ x τ w →
      ((∃ a : Fin r → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t x u' a w) ↔ spMap (epsMul δ') ≫ w ∈ Λ))
    {i : Fin r} {a : Fin r → C} (ha : IsCombAtG Z.t x u a (u' i)) (b : Fin r) : ‖a b‖ ≤ 1 := by
  have h1 : spMap (epsMul δ') ≫ u' i ∈ Λ := by
    refine (h' _ (hu'.1 i)).1 ⟨Pi.single i 1, fun k => ?_, isCombAtG_single Z.t x (fun j => (hu'.1 j).1) i⟩
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  have h2 := isEigTan_smul Z (hu'.1 i) (δ' / δ)
  obtain ⟨a', ha', hc⟩ := (h _ h2).2 (by
    rw [← Category.assoc, sp_epsMul_mul, mul_div_cancel₀ _ h0]; exact h1)
  have h3 := (hu.2 _ h2).unique (comb_smul (fun j => (hu.1 j).1) ha (δ' / δ)) hc
  have h4 := ha' b
  rw [← congrFun h3 b, norm_mul, norm_div, hδ, div_self (norm_ne_zero_iff.2 h0), one_mul] at h4
  exact h4

theorem evalPt_app {K : Type} [CommRing K] {X W : Scheme.{0}} (j : W ⟶ X) (x : Sp K ⟶ W) (V : X.Opens)
    (h : ⊤ ≤ (x ≫ j) ⁻¹ᵁ V) (f : Γ(X, V)) : evalPt (x ≫ j) V h f = evalPt x (j ⁻¹ᵁ V) h (j.app V f) := by
  have e : (x ≫ j).appLE V ⊤ h = j.app V ≫ x.appLE (j ⁻¹ᵁ V) ⊤ h := Scheme.Hom.comp_appLE _ _ _ _ _
  unfold evalPt
  rw [e]
  rfl

theorem exists_generic {F : Type} [Field F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) {r : ℕ}
    {τ : E →+* ℂ} {U U' : X.Opens} {u : LocAssign Z r jB U} {u' : LocAssign Z r jB U'}
    (hV : IsAffineOpen (jB ⁻¹ᵁ (U ⊓ U'))) (hu : IsLocFrame Z e jB πB r τ U u) (hu' : IsLocFrame Z e jB πB r τ U' u') :
    ∃ T : Fin r → Fin r → Γ(W, jB ⁻¹ᵁ (U ⊓ U')),
      ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (hx' : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U')
        (hxx : ⊤ ≤ x ⁻¹ᵁ (jB ⁻¹ᵁ (U ⊓ U'))) (i : Fin r),
        IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u K x hx) (fun b => evalPt x _ hxx (T b i)) (u' K x hx' i) := by
  let x₀ : Sp Γ(W, jB ⁻¹ᵁ (U ⊓ U')) ⟶ W := hV.fromSpec
  have h₀ : ⊤ ≤ x₀ ⁻¹ᵁ (jB ⁻¹ᵁ (U ⊓ U')) := hV.fromSpec_preimage_self.ge
  have h1 : ⊤ ≤ (x₀ ≫ jB) ⁻¹ᵁ U := fun p hp => (h₀ hp).1
  have h2 : ⊤ ≤ (x₀ ≫ jB) ⁻¹ᵁ U' := fun p hp => (h₀ hp).2
  have hψ : x₀ ≫ πB ≫ genStr Z ≫ spMap e.toRingHom =
      spMap (Spec.preimage (x₀ ≫ πB ≫ genStr Z ≫ spMap e.toRingHom)).hom := (Spec.map_preimage _).symm
  choose a ha using fun i => ((hu.1 _ x₀ h1 _ hψ).2 _ ((hu'.1 _ x₀ h2 _ hψ).1 i)).exists
  refine ⟨fun b i => a i b, fun K _ x hx hx' hxx i => ?_⟩
  have hx0 : x = spMap (evalPt x _ hxx) ≫ x₀ := eq_spec_fromSpec hV x hxx
  generalize evalPt x _ hxx = ψ at hx0 ⊢
  subst hx0
  have h3 := GlobalTheory.LatDRFree.comb_map Z.t ψ (ha i)
  rw [hu'.2 _ _ ψ x₀ h2 hx' i, show u K (spMap ψ ≫ x₀) hx = _ from funext fun k => hu.2 _ _ ψ x₀ h1 hx k,
    Category.assoc]
  exact h3

end GlobalTheory.ArLieBase.Trans

namespace GlobalTheory.ArLieBase

open GlobalTheory.ShFam.Pad.Guard GlobalTheory.TangentOrigin

theorem exists_isTrans : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (X W : Scheme.{0}) (jB : W ⟶ X) (πB : W ⟶ gen Z), IsAffineHom jB → IntCrit (πB ≫ genStr Z ≫ spMap e.toRingHom) jB → ∀ (r : ℕ) (τ : E →+* ℂ) (kind : ℕ → Bool) (U U' : X.Opens) (u : LocAssign Z r jB U) (u' : LocAssign Z r jB U'), IsAffineOpen (U ⊓ U') → IsLocFrame Z e jB πB r τ U u → IsLocFrame Z e jB πB r τ U' u' → IsLocLat Z e jB πB r τ kind U u → IsLocLat Z e jB πB r τ kind U' u' → ∃ A : Matrix (Fin r) (Fin r) Γ(X, U ⊓ U'), IsTrans Z jB πB u u' A := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W jB πB hj hI r τ kind U U' u u' hV hu hu' hL hL'
  obtain ⟨T, hT⟩ := Trans.exists_generic Z e jB πB (hV.preimage jB) hu hu'
  have key : ∀ b i, ∃ f₀ : Γ(X, U ⊓ U'), jB.app (U ⊓ U') f₀ = T b i := fun b i => by
    refine hI _ hV _ fun v ε xg xt h1 h2 h3 hx => ?_
    obtain ⟨hp, hio, -⟩ := ioOf_spec F v ε
    haveI : Fact (resP v).Prime := ⟨hp⟩
    have hxU : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U := fun p hp => (hx hp).1
    have hxU' : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U' := fun p hp => (hx hp).2
    obtain ⟨δ, hδ, hd⟩ := hL v hp ε xg xt h1 h2 (fun p hp => (h3 hp).1) hxU
    obtain ⟨δ', hδ', hd'⟩ := hL' v hp ε xg xt h1 h2 (fun p hp => (h3 hp).2) hxU'
    have h0 : δ ≠ 0 := by
      rw [← norm_pos_iff, hδ]
      exact Real.rpow_pos_of_pos (Nat.cast_pos.2 hp.pos) _
    have h4 : (spMap (ioOf (resP v) ε) ≫ xg) ≫ πB ≫ genStr Z ≫ spMap e.toRingHom =
        spMap ((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))) := by
      rw [Category.assoc, h1, sp_comp]
    have hy : ⊤ ≤ ((spMap (ioOf (resP v) ε) ≫ xg) ≫ jB) ⁻¹ᵁ U := fun p _ => hxU (Set.mem_univ _)
    have hy' : ⊤ ≤ ((spMap (ioOf (resP v) ε) ≫ xg) ≫ jB) ⁻¹ᵁ U' := fun p _ => hxU' (Set.mem_univ _)
    have b1 := hu.1 _ _ hy _ h4
    have b2 := hu'.1 _ _ hy' _ h4
    rw [show u _ _ hy = _ from funext fun k => hu.2 _ _ _ xg hxU hy k, Category.assoc] at b1
    rw [show u' _ _ hy' = _ from funext fun k => hu'.2 _ _ _ xg hxU' hy' k, Category.assoc] at b2
    exact (hio _).1 (Trans.norm_le_one Z b1 b2 h0 (hδ'.trans hδ.symm) hd hd'
      (GlobalTheory.LatDRFree.comb_map Z.t (ioOf (resP v) ε) (hT _ xg hxU hxU' hx i)) b)
  choose A hA using key
  refine ⟨Matrix.of A, fun K _ x hx hx' hxx i => ?_⟩
  have h := hT K x hx hx' hxx i
  simp only [← hA] at h
  simp only [Matrix.of_apply, Trans.evalPt_app]
  exact h

end GlobalTheory.ArLieBase

end
