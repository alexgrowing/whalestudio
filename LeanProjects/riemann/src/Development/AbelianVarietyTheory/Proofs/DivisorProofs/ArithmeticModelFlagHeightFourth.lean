import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

attribute [local instance] Over.cartesianMonoidalCategory

theorem intComb_of_intMatrix {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X0 : Scheme.{0}} (t : SAB H X0) {K : Type} [CommRing K] {p : ℕ} [Fact p.Prime] (io : K →+* ℂ_[p])
    {x0 : Sp K ⟶ X0} {r : ℕ} {u u' : Fin r → (Sp (DualNumber K) ⟶ t.G.left)} (hu : ∀ b, IsTanAtG t x0 (u b))
    (A : Matrix (Fin r) (Fin r) K) (hA : ∀ j, IsCombAtG t x0 u (fun b => A b j) (u' j))
    (hn : ∀ b j, ‖io (A b j)‖ ≤ 1) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left)
    (h : ∃ a : Fin r → ℂ_[p], (∀ i, ‖a i‖ ≤ 1) ∧
      IsCombAtG t (spMap io ≫ x0) (fun i => spMap (dualMap io) ≫ u' i) a w) :
    ∃ a : Fin r → ℂ_[p], (∀ i, ‖a i‖ ≤ 1) ∧
      IsCombAtG t (spMap io ≫ x0) (fun i => spMap (dualMap io) ≫ u i) a w := by
  obtain ⟨a, ha, hw⟩ := h
  refine ⟨(A.map io).mulVec a, fun b => ?_, tanLinG _ (fun b => GlobalTheory.FactorDepth.isTanAtG_map t io (hu b)) _
    (A.map io) a w (fun j => GlobalTheory.LatDRFree.comb_map t io (hA j)) hw⟩
  show ‖∑ j, io (A b j) * a j‖ ≤ 1
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => by
    rw [norm_mul]; exact mul_le_one₀ (hn b j) (norm_nonneg _) (ha j)

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (x : Sp R ⟶ X)
    (V : X.Opens) (h : x.base (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ x ⁻¹ᵁ V := fun y _ =>
  ((IsLocalRing.specializes_closedPoint y).map x.base.hom.continuous).mem_open V.2 h

theorem isLieLat_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (X W : Scheme.{0}) (jB : W ⟶ X) (πB : W ⟶ gen Z) (M : X.Modules) (r : ℕ) (τ : E →+* ℂ) (dual : Bool) (kind : ℕ → Bool) (ι : Type) (U : ι → X.Opens) (f : ∀ i, Fin r → Γ(M, U i)) (hf : ∀ i, VB.IsFrame (f i)) (uu : FrAssign Z M r jB), (∀ x : X, ∃ i, x ∈ U i) → IsLieFrames Z e jB πB M r τ dual uu → (∀ i, IsLocLat Z e jB πB r τ kind (U i) (uu (U i) (f i) (hf i))) → IsLieLat Z e jB πB M r τ kind (fun _ => True) uu := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W jB πB M r τ dual kind ι U f hf uu hcov hLF hLL
  have key : ∀ (U₀ : X.Opens) (f₀ : Fin r → Γ(M, U₀)) (hf₀ : VB.IsFrame f₀),
      IsLocLat Z e jB πB r τ kind U₀ (uu U₀ f₀ hf₀) := by
    intro U₀ f₀ hf₀ v hp ε xg xt hgen hxt hxtU hx
    obtain ⟨i, hi⟩ := hcov (xt.base (IsLocalRing.closedPoint ε.O))
    have hxti : ⊤ ≤ xt ⁻¹ᵁ U i := top_le_preimage_of_closedPoint xt _ hi
    have hcomp : ∀ V : X.Opens, ⊤ ≤ xt ⁻¹ᵁ V → ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ V := fun V hV => by
      rw [← hxt, Scheme.Hom.comp_preimage]; exact fun z _ => hV trivial
    have hxgi := hcomp _ hxti
    obtain ⟨δ, hδ, hiff⟩ := hLL i v hp ε xg xt hgen hxt hxti hxgi
    refine ⟨δ, hδ, fun w hw => Iff.trans ?_ (hiff w hw)⟩
    haveI : Fact (resP v).Prime := ⟨hp⟩
    have hint : ∀ (V : X.Opens), ⊤ ≤ xt ⁻¹ᵁ V → ∀ (hV : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ V) (s : Γ(X, V)),
        ‖ioOf (resP v) ε (TangentOrigin.evalPt (xg ≫ jB) V hV s)‖ ≤ 1 := by
      intro V hV hV' s
      have key : ∀ (y : Sp (AlgebraicClosure F) ⟶ X) (hy : spMap ε.O.subtype ≫ xt = y) (h : ⊤ ≤ y ⁻¹ᵁ V),
          TangentOrigin.evalPt y V h s ∈ ε.O := by
        rintro _ rfl h
        rw [TangentOrigin.evalPt_spMap_comp ε.O.subtype xt V hV h s]
        exact (TangentOrigin.evalPt xt V hV s).2
      exact (ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε _).2 (key _ hxt hV')
    have hinf : ∀ V V' : X.Opens, ⊤ ≤ xt ⁻¹ᵁ V → ⊤ ≤ xt ⁻¹ᵁ V' → ⊤ ≤ xt ⁻¹ᵁ (V ⊓ V') :=
      fun V V' h h' z hz => ⟨h hz, h' hz⟩
    have htan : ∀ (V : X.Opens) (g : Fin r → Γ(M, V)) (hg : VB.IsFrame g) (h : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ V) b,
        IsTanAtG Z.t (xg ≫ πB ≫ genι Z) (uu V g hg _ xg h b) :=
      fun V g hg h b => ((hLF.1 V g hg _ xg h _ hgen).1 b).1
    obtain ⟨A, hA, hAn⟩ : ∃ A : Matrix (Fin r) (Fin r) (AlgebraicClosure F),
        (∀ j, IsCombAtG Z.t (xg ≫ πB ≫ genι Z) (uu U₀ f₀ hf₀ _ xg hx) (fun b => A b j)
          (uu (U i) (f i) (hf i) _ xg hxgi j)) ∧ ∀ b j, ‖ioOf (resP v) ε (A b j)‖ ≤ 1 := by
      cases dual
      · exact ⟨fun b j => TangentOrigin.evalPt (xg ≫ jB) (U₀ ⊓ U i) (hcomp _ (hinf _ _ hxtU hxti)) (trCo hf₀ (f i) b j),
          fun j => hLF.2.1 U₀ (U i) f₀ (f i) hf₀ (hf i) _ xg hx hxgi _ j, fun b j => hint _ (hinf _ _ hxtU hxti) _ _⟩
      · exact ⟨fun b j => TangentOrigin.evalPt (xg ≫ jB) (U i ⊓ U₀) (hcomp _ (hinf _ _ hxti hxtU)) (trCo (hf i) f₀ j b),
          fun j => hLF.2.1 (U i) U₀ (f i) f₀ (hf i) hf₀ _ xg hxgi hx _ j, fun b j => hint _ (hinf _ _ hxti hxtU) _ _⟩
    obtain ⟨B, hB, hBn⟩ : ∃ B : Matrix (Fin r) (Fin r) (AlgebraicClosure F),
        (∀ j, IsCombAtG Z.t (xg ≫ πB ≫ genι Z) (uu (U i) (f i) (hf i) _ xg hxgi) (fun b => B b j)
          (uu U₀ f₀ hf₀ _ xg hx j)) ∧ ∀ b j, ‖ioOf (resP v) ε (B b j)‖ ≤ 1 := by
      cases dual
      · exact ⟨fun b j => TangentOrigin.evalPt (xg ≫ jB) (U i ⊓ U₀) (hcomp _ (hinf _ _ hxti hxtU)) (trCo (hf i) f₀ b j),
          fun j => hLF.2.1 (U i) U₀ (f i) f₀ (hf i) hf₀ _ xg hxgi hx _ j, fun b j => hint _ (hinf _ _ hxti hxtU) _ _⟩
      · exact ⟨fun b j => TangentOrigin.evalPt (xg ≫ jB) (U₀ ⊓ U i) (hcomp _ (hinf _ _ hxtU hxti)) (trCo hf₀ (f i) j b),
          fun j => hLF.2.1 U₀ (U i) f₀ (f i) hf₀ (hf i) _ xg hx hxgi _ j, fun b j => hint _ (hinf _ _ hxtU hxti) _ _⟩
    exact ⟨intComb_of_intMatrix Z.t _ (htan _ _ _ _) B hB hBn w, intComb_of_intMatrix Z.t _ (htan _ _ _ _) A hA hAn w⟩
  exact fun v _ hp ε xg xt h1 h2 U₀ f₀ hf₀ h3 hx => key U₀ f₀ hf₀ v hp ε xg xt h1 h2 h3 hx

end GlobalTheory.ArLieBase

end
