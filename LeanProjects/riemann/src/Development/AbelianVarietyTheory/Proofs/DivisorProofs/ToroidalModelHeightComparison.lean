import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange

set_option autoImplicit false

open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

namespace GlobalTheory.LieFilt

theorem exists_genCoord : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} (ρ : X ⟶ Z.X), IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) → jB ≫ ρ = πB ≫ genι Z →
    ∀ {M : X.Modules} {r g : ℕ} (τ : E →+* ℂ) (t : FrAssign Z M r jB), IsLieFrames Z e jB πB M r τ false t →
    ∀ (ch : VB.Chart (omega Z.t.G) g) (V : X.Opens), V ≤ ρ ⁻¹ᵁ ch.U → IsAffineOpen V →
    ∀ (f : Fin r → Γ(M, V)) (hf : VB.IsFrame f), ∃ A, GenCoord Z jB πB t ch hf A := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB ρ hpb hρ M r g τ t ht ch V hV hVa f hf
  haveI : IsAffineHom jB := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hW : IsAffineOpen (jB ⁻¹ᵁ V) := hVa.preimage jB
  obtain ⟨x₀, h₀, e₀⟩ := TangentOrigin.exists_evalPt_eq hW (RingHom.id Γ(W, jB ⁻¹ᵁ V))
  have hx₀ : ⊤ ≤ (x₀ ≫ jB) ⁻¹ᵁ V := h₀
  have hc₀ : ⊤ ≤ (x₀ ≫ πB ≫ genι Z) ⁻¹ᵁ ch.U := by
    rw [← hρ]
    exact fun p hp => hV (hx₀ hp)
  have hψ : x₀ ≫ πB ≫ genStr Z ≫ spMap e.toRingHom =
      spMap (Spec.preimage (x₀ ≫ πB ≫ genStr Z ≫ spMap e.toRingHom)).hom := (Spec.map_preimage _).symm
  have hv₀ := fun i => ((ht.1 V f hf _ x₀ hx₀ _ hψ).1 i).1
  refine ⟨Matrix.of fun b i => tanEv Z.t (hv₀ i) hc₀ (ch.e b), fun K _ x hx hx' i hv hc b => ?_⟩
  have hφ : ⊤ ≤ (spMap (TangentOrigin.evalPt x _ hx') ≫ x₀) ⁻¹ᵁ (jB ⁻¹ᵁ V) := fun p _ => h₀ (Set.mem_univ _)
  have ex : spMap (TangentOrigin.evalPt x _ hx') ≫ x₀ = x := by
    refine TangentOrigin.ext_evalPt hW hφ hx' (RingHom.ext fun a => ?_)
    rw [TangentOrigin.evalPt_spMap_comp _ x₀ _ h₀ hφ, e₀]
    rfl
  change TangentOrigin.evalPt x _ hx' (tanEv Z.t (hv₀ i) hc₀ (ch.e b)) = _
  generalize TangentOrigin.evalPt x _ hx' = φ at ex
  subst ex
  have key : ∀ (y : Sp K ⟶ Z.X) (w : Sp (DualNumber K) ⟶ Z.t.G.left) (hw : IsTanAtG Z.t y w) (hy : ⊤ ≤ y ⁻¹ᵁ ch.U),
      y = spMap φ ≫ x₀ ≫ πB ≫ genι Z → w = spMap (Formalism.L2.Pj.dualMap φ) ≫ t V f hf _ x₀ hx₀ i →
      φ (tanEv Z.t (hv₀ i) hc₀ (ch.e b)) = tanEv Z.t hw hy (ch.e b) := by
    rintro y w hw hy rfl rfl
    exact (GlobalTheory.LocM.tanEv_baseChange E H _ Z.t _ _ _ hc₀ _ (hv₀ i) K φ hw hy _).symm
  exact key _ _ hv hc (Category.assoc _ _ _) (ht.2.2 V f hf _ _ φ x₀ hx₀ hx i)

end GlobalTheory.LieFilt
