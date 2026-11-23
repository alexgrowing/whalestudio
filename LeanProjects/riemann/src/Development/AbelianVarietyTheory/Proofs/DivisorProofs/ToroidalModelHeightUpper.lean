import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtIntegralPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightFirst
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieFilt

open GlobalTheory.TangentOrigin

theorem genCoord_rel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} (ρ : X ⟶ Z.X), IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) → jB ≫ ρ = πB ≫ genι Z →
    ∀ {M M' : X.Modules} {r g : ℕ} (τ : E →+* ℂ) (t : FrAssign Z M r jB) (t' : FrAssign Z M' r jB) (u : M ⟶ M'),
    IsLieFrames Z e jB πB M r τ false t → IsLieFrames Z e jB πB M' r τ false t' → Matches Z jB πB u t t' →
    ∀ (ch : VB.Chart (omega Z.t.G) g) (V : X.Opens), V ≤ ρ ⁻¹ᵁ ch.U → IsAffineOpen V →
    ∀ (f : Fin r → Γ(M, V)) (hf : VB.IsFrame f) (f' : Fin r → Γ(M', V)) (hf' : VB.IsFrame f')
      (A A' : Matrix (Fin g) (Fin r) Γ(W, jB ⁻¹ᵁ V)), GenCoord Z jB πB t ch hf A → GenCoord Z jB πB t' ch hf' A' →
    ∀ b i, A b i = ∑ j, A' b j * jB.app V ((hf'.basis le_rfl).repr (u.app V (f i)) j) := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB ρ pb hρ M M' r g τ t t' u ht ht' hm ch V hVch hV f hf f' hf' A A' hA hA' b i
  have hj : IsAffineHom jB := MorphismProperty.of_isPullback (P := @IsAffineHom) pb.flip inferInstance
  have hW : IsAffineOpen (jB ⁻¹ᵁ V) := hV.preimage jB
  let x₀ : Sp Γ(W, jB ⁻¹ᵁ V) ⟶ W := hW.fromSpec
  have h0 : ⊤ ≤ x₀ ⁻¹ᵁ (jB ⁻¹ᵁ V) := hW.fromSpec_preimage_self.ge
  have h1 : ⊤ ≤ (x₀ ≫ jB) ⁻¹ᵁ V := fun p hp => h0 hp
  have hψ : x₀ ≫ πB ≫ genStr Z ≫ spMap e.toRingHom =
      spMap (Spec.preimage (x₀ ≫ πB ≫ genStr Z ≫ spMap e.toRingHom)).hom := (Spec.map_preimage _).symm
  have hid : ∀ a, evalPt x₀ (jB ⁻¹ᵁ V) h0 a = a := by
    have e1 := eq_spec_fromSpec hW x₀ h0
    have e2 : 𝟙 _ ≫ x₀ = Spec.map (CommRingCat.ofHom (evalPt x₀ (jB ⁻¹ᵁ V) h0)) ≫ x₀ := by
      rw [Category.id_comp]; exact e1
    rw [cancel_mono] at e2
    have e3 := Spec.map_injective ((Spec.map_id _).trans e2)
    intro a
    have e4 := congrArg (fun φ => φ.hom a) e3
    simpa using e4.symm
  have hC : ⊤ ≤ (x₀ ≫ πB ≫ genι Z) ⁻¹ᵁ ch.U := by
    rw [← hρ]
    exact fun p hp => hVch (h1 hp)
  have hb := ht.1 V f hf _ x₀ h1 _ hψ
  have hb' := ht'.1 V f' hf' _ x₀ h1 _ hψ
  have hu' : ∀ j, IsTanAtG Z.t (x₀ ≫ πB ≫ genι Z) (t' V f' hf' _ x₀ h1 j) := fun j => (hb'.1 j).1
  have hc := hm V f f' hf hf' _ x₀ h1 i
  obtain ⟨hv, hev⟩ := GlobalTheory.TanSec.Norm.exists_tanEv_comb Z.t hC ch.isFrame hu' hc
  have e5 := hA _ x₀ h1 h0 i hv hC b
  have e6 : ∀ j, (A'.map (evalPt x₀ (jB ⁻¹ᵁ V) h0)) b j = tanEv Z.t (hu' j) hC (ch.e b) := fun j => hA' _ x₀ h1 h0 j (hu' j) hC b
  simp only [Matrix.map_apply, hid] at e5 e6
  rw [e5, hev b]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← e6 j, mul_comm, GlobalTheory.ArLieBase.Trans.evalPt_app jB x₀ V h1, hid, GlobalTheory.Twist.resM_self]

end GlobalTheory.LieFilt

end
