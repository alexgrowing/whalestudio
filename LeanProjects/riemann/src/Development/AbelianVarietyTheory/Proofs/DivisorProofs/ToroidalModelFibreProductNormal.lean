import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightSecond
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat

theorem coordMat_compat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} {d : ℕ}, IsArithVar q d →
    IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) →
    ∀ (M M' : X.Modules) (r : ℕ) (τ : E →+* ℂ) (t : FrAssign Z M r jB) (t' : FrAssign Z M' r jB),
    IsLieFrames Z e jB πB M r τ false t → IsLieFrames Z e jB πB M' r τ false t' →
    ∀ (U U' : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f) (f' : Fin r → Γ(M', U)) (hf' : VB.IsFrame f')
    (g : Fin r → Γ(M, U')) (hg : VB.IsFrame g) (g' : Fin r → Γ(M', U')) (hg' : VB.IsFrame g')
    (A : Matrix (Fin r) (Fin r) Γ(X, U)) (A' : Matrix (Fin r) (Fin r) Γ(X, U')),
    GlobalTheory.TwoLat.IsCoordMat Z jB πB t t' hf hf' A → GlobalTheory.TwoLat.IsCoordMat Z jB πB t t' hg hg' A' → ∀ a : Fin r,
    Twist.resM M' (inf_le_right : U ⊓ U' ≤ U') (∑ b, A' b a • g' b) =
      ∑ b, trCo hf g b a • Twist.resM M' (inf_le_left : U ⊓ U' ≤ U) (∑ k, A k b • f' k) := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB d hq hW M M' r τ t t' ht ht' U U' f hf f' hf' g hg g' hg'
    A A' hA hA' a
  have key : ∀ k, ∑ b, trCo hf' g' k b * resG X (inf_le_right : U ⊓ U' ≤ U') (A' b a) =
      ∑ b, resG X (inf_le_left : U ⊓ U' ≤ U) (A k b) * trCo hf g b a := by
    intro k
    rcases ((U ⊓ U' : X.Opens) : Set X).eq_empty_or_nonempty with hV | hV
    · have hb : U ⊓ U' = ⊥ := TopologicalSpace.Opens.coe_eq_empty.1 hV
      haveI : Subsingleton Γ(X, U ⊓ U') :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hb)
      exact Subsingleton.elim _ _
    obtain ⟨K, _, x, ψ, hψ, h, hinj⟩ := exists_generic_evalPt_injective hq hW _ hV
    have hU : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U := h.trans ((x ≫ jB).preimage_mono inf_le_left)
    have hU' : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U' := h.trans ((x ≫ jB).preimage_mono inf_le_right)
    have bf := ht.1 U f hf K x hU ψ hψ
    have bg := ht.1 U' g hg K x hU' ψ hψ
    have bf' := ht'.1 U f' hf' K x hU ψ hψ
    have bg' := ht'.1 U' g' hg' K x hU' ψ hψ
    have h1 := isCombAtG_mul Z.t _ (fun a => (bf'.1 a).1) (fun a => (bg'.1 a).1) (bg.1 a).1
      (Matrix.of fun i j => TangentOrigin.evalPt (x ≫ jB) _ h (trCo hf' g' i j)) _
      (fun i => ht'.2.1 U U' f' g' hf' hg' K x hU hU' h i) (hA' K x hU' a)
    have h2 := isCombAtG_mul Z.t _ (fun a => (bf'.1 a).1) (fun a => (bf.1 a).1) (bg.1 a).1
      (A.map (TangentOrigin.evalPt (x ≫ jB) _ hU)) _
      (fun i => hA K x hU i) (ht.2.1 U U' f g hf hg K x hU hU' h a)
    have h3 := congrFun ((bf'.2 _ (bg.1 a)).unique h1 h2) k
    apply hinj
    simp only [Matrix.of_apply, Matrix.map_apply, map_sum, map_mul] at h3 ⊢
    simp only [TangentOrigin.evalPt_res (x ≫ jB) inf_le_left hU h,
      TangentOrigin.evalPt_res (x ≫ jB) inf_le_right hU' h]
    exact h3
  refine (hf'.basis (inf_le_left : U ⊓ U' ≤ U)).ext_elem fun k => ?_
  have e1 (b : Fin r) : Twist.resM M' (inf_le_left : U ⊓ U' ≤ U) (f' b) = hf'.basis inf_le_left b :=
    (VB.IsFrame.basis_apply _ _ _).symm
  simp only [map_sum, Twist.resM_smul, e1, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have := key k
  simp only [mul_comm (trCo hf' g' k _), mul_comm _ (trCo hf g _ a)] at this
  exact this

end GlobalTheory.TwoLat

end
