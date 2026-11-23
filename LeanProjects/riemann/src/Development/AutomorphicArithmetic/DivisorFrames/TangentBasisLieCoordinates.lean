import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointPairingCompatible
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.RootFrame
open scoped NNReal
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

private theorem tan_act' {S : Type} [CommRing S] {y : Sp S ⟶ X} {w : Sp (DualNumber S) ⟶ t.G.left}
    (hw : IsTanAtG t y w) (a : 𝓞 E) : IsTanAtG t y (w ≫ (t.act.act a).left) := by
  have := t.act.hom a
  exact isTanAtG_of (ovT hw ≫ t.act.act a) (by rw [smT_post, smT_zero_ovT, MonObj.one_comp])

private theorem comb_act' {S : Type} [CommRing S] {y : Sp S ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hu : ∀ k, IsTanAtG t y (u k)) {cf : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t y u cf w) (a : 𝓞 E) :
    IsCombAtG t y (fun k => u k ≫ (t.act.act a).left) cf (w ≫ (t.act.act a).left) := by
  have := t.act.hom a
  rw [← (isCombAtG_iff t y (fun j => ovT (hu j)) _ _).1 h]
  exact (isCombAtG_iff t y (fun j => ovT (hu j) ≫ t.act.act a) _ _).2 (by rw [← combT_post]; rfl)

open GlobalTheory.FlatModel.RetractionModules in
private theorem bLie_of_comb {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] {P : PtP E p} {yb : Sp 𝓞_ℂ_[p] ⟶ X}
    {π : P.G.left ⟶ t.G.left} (hπ : IsGrpPullback P.G t.G yb π) {m : ℕ}
    {vv : Fin m → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)} {xs : Fin m → LieG P.Gt} {cf : Fin m → 𝓞_ℂ_[p]}
    {u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left} {x : LieG P.Gt} (hxs : ∀ i, ITie P π (xs i) (vv i))
    (hu : IsCombAtG t yb vv cf u) (hx : ITie P π x u) :
    P.bLie x = ∑ i, (cf i : ℂ_[p]) • P.bLie (xs i) := by
  choose xG hxc hxG using hxs
  obtain ⟨w, hw, hwu⟩ := hu
  obtain ⟨yG, hyc, hyG⟩ := hx
  have h1 : ((List.ofFn w).prod).left =
      ((List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xG i).1).prod).left ≫ π :=
    prod_left_comp hπ (T := specO 𝓞_ℂ_[p] (DualNumber 𝓞_ℂ_[p]))
      (fun i => ptMap (dualScale (cf i)) ≫ (xG i).1) w fun i => by
      rw [hw i, Over.comp_left, Category.assoc, hxG i]
      rfl
  have h2 : yG.1 = (List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xG i).1).prod :=
    hom_ext_pb hπ (hyG.trans (hwu.symm.trans h1))
  have h4 : x = combLie P.Gt m cf xs := Subtype.ext (corr_left_unique hyc (by
    rw [combLie_val, h2]
    exact corr_prod _ _ fun i => (hxc i).comp (dualScale (cf i))))
  rw [h4, bLie_combLie]

end SlopeTestRemainingChoices

theorem UpperTheory.tangent_basis_lie_coordinates :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (π : P.G.left ⟶ t.G.left), IsGrpPullback P.G t.G yb π → (∀ a, (P.oG.act a).left ≫ π = π ≫ (t.act.act a).left) → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)), IsTanBasis t yb e → ∃ x : Fin g → LieG P.Gt, (∀ k, ITie P π (x k) (e k)) ∧ ∀ (cf : Fin g → ℂ_[p]) (w : (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)), IsCombAtG t (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) (fun i => spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ e i) cf w → ∀ σ : 𝓞 E →+* ℂ_[p], IsEigG t σ w → ∀ o, P.actV o (∑ k, cf k • P.bLie (x k)) = σ o • ∑ k, cf k • P.bLie (x k) := by
  intro E _ _ _ H X t p _ _ P yb π hπ hact g e he
  have hex : ∀ k, ∃ x : LieG P.Gt, ITie P π x (e k) := fun k => by
    obtain ⟨xG, hxG⟩ := RetractionModules.tan_lift hπ (he.1 k)
    obtain ⟨x, hx⟩ := RetractionModules.exists_corr_left xG
    exact ⟨x, xG, hx, hxG⟩
  choose x hx using hex
  refine ⟨x, hx, fun cf w hw σ hσ o => ?_⟩
  have h1 : spMap (RingHom.id 𝓞_ℂ_[p]) = 𝟙 _ := Spec.map_id _
  have h3 : spMap (dualMap (RingHom.id 𝓞_ℂ_[p])) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have hb0 := he.2 𝓞_ℂ_[p] (RingHom.id _)
  simp only [h1, h3, Category.id_comp] at hb0
  choose α hα using fun k => (hb0 _ (tan_act' (he.1 k) o)).exists
  have hT : ∀ k, ITie P π (AvDefs.lieAct P.Gt P.oGt o (x k)) (e k ≫ (t.act.act o).left) := fun k => by
    obtain ⟨xG, hxc, hxG⟩ := hx k
    refine ⟨AvDefs.lieAct P.G P.oG o xG, corr_act hxc o, ?_⟩
    change (xG.1 ≫ P.oG.act o).left ≫ π = _
    rw [Over.comp_left, Category.assoc, hact, ← Category.assoc, hxG]
  have hV : ∀ k, P.actV o (P.bLie (x k)) = ∑ j, (α k j : ℂ_[p]) • P.bLie (x j) := fun k => by
    rw [← P.bLie_act]
    exact bLie_of_comb hπ hx (hα k) (hT k)
  have he' := fun k => GlobalTheory.FactorDepth.isTanAtG_map t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) (he.1 k)
  have c1 := tanLinG _ he' (fun k => (spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ e k) ≫ (t.act.act o).left)
    (Matrix.of fun j k => algebraMap 𝓞_ℂ_[p] ℂ_[p] (α k j)) cf _
    (fun k => by
      rw [Category.assoc]
      exact GlobalTheory.LatDRFree.comb_map t _ (hα k)) (comb_act' he' hw o)
  have c2 := GlobalTheory.ShFam.Pad.Guard.comb_smul he' hw (σ o)
  rw [← hσ o] at c2
  have c3 := (he.2 _ _ _ (GlobalTheory.ShFam.Pad.Guard.comb_tan he' c2)).unique c1 c2
  rw [map_sum, Finset.smul_sum]
  simp only [map_smul, hV, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← congrFun c3 j]
  congr 1
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _
