import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModelChart

theorem exists_open_isDomain (X : Scheme.{0}) [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ ∀ U : X.Opens, x ∈ U → U ≤ W → IsDomain Γ(X, U) := by
  let Z : irreducibleComponents X := ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
  refine ⟨GlobalTheory.IsNormalScheme.component Z, mem_irreducibleComponent, fun U hx hU => ?_⟩
  have : Nonempty U.toScheme := ⟨⟨x, hx⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion (X.homOfLE hU)
  have e : Γ(U.toScheme, ⊤) ≅ Γ(X, U) := U.topIso
  exact e.commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain _

theorem res_mem_secOn {X : Scheme.{0}} (L : LB X) {V W : X.Opens} (h : W ≤ V) {θ : ∀ i, Γ(X, V ⊓ L.U i)}
    (hθ : θ ∈ secOn L V) : (fun i => resG X (inf_le_inf_right _ h) (θ i)) ∈ secOn L W := by
  intro i j
  have e := congrArg (resG X (inf_le_inf_right _ (inf_le_inf_right _ h) :
    W ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hθ i j)
  rw [map_mul] at e
  simpa only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp] using e

theorem isTangent_comp_hom {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {v : epsR R ⟶ G} (hv : IsTangent v)
    (a : G ⟶ G) [IsMonHom a] : IsTangent (v ≫ a) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem spMap_dualMapR_id (R : Type) [CommRing R] :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (RingHom.id R)) = 𝟙 _ := by
  have : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  rw [this]
  exact Spec.map_id _

theorem exists_chart_lieBasis_matrices :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L → ∀ x : Y.X, ∃ (U : Y.X.Opens) (hU : IsAffineOpen U), x ∈ U ∧ IsDomain Γ(Y.X, U) ∧ (∃ θ ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ U), ∀ y ∈ U, ∃ (g : Y.t.G.left) (i : Y.t.PP.L.ι), Y.t.G.hom g = y ∧ g ∈ Y.t.G.left.basicOpen (θ i)) ∧ ∃ (n : ℕ) (v₀ : Fin n → (Sp (DualNumber Γ(Y.X, U)) ⟶ Y.t.G.left)) (ρ : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U)), ∀ (R' : Type) [CommRing R'] (f : Γ(Y.X, U) →+* R') (t' : SAB H (Sp R')) (m : SABMap t' Y.t (spMap f ≫ hU.fromSpec)), ∃ v' : Fin n → (epsR R' ⟶ t'.G), (∀ j, (v' j).left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v' ∧ ∀ a j, IsLieComb (fun i => f (ρ a i j)) v' (v' j ≫ t'.act.act a) := by
  intro E _ _ _ H D l Xo c O _ _ β Y hP x
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := Y.t.semi.smooth
  obtain ⟨W, hxW, hW⟩ := exists_open_isDomain Y.X x
  obtain ⟨V, hxV, θ, hθ, -, nz⟩ := hP x
  obtain ⟨U, hU, hxU, hUW, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Y.X Y.t.G x (W ⊓ V) ⟨hxW, hxV⟩
  have hUV : U ≤ V := hUW.trans inf_le_right
  refine ⟨U, hU, hxU, hW U hxU (hUW.trans inf_le_left),
    ⟨_, res_mem_secOn _ (Y.t.G.hom.preimage_mono hUV) hθ, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨g, i, rfl, hg⟩ := nz y (hUV hy)
    refine ⟨g, i, rfl, ?_⟩
    show g ∈ Y.t.G.left.basicOpen (Y.t.G.left.presheaf.map (homOfLE _).op (θ i))
    rw [Scheme.basicOpen_res]
    exact ⟨⟨hy, (Y.t.G.left.basicOpen_le _ hg).2⟩, hg⟩
  obtain ⟨t₀, ⟨m₀⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y).2.1 (Sp Γ(Y.X, U)) hU.fromSpec
  have c₀ : IsGrpPullback t₀.G Y.t.G (spMap (RingHom.id Γ(Y.X, U)) ≫ hU.fromSpec) m₀.φ := by
    have e : spMap (RingHom.id Γ(Y.X, U)) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp]
    exact m₀.cart
  obtain ⟨u, hu, hb⟩ := hv _ (RingHom.id _) t₀.G m₀.φ c₀
  simp only [spMap_dualMapR_id, Category.id_comp] at hu
  have ex : ∀ a j, ∃ r : Fin n → Γ(Y.X, U), IsLieComb r u (u j ≫ t₀.act.act a) := fun a j =>
    have := t₀.act.hom a
    (hb.2 _ (isTangent_comp_hom (hb.1 j) _)).exists
  choose r hr using ex
  refine ⟨n, v₀, fun a i j => r a j i, fun R' _ f t' m => ?_⟩
  obtain ⟨v', hv', hb'⟩ := hv R' f t'.G m.φ m.cart
  refine ⟨v', hv', hb', fun a j => ?_⟩
  have hp := m₀.cart.1
  let F : t'.G.left ⟶ t₀.G.left := hp.lift m.φ (t'.G.hom ≫ spMap f) (by rw [m.cart.1.w, Category.assoc])
  have hF : F ≫ m₀.φ = m.φ := hp.lift_fst _ _ _
  have hw : F ≫ t₀.G.hom = t'.G.hom ≫ spMap f := hp.lift_snd _ _ _
  have hc : IsGrpPullback t'.G t₀.G (spMap f) F := m₀.cart.cancel (hF ▸ m.cart) hw
  have lies : ∀ (w' : epsR R' ⟶ t'.G) (w : epsR Γ(Y.X, U) ⟶ t₀.G),
      w'.left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left ≫ m₀.φ →
      w'.left ≫ F = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left := fun w' w h => by
    apply hp.hom_ext
    · rw [Category.assoc, hF, h, Category.assoc]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (GlobalTheory.LieCombBaseChange.dualMap_over f).symm
  refine (GlobalTheory.lieComb_baseChange _ _ f t₀.G t'.G F hc n u _ (r a j) v' _
    (fun k => lies _ _ (by rw [hv', hu])) (hr a j)).1 (lies _ _ ?_)
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, m.act, m₀.act, ← Category.assoc, hv',
    ← Category.assoc (u j).left, hu, Category.assoc]

end GlobalTheory.ModelChart
