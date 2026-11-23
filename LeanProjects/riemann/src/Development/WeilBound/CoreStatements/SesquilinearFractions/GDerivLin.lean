import Development.WeilBound.CoreStatements.SesquilinearFractions.RetractionTwoProjectionOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartX
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.TwoTangentVectors

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] (x : Sp ℂ ⟶ X)

instance : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom q)) := inferInstanceAs (IsLocalHom q)

abbrev epsPart {Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(Y, U)) : ℂ :=
  TrivSqZeroExt.snd (show DualNumber ℂ from
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE U ⊤ h).hom f))

theorem preimage_open_eq_top_of_closed_point {Y : Scheme.{0}} (F : Spec (CommRingCat.of D2) ⟶ Y) (U : Y.Opens)
    (hc : IsLocalRing.closedPoint D2 ∈ F ⁻¹ᵁ U) : ⊤ ≤ F ⁻¹ᵁ U :=
  fun p _ => (IsLocalRing.specializes_closedPoint p).mem_open (F ⁻¹ᵁ U).isOpen hc

theorem epsPart_comp {Y : Scheme.{0}} (χ : D2 →+* DualNumber ℂ) (F : Spec (CommRingCat.of D2) ⟶ Y) (U : Y.Opens)
    (hF : ⊤ ≤ F ⁻¹ᵁ U) (f : Γ(Y, U)) : ∀ (φ : Sp (DualNumber ℂ) ⟶ Y) (hφ : φ = spMap χ ≫ F) (h : ⊤ ≤ φ ⁻¹ᵁ U),
      epsPart φ U h f = (χ ((Scheme.ΓSpecIso (CommRingCat.of D2)).hom.hom ((F.appLE U ⊤ hF).hom f))).snd := by
  intro φ hφ h
  subst hφ
  have := ConcreteCategory.congr_hom (ReciprocityTheory.ChartRestriction.G.PullbackSections.specMap_comp_appLE (CommRingCat.ofHom χ) F U h hF) f
  simp only [ConcreteCategory.comp_apply] at this
  simp only [epsPart]
  erw [this]
  rfl

theorem epsPart_mul {v v' : epsAt x ⟶ G} (hv : IsTanAt G x v) (hv' : IsTanAt G x v') (U : G.left.Opens)
    (h : ⊤ ≤ (v * v').left ⁻¹ᵁ U) (h1 : ⊤ ≤ v.left ⁻¹ᵁ U) (h2 : ⊤ ≤ v'.left ⁻¹ᵁ U) (f : Γ(G.left, U)) :
    epsPart (v * v').left U h f = epsPart v.left U h1 f + epsPart v'.left U h2 f := by
  obtain ⟨F, hF0⟩ : ∃ F : Spec (CommRingCat.of D2) ⟶ G.left, F = (V2 x v v').left := ⟨_, rfl⟩
  have eQ : (v * v').left = spMap q ≫ F := by rw [hF0, ← quotient_tangent_product x v v']; rfl
  have e1 : v.left = spMap r1 ≫ F := by
    rw [hF0]
    conv_lhs => rw [← retraction_one_tangent_sum x (v := v) hv']
    rfl
  have e2 : v'.left = spMap r2 ≫ F := by
    rw [hF0]
    conv_lhs => rw [← retraction_two_tangent_sum x (v' := v') hv]
    rfl
  have hF : ⊤ ≤ F ⁻¹ᵁ U := by
    apply preimage_open_eq_top_of_closed_point
    have hm : IsLocalRing.closedPoint (DualNumber ℂ) ∈ (spMap q ≫ F) ⁻¹ᵁ U :=
      eQ ▸ h (show IsLocalRing.closedPoint (DualNumber ℂ) ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    have hm2 : (spMap q) (IsLocalRing.closedPoint (DualNumber ℂ)) ∈ F ⁻¹ᵁ U := hm
    rw [spMap, Spec_closedPoint] at hm2
    exact hm2
  rw [epsPart_comp q F U hF f _ eQ h, epsPart_comp r1 F U hF f _ e1 h1, epsPart_comp r2 F U hF f _ e2 h2, q_snd]

theorem top_le_of_fst {Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ Y) (y0 : Sp ℂ ⟶ Y)
    (hv : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = y0) (U : Y.Opens) (hU : ⊤ ≤ y0 ⁻¹ᵁ U) : ⊤ ≤ v ⁻¹ᵁ U := by
  apply ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.dual_top_le
  subst hv
  have hm : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (IsLocalRing.closedPoint ℂ) ∈ v ⁻¹ᵁ U :=
    hU (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  rw [spMap, Spec_closedPoint] at hm
  exact hm

theorem epsMul_eq (c : ℂ) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul c = GlobalTheory.CompanionTheory.Ar.epsMul c := rfl

def rhoTy {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) :
    𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a :=
    { toFun := fun w k => ty k (a : E) * w k
      map_add' := fun w w' => by funext k; simp [mul_add]
      map_smul' := fun c w => by funext k; simp; ring }
  map_one' := by ext w k; simp
  map_mul' a b := by ext w k; simp; push_cast; ring
  map_zero' := by ext w k; simp
  map_add' a b := by ext w k; simp [add_mul]

end PositivityTheory.Xgf.TwoTangentVectors

namespace PositivityTheory.Xgf

open TwoTangentVectors in
theorem lie_model_with_cm_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsPeriod (FU.Di i) ty P → ∃ (M : LieModel Xo.univ.t.G (FU.u i P) (Fin g → ℂ)) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), M.IsActOf Xo.univ.t.act.act ρ ∧ (∀ a w, ρ a w = fun k => ty k (a : E) * w k) ∧ (∀ w, IsDerivAt0 (fun z => (FU.ex i P z).left) w (M.pt w).left) ∧ ∀ τ w, HT.eigProj ρ τ w = tyPart ty τ w := by
  intro E _ _ _ H D l Xo c g ty FU i P hP
  classical
  have hd := FU.ex_diff i P hP
  have ex0 : FU.ex i P 0 = 1 := by
    have := FU.ex_add i P hP 0 0
    rw [add_zero] at this
    exact left_eq_mul.mp this
  choose pt hpt using fun w => (hd.1 w).exists
  have huniq : ∀ w (v : epsAt (FU.u i P) ⟶ Xo.univ.t.G), IsDerivAt0 (fun z => (FU.ex i P z).left) w v.left → v = pt w :=
    fun w v hv => (hd.1 w).unique hv (hpt w)
  have htan : ∀ w, IsTanAt Xo.univ.t.G (FU.u i P) (pt w) := fun w =>
    (hpt w).1.trans (congrArg Over.Hom.left ex0)
  have hmul : ∀ w w', IsDerivAt0 (fun z => (FU.ex i P z).left) (w + w') (pt w * pt w').left := by
    intro w w'
    have ht := LieTangent.isTanAt_mul (htan w) (htan w')
    refine ⟨ht.trans (congrArg Over.Hom.left ex0).symm, fun U h f => ?_⟩
    have he0 : ∀ v : epsAt (FU.u i P) ⟶ Xo.univ.t.G, IsTanAt Xo.univ.t.G (FU.u i P) v →
        spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (FU.ex i P 0).left := fun v hv =>
      hv.trans (congrArg Over.Hom.left ex0).symm
    have hU : ⊤ ≤ (FU.ex i P 0).left ⁻¹ᵁ U := by
      rw [← he0 _ ht]
      intro p _
      exact h trivial
    have h1 := top_le_of_fst _ _ (he0 _ (htan w)) U hU
    have h2 := top_le_of_fst _ _ (he0 _ (htan w')) U hU
    have := epsPart_mul (FU.u i P) (htan w) (htan w') U h h1 h2 f
    simp only [epsPart] at this
    rw [this, (hpt w).2 U h1 f, (hpt w').2 U h2 f, map_add]
  let M : LieModel Xo.univ.t.G (FU.u i P) (Fin g → ℂ) :=
    { pt := pt
      tan := htan
      inj := fun w w' e' => by
        obtain ⟨w'', -, hw''⟩ := hd.2 (pt w) ((htan w).trans (congrArg Over.Hom.left ex0).symm)
        exact (hw'' w (hpt w)).trans (hw'' w' (e' ▸ hpt w')).symm
      onto := fun v hv => by
        obtain ⟨w, hw, -⟩ := hd.2 v (hv.trans (congrArg Over.Hom.left ex0).symm)
        exact ⟨w, (huniq w v hw).symm⟩
      add := fun w w' => (huniq (w + w') _ (hmul w w')).symm
      smul := fun c w => by
        have := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul (hpt w) c
        exact ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (hpt (c • w)) this }
  have hhol : ReciprocityTheory.ChartRestriction.G.PullbackSections.IsHolFam (fun z => (FU.ex i P z).left) := ReciprocityTheory.ChartRestriction.G.PullbackSections.anHol FU i P hP
  refine ⟨M, rhoTy ty, fun a w => ?_, fun a w => rfl, fun w => hpt w, fun τ w => ?_⟩
  ·
    apply Over.OverMorphism.ext
    show (pt (rhoTy ty a w)).left = (pt w).left ≫ (Xo.univ.t.act.act a).left
    have hA := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_lin hhol (ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.tyD ty a) (hpt (rhoTy ty a w))
    have hB := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom (hpt w) (Xo.univ.t.act.act a).left
    have hfun : (fun z => (FU.ex i P z).left ≫ (Xo.univ.t.act.act a).left) =
        fun z => (FU.ex i P (ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.tyD ty a z)).left := funext fun z => by
      rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.tyD_apply, FU.ex_lin i P hP a z]
      rfl
    rw [hfun] at hB
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique hA hB
  ·
    have hmem : ∀ j, (Pi.single j 1 : Fin g → ℂ) ∈ HT.eigSp (rhoTy ty) (ty j) := by
      intro j
      rw [HT.LatBasic.mem_eigSp]
      intro a
      funext k
      by_cases hk : k = j
      · subst hk; simp [rhoTy]
      · simp [rhoTy, Pi.single_apply, hk]
    have hproj : ∀ j, HT.eigProj (rhoTy ty) τ (Pi.single j 1) = if ty j = τ then Pi.single j 1 else 0 := by
      intro j
      split_ifs with hj
      · rw [← hj]; exact HT.LatBasic.eigProj_of_mem (hmem j)
      · exact HT.LatBasic.eigProj_of_ne (fun h => hj h.symm) (hmem j)
    have hw : w = ∑ j, w j • (Pi.single j 1 : Fin g → ℂ) := by
      funext k; simp [Pi.single_apply]
    conv_lhs => rw [hw, map_sum]
    simp only [map_smul, hproj]
    funext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp only [tyPart, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    · intro b _ hb
      split_ifs <;> simp [Pi.single_apply, Ne.symm hb]
    · simp

end PositivityTheory.Xgf
