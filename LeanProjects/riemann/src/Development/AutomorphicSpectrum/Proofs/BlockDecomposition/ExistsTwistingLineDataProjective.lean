import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLineDataTwistingSheaf
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CompanionTheory.LineCech (pl pl_pl pl_congr pullC isLB_pullC toLine uc uc_of_charts fc Yc ι_fc)

namespace GlobalTheory.CompanionTheory.ConeTwistingSheafMap

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R] {N : ℕ}

theorem awayToSection_ratio (j k : Fin (N + 1)) :
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X j)).hom (ratio R N j k) =
      GlobalTheory.ProjSpace.ratio R N j k := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  have e := ProjectiveSpectrum.Proj.awayToSection_apply (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (MvPolynomial.X j) (ratio R N j k) x
  refine e.trans ?_
  change _ = Localization.mk (MvPolynomial.X k) ⟨MvPolynomial.X j, x.2⟩
  rw [ratio, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    Localization.mk_eq_mk']
  congr 1
  exact Subtype.ext (pow_one _)

theorem appLE_ι_top {Z : Scheme.{0}} {U : Z.Opens} {g : U.toScheme ⟶ Z} (hg : g = U.ι) (e : ⊤ ≤ g ⁻¹ᵁ U) :
    g.appLE U ⊤ e = U.topIso.inv := by
  subst hg
  simp only [Scheme.Hom.appLE, Scheme.Opens.ι_app, Scheme.Opens.topIso_inv]
  exact (Z.presheaf.map_comp _ _).symm.trans (congrArg Z.presheaf.map (Subsingleton.elim _ _))

theorem chart_appLE (j : Fin (N + 1)) (y : ChartR R N j) (e) :
    ((chart R N j).appLE (GlobalTheory.ProjSpace.chart R N j) ⊤ e).hom
      ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X j)).hom y) =
      (Scheme.ΓSpecIso (CommRingCat.of (ChartR R N j))).inv.hom y := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R
  let B := Proj.basicOpenToSpec 𝒜 (MvPolynomial.X j)
  have hiso : IsIso B := (Proj.basicOpenIsoSpec 𝒜 (MvPolynomial.X j) (X_mem R N j) one_pos).isIso_hom
  have hinj : Function.Injective B.appTop.hom :=
    (ConcreteCategory.bijective_of_isIso B.appTop).1
  apply hinj
  have hB := congr($(Proj.basicOpenToSpec_app_top 𝒜 (MvPolynomial.X j)) ((Scheme.ΓSpecIso _).inv y))
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hB
  have hc : B ≫ chart R N j = (GlobalTheory.ProjSpace.chart R N j).ι := by
    change (Proj.basicOpenIsoSpec 𝒜 _ (X_mem R N j) one_pos).hom ≫
      (Proj.basicOpenIsoSpec 𝒜 _ (X_mem R N j) one_pos).inv ≫ _ = _
    rw [Iso.hom_inv_id_assoc]
  have h1 : ∀ t, B.appTop.hom (((chart R N j).appLE (GlobalTheory.ProjSpace.chart R N j) ⊤ e).hom t) =
      ((GlobalTheory.ProjSpace.chart R N j).topIso.inv).hom t := by
    intro t
    have h2 := Scheme.Hom.appLE_comp_appLE B (chart R N j) (GlobalTheory.ProjSpace.chart R N j) ⊤ ⊤ e le_top
    have h3 : B.appTop = B.appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE ..
    rw [h3, ← CommRingCat.comp_apply, h2]
    exact congrArg (fun φ => φ.hom t) (appLE_ι_top hc _)
  rw [h1]
  exact hB.symm

instance isOpenImmersion_chart (j : Fin (N + 1)) : IsOpenImmersion (chart R N j) := by
  unfold chart
  infer_instance

theorem comp_ι_fc {X W : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (l : L.ι) (c : W ⟶ (L.U l).toScheme) :
    (c ≫ Sigma.ι (fun i => (L.U i).toScheme) l) ≫ fc L = c ≫ (L.U l).ι := by
  rw [Category.assoc, ι_fc]

theorem pull_ratio {V : Scheme.{0}} (j k : Fin (N + 1)) (x : V ⟶ Spec (CommRingCat.of (ChartR R N j)))
    (e : ⊤ ≤ (x ≫ chart R N j) ⁻¹ᵁ (GlobalTheory.ProjSpace.chart R N j ⊓ GlobalTheory.ProjSpace.chart R N k)) :
    ((pl (x ≫ chart R N j) e (GlobalTheory.ProjSpace.ratioUnit _ j k inf_le_left inf_le_right) : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) =
      x.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (ChartR R N j))).inv.hom (ratio R N j k)) := by
  have e0 : (⊤ : (Spec (CommRingCat.of (ChartR R N j))).Opens) ≤ chart R N j ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j := by
    have : (chart R N j).opensRange = GlobalTheory.ProjSpace.chart R N j := Proj.opensRange_awayι _ _ _ _
    rw [← this]
    exact fun y _ => ⟨y, rfl⟩
  rw [← chart_appLE j _ e0, awayToSection_ratio]
  have h1 : (GlobalTheory.ProjSpace.ratioUnit (GlobalTheory.ProjSpace.chart R N j ⊓ GlobalTheory.ProjSpace.chart R N k) j k inf_le_left inf_le_right :
      Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N j ⊓ GlobalTheory.ProjSpace.chart R N k)) =
      ((PSpace R N).presheaf.map (homOfLE inf_le_left).op).hom (GlobalTheory.ProjSpace.ratio R N j k) := rfl
  change ((x ≫ chart R N j).appLE _ ⊤ e).hom _ = _
  rw [h1, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have h2 := Scheme.Hom.appLE_comp_appLE x (chart R N j) (GlobalTheory.ProjSpace.chart R N j) ⊤ ⊤ e0 le_top
  have h3 : x.appTop = x.appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE ..
  rw [h3, ← CommRingCat.comp_apply, h2]

theorem range_fst_le {X : Scheme.{0}} (i : X ⟶ PSpace R N) (j : Fin (N + 1)) :
    Set.range (pullback.fst i (chart R N j)) ⊆ Set.range (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j).ι := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  change i (pullback.fst i (chart R N j) z) ∈ GlobalTheory.ProjSpace.chart R N j
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have : (chart R N j).opensRange = GlobalTheory.ProjSpace.chart R N j := Proj.opensRange_awayι _ _ _ _
  rw [← this]
  exact ⟨_, rfl⟩

theorem uc_congr {X V : Scheme.{0}} {L : ReciprocityTheory.ChartRestriction.G.Semi.LB X} {a a' b b' : V ⟶ Yc L} (ha : a = a') (hb : b = b')
    (h : a ≫ fc L = b ≫ fc L) (h' : a' ≫ fc L = b' ≫ fc L) : uc h = uc h' := by
  subst ha hb
  rfl

theorem main : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace R N), ∃ D : E.LineData X, IsTautologicalLineAt D N i := by
  intro R _ X N i
  let L := pullC (GlobalTheory.ProjSpace.O1 R N) i
  let hL : L.IsLB := isLB_pullC (GlobalTheory.ProjSpace.O1_isLB R N) i
  let t : ∀ j : Fin (N + 1), pullback i (chart R N j) ⟶ (L.U j).toScheme := fun j =>
    IsOpenImmersion.lift (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j).ι (pullback.fst i (chart R N j)) (range_fst_le i j)
  have ht : ∀ j, t j ≫ (L.U j).ι = pullback.fst i (chart R N j) := fun j => IsOpenImmersion.lift_fac _ _ _
  refine ⟨toLine L hL, ?_, fun j => t j ≫ Sigma.ι (fun j => (L.U j).toScheme) j, ?_⟩
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
  · have hs : ∀ j, (t j ≫ Sigma.ι (fun j => (L.U j).toScheme) j) ≫ (toLine L hL).f = pullback.fst i (chart R N j) :=
      fun j => by
        change (t j ≫ Sigma.ι (fun j => (L.U j).toScheme) j) ≫ fc L = _
        rw [Category.assoc, ι_fc, ht]
    refine ⟨hs, fun V j k a b h => ?_⟩
    have hca : (a ≫ t j) ≫ (L.U j).ι = a ≫ pullback.fst i (chart R N j) := by rw [Category.assoc, ht]
    have hcb : (b ≫ t k) ≫ (L.U k).ι = b ≫ pullback.fst i (chart R N k) := by rw [Category.assoc, ht]
    have hfc : ((a ≫ t j) ≫ Sigma.ι (fun j => (L.U j).toScheme) j) ≫ fc L =
        ((b ≫ t k) ≫ Sigma.ι (fun j => (L.U j).toScheme) k) ≫ fc L := by
      exact (comp_ι_fc L j (a ≫ t j)).trans (hca.trans (h.trans (hcb.symm.trans (comp_ι_fc L k (b ≫ t k)).symm)))
    have e : ⊤ ≤ ((a ≫ t j) ≫ (L.U j).ι) ⁻¹ᵁ (L.U j ⊓ L.U k) := fun v _ => by
      refine ⟨((a ≫ t j) v).2, ?_⟩
      change (((a ≫ t j) ≫ (L.U j).ι) v) ∈ L.U k
      rw [hca, h, ← hcb]
      exact ((b ≫ t k) v).2
    have h1 := uc_of_charts (L := L) (a ≫ t j) (b ≫ t k) hfc e
    have hx : ((a ≫ t j) ≫ (L.U j).ι) ≫ i = (a ≫ pullback.snd i (chart R N j)) ≫ chart R N j := by
      rw [hca, Category.assoc, Category.assoc, pullback.condition]
    have e2 : ⊤ ≤ ((a ≫ pullback.snd i (chart R N j)) ≫ chart R N j) ⁻¹ᵁ
        (GlobalTheory.ProjSpace.chart R N j ⊓ GlobalTheory.ProjSpace.chart R N k) := fun v hv => by
      rw [← hx]
      exact e hv
    have h2 : (uc hfc) = pl ((a ≫ pullback.snd i (chart R N j)) ≫ chart R N j) e2
        (GlobalTheory.ProjSpace.ratioUnit _ j k inf_le_left inf_le_right) := by
      rw [h1]
      change pl _ e (pl i _ ((GlobalTheory.ProjSpace.O1 R N).g j k)) = _
      rw [pl_pl, pl_congr hx]
      rfl
    rw [← pull_ratio j k _ e2, ← h2]
    have hfc' : (a ≫ t j ≫ Sigma.ι (fun j => (L.U j).toScheme) j) ≫ fc L =
        (b ≫ t k ≫ Sigma.ι (fun j => (L.U j).toScheme) k) ≫ fc L := by
      rw [← Category.assoc a, ← Category.assoc b]
      exact hfc
    exact congrArg Units.val (uc_congr (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm hfc' hfc)

end GlobalTheory.CompanionTheory.ConeTwistingSheafMap
