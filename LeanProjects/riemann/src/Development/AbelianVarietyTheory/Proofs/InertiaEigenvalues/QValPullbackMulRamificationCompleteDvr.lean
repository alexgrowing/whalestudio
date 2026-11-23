import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsValGenHasVal
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
open ReciprocityTheory.ChartRestriction.G.DVR (HasVal GenHasVal wchart_le_preimage)

noncomputable section

namespace GlobalTheory.QValPull

theorem chart_eq_of_val {V : Type} [CommRing V] [IsDomain V] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {φ : PUnit → (Spec (CommRingCat.of V) ⟶ X)} {φ' : PUnit → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    (hφ : ∀ k, φ' k = jK V ≫ φ k) {ε : PUnit → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)}
    {e : LB.Gen (LB.LinComb L φ ε)} {c : FractionRing V}
    (h : ∀ (z : Spec (CommRingCat.of (FractionRing V))) (J : (Spec (CommRingCat.of (FractionRing V)) ⟶ X) → L.ι),
      Good L z J → (val t (𝟙 _) z J).val =
        gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) * (val e (𝟙 _ ≫ jK V) z J).val)
    (j : PUnit → L.ι) :
    (t.s j).val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j))).val := by
  apply fn_ext
  intro x hx
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL x φ' j (fun a b _ => by cases a; cases b; rfl)
    (fun k => LB.wchart_le L φ' j k hx)
  have h1 : ∀ k, J (𝟙 _ ≫ φ' k) = j k := fun k => by rw [Category.id_comp]; exact hJj k
  have h2 : ∀ k, J ((𝟙 _ ≫ jK V) ≫ φ k) = j k := fun k => by rw [Category.id_comp, ← hφ]; exact hJj k
  have eL : gs (𝟙 _) x _ (t.s j).val = (val t (𝟙 _) x J).val :=
    (gs_unit _ x _ hx _).trans (congrArg Units.val (val_of t (𝟙 _) x J j h1).symm)
  rw [eL, h x J hJ]
  refine Eq.trans ?_ (gs_mul _ x _ hx _ _).symm
  congr 1
  · exact (gs_res _ x _ hx _).symm
  · have hx' : x ∈ LB.wchart L φ' j := hx
    have hxe : x ∈ jK V ⁻¹ᵁ LB.wchart L φ j := wchart_le_preimage L (jK V) φ φ' hφ j hx'
    unfold res pullU
    simp only [Units.coe_map, MonoidHom.coe_coe]
    refine Eq.symm ((gs_res _ x _ hx _).trans ((gs_pull (𝟙 _) (jK V) x _ hxe _).trans
      ((gs_unit (𝟙 _ ≫ jK V) x _ hxe _).trans ?_)))
    exact congrArg Units.val (val_of e _ x J j h2).symm

theorem hasVal_fracMap {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] {g : V →+* V'}
    (hg : Function.Injective g) {ϖ : V} {ϖ' : V'} {e : ℕ} (ha : Associated (g ϖ) (ϖ' ^ e))
    {c : FractionRing V} {n : ℤ} (hc : HasVal ϖ c n) : HasVal ϖ' (ArcPull.fracMap hg c) (e * n) := by
  obtain ⟨u, rfl⟩ := hc
  obtain ⟨v, hv⟩ := ha
  refine ⟨v⁻¹ ^ n * Units.map (g : V →* V') u, ?_⟩
  have hϖ : g ϖ = ϖ' ^ e * ((v⁻¹ : V'ˣ) : V') := by
    rw [← hv, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  have key : ∀ (w : V'ˣ) (m : ℤ), algebraMap V' (FractionRing V') ((w ^ m : V'ˣ) : V') =
      algebraMap V' (FractionRing V') (w : V') ^ m := by
    intro w m
    have h1 := Units.coe_map (algebraMap V' (FractionRing V') : V' →* FractionRing V') (w ^ m)
    rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map] at h1
    simpa only [MonoidHom.coe_coe] using h1.symm
  rw [map_mul, map_zpow₀, ArcPull.fracMap_algebraMap, ArcPull.fracMap_algebraMap, hϖ, Units.val_mul, map_mul,
    map_mul, map_pow, key, mul_zpow, ← zpow_natCast, ← zpow_mul]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  ring

theorem gs_scal_spMap {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (z : Spec (CommRingCat.of K')) (c : K) :
    gs (spMap f) z ⊤ (scal (𝟙 (Spec (CommRingCat.of K))) c) =
      gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of K'))) (f c)) := by
  unfold gs scal spMap
  simp only [TopologicalSpace.Opens.mem_top, ↓reduceDIte]
  have hn := congrArg (fun φ => CommRingCat.Hom.hom φ c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  rw [hn]
  rfl

theorem qVal_pull {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    {g : V →+* V'} {D : DegPre V} {D' : DegPre V'} (hD : IsPullDeg g D D') {ϖ : V} {ϖ' : V'} {e : ℕ}
    (hg : Function.Injective g) (ha : Associated (g ϖ) (ϖ' ^ e)) (y : D'.X) (n : ℤ) (h : QVal D ϖ (hD.xe y) n) :
    QVal D' ϖ' y (e * n) := by
  obtain ⟨e0, he0, c0, hc0, hch⟩ := h
  obtain ⟨e', he', hdown⟩ := ArcPull.exists_down_om hD.w_gen D.P.isLB D'.P.isLB (spMap g)
    (fun _ : PUnit => hD.c_pr y) e0 he0
  refine ⟨e', he', ArcPull.fracMap hg c0, hasVal_fracMap hg ha hc0, ?_⟩
  refine chart_eq_of_val D'.P.isLB (fun _ => DVR.QForm.ptK_eq D' y) ?_
  intro z J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good D.P.L D.P.isLB z (fun k : Empty => k.elim) (fun k : Empty => k.elim)
    (fun a => a.elim) (fun k => k.elim)
  have hv := DVR.SectionScalarValuation.val_genHasVal (hφ := fun _ => DVR.QForm.ptK_eq D (hD.xe y)) hch (ArcPull.genMap hg) z hJ
  have hp := ArcPull.psi_val hD (ArcPull.genMap hg) (𝟙 (Spec (CommRingCat.of (FractionRing V')))) (ArcPull.fracMap_sq hg) hJ hJ' y
  have hd := hdown _ (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') z J J' hJ hJ'
  have hr : ArcPull.genMap hg ≫ jK V = (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') ≫ spMap g := by
    rw [← ArcPull.fracMap_sq hg, Category.assoc]
    rfl
  have hxk : (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ D'.xK y) = (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') ≫ (D'.c y).left := by
    rw [Category.assoc]
    exact congrArg _ (DVR.QForm.ptK_eq D' y)
  rw [hp, hr, hd] at hv
  simp only [Fintype.prod_unique, zpow_neg, zpow_one] at hv
  rw [← hxk, show ArcPull.genMap hg = spMap (ArcPull.fracMap hg) from rfl, gs_scal_spMap] at hv
  generalize ArcPull.om hD.w z J J' (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ D'.xK y) = o at hv
  generalize val (D'.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing V')))) z J' = A at hv ⊢
  generalize val e' (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') z J' = E at hv ⊢
  generalize gs (𝟙 (Spec (CommRingCat.of (FractionRing V')))) z ⊤ (scal (𝟙 _) (ArcPull.fracMap hg c0)) = G at hv ⊢
  rw [Units.val_mul, Units.val_mul] at hv
  linear_combination o.val * hv + (G * E.val - A.val) * Units.mul_inv o

theorem main : ∀ (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (D : DegPre T.V) (D' : DegPre T'.V) (hD : IsPullDeg g D D')
    (ϖ : T.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g → Irreducible ϖ → Irreducible ϖ' →
    Associated (g ϖ) (ϖ' ^ e) → ∀ (y : D'.X) (n : ℤ), QVal D ϖ (hD.xe y) n → QVal D' ϖ' y (e * n) := by
  intro T T' g D D' hD ϖ ϖ' e hg _ _ ha y n h
  exact qVal_pull hD hg ha y n h

end GlobalTheory.QValPull
