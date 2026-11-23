import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpenStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.RegCrit

theorem isUnit_eval_iff {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (t : Sp R ⟶ X) {W : X.Opens}
    (h : ⊤ ≤ t ⁻¹ᵁ W) (g : Γ(X, W)) :
    IsUnit ((t.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom g) ↔
      t (IsLocalRing.closedPoint R) ∈ X.basicOpen g := by
  have hU : t (IsLocalRing.closedPoint R) ∈ W := h trivial
  have e : X.presheaf.germ W _ hU ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of R) t =
      t.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [← e, X.mem_basicOpen g _ hU]
  exact isUnit_map_iff (Scheme.stalkClosedPointTo (R := CommRingCat.of R) t).hom _

theorem isUnit_of_one_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (c : e.O)
    (hc : 1 ≤ e.w c) : IsUnit c := by
  have h0 : (c : AlgebraicClosure F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact absurd hc (by norm_num)
  have h1 : (c : AlgebraicClosure F)⁻¹ ∈ e.O := by
    rw [e.mem_O, map_inv₀]
    exact inv_le_one_of_one_le₀ hc
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ h0))

theorem regAt_of_integral_values : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : TrueGeo.Model Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X → haveI := N.ar.isIntegral; ∀ (U : N.X.Opens) (f : N.X.functionField), (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X), spMap e.O.subtype ≫ yt = y.1 ≫ N.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (y.1 ≫ N.j) f) ≤ 1) → ∀ x ∈ U, RegAt x f := by
  intro F _ _ Y N hN
  haveI := N.ar.isIntegral
  intro U f hf x hx
  have : IsProper N.p := by
    obtain ⟨n, c, hc, h⟩ := N.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  have : IsLocallyNoetherian N.X := LocallyOfFiniteType.isLocallyNoetherian N.p
  by_contra hreg
  obtain ⟨z, hz, hzero⟩ := GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal N.X hN x f hreg
  have hf0 : f ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have hzU : z ∈ U := hz.mem_open U.isOpen hx
  obtain ⟨W₀, hzW, g₀, hg₀⟩ := hzero.regAt.exists_fnOf
  have hzW' : z ∈ W₀ ⊓ U := ⟨hzW, hzU⟩
  obtain ⟨g, hg⟩ : ∃ g : Γ(N.X, W₀ ⊓ U), ∀ h, fnOf _ h g = f⁻¹ :=
    ⟨resG N.X inf_le_left g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩
  have hg0 : g ≠ 0 := fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzW'), h, map_zero])
  have hzg : z ∉ N.X.basicOpen g := fun h =>
    (zeroAt_iff.1 hzero).2 (hg (gen_mem hzW') ▸ (unitAt_fnOf_iff hzW' _ g).2 h)
  obtain ⟨v, e, y, yt, hc, hW, hn, hu⟩ := GlobalTheory.T.exists_ext_point_specializing_outside_basicOpen F Y N _ z g hzW' hg0 hzg
  have hle := hf v e y yt hc fun p hp => (hW hp).2
  have hu' : below (y.1 ≫ N.j) ∈ N.X.basicOpen g := hu
  have hb : below (y.1 ≫ N.j) ∈ W₀ ⊓ U := N.X.basicOpen_le g hu'
  have ht : ⊤ ≤ (y.1 ≫ N.j) ⁻¹ᵁ (W₀ ⊓ U) := fun p _ => by
    change (y.1 ≫ N.j) p ∈ W₀ ⊓ U
    rw [← hc]
    exact hW (x := spMap e.O.subtype p) trivial
  have hunit : UnitAt (below (y.1 ≫ N.j)) f⁻¹ := hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'
  have hfu : UnitAt (below (y.1 ≫ N.j)) f := inv_inv f ▸ hunit.inv
  have hmul := OfModel.valAt_mul (y.1 ≫ N.j) hfu.regAt hunit.regAt
  have hone : valAt (y.1 ≫ N.j) (1 : N.X.functionField) = 1 := by
    have := OfModel.valAt_algebraMap (y.1 ≫ N.j) 1
    rwa [map_one, map_one] at this
  have hev := OfModel.eval_pull e.O.subtype (𝟙 N.X) (y.1 ≫ N.j) yt (hc.trans (Category.comp_id _).symm)
    (U := W₀ ⊓ U) (W := W₀ ⊓ U) le_rfl ht hW g
  have hid : ((𝟙 N.X : N.X ⟶ N.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl).hom g = g := by
    have : (𝟙 N.X : N.X ⟶ N.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl = 𝟙 _ :=
      (Category.id_comp _).trans (N.X.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev] at hmul
  refine hn ((isUnit_eval_iff yt hW g).1 (isUnit_of_one_le e _ ?_))
  have h₁ := congrArg e.w hmul
  rw [map_one, map_mul] at h₁
  exact h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hle)

end GlobalTheory.TrueGeo.RegCrit
