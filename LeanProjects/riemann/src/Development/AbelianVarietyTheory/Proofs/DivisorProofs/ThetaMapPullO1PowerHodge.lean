import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelSemiAbelianRelDimCotangentVectorBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalizationModelFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPowMultipleDegreeDescendsNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyFormulaNormalCoverRationalThetaConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsListedFiniteGaloisExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStableStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.KeyOne

theorem isNormalScheme_of_isOpenImmersion {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (h : Geo.Tor.IsNormalScheme X) : Geo.Tor.IsNormalScheme Y := by
  intro y
  obtain ⟨h1, h2⟩ := h (f y)
  let e : X.presheaf.stalk (f y) ≃+* Y.presheaf.stalk y :=
    (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨MulEquiv.isDomain _ e.symm.toMulEquiv, IsIntegrallyClosed.of_equiv e⟩

theorem exists_lift_of_dense {P U : Scheme.{0}} (i : U ⟶ P) [IsOpenImmersion i] (hi : Dense (Set.range i))
    {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (a : M.Z ⟶ P) [IsOpenImmersion a] :
    ∃ y : Sp Ω ⟶ U, y ≫ i = M.pt ≫ a := by
  have hV : IsOpen (Set.range a) := a.isOpenEmbedding.isOpen_range
  have hne : (Set.range a).Nonempty := ⟨_, M.pt (IsLocalRing.closedPoint Ω), rfl⟩
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := hi.inter_open_nonempty _ hV hne
  have hU : IsOpen (Set.range i) := i.isOpenEmbedding.isOpen_range
  have hsub : Set.range (M.pt ≫ a) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have := ((M.pt_specializes w z).map a.continuous).mem_open hU hz
    simpa using this
  exact ⟨IsOpenImmersion.lift i (M.pt ≫ a) hsub, IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_pt_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F))
    {Ω : Type} [Field Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (io : M.Z ⟶ Y.X) [IsOpenImmersion io] :
    ∃ y : Sp Ω ⟶ Xo.XF c, M.pt ≫ io = y ≫ Y.j := by
  have hid : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 _ from rfl]
      infer_instance
    infer_instance
  haveI := Y.jQ_open
  obtain ⟨y, hy⟩ := exists_lift_of_dense Y.jQ Y.jQ_dense M (io ≫ inv (pullback.fst Y.s (spMap (RingHom.id c.F))))
  refine ⟨y, ?_⟩
  rw [Model.j, ← Category.assoc, hy, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem lbIso_pull_pull {X Y Z : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : LBIso (A.pull (g ≫ f)) (B.pull (g ≫ f))) : LBIso ((A.pull f).pull g) ((B.pull f).pull g) := by
  have hA' := pull_isLB hA f
  have hB' := pull_isLB hB f
  rw [← CechPic.cls_eq_iff (pull_isLB hA' g) (pull_isLB hB' g), CechPic.cls_pull hA' g, CechPic.cls_pull hB' g,
    CechPic.cls_pull hA f, CechPic.cls_pull hB f, ← CechPic.pull_comp, ← CechPic.pull_comp,
    ← CechPic.cls_pull hA _ (pull_isLB hA _), ← CechPic.cls_pull hB _ (pull_isLB hB _), CechPic.cls_eq_iff]
  exact h

theorem lbIso_pull_lbPow {X Y : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) (a b d : ℕ)
    (h : LBIso (lbPow ((lbPow A a).pull f) d) (lbPow ((lbPow B b).pull f) d)) :
    LBIso ((lbPow A (a * d)).pull f) ((lbPow B (b * d)).pull f) := by
  rw [← CechPic.cls_eq_iff (pull_isLB (isLB_lbPow hA _) f) (pull_isLB (isLB_lbPow hB _) f),
    CechPic.cls_pull (isLB_lbPow hA _) f, CechPic.cls_pull (isLB_lbPow hB _) f,
    CechPic.cls_lbPow hA, CechPic.cls_lbPow hB]
  rw [← CechPic.cls_eq_iff (isLB_lbPow (pull_isLB (isLB_lbPow hA _) f) _)
    (isLB_lbPow (pull_isLB (isLB_lbPow hB _) f) _), CechPic.cls_lbPow (pull_isLB (isLB_lbPow hA _) f),
    CechPic.cls_lbPow (pull_isLB (isLB_lbPow hB _) f), CechPic.cls_pull (isLB_lbPow hA _) f,
    CechPic.cls_pull (isLB_lbPow hB _) f, CechPic.cls_lbPow hA, CechPic.cls_lbPow hB] at h
  rw [map_nsmul, map_nsmul] at h
  rw [map_nsmul, map_nsmul, mul_nsmul, mul_nsmul, h]

end GlobalTheory.UMin.KeyOne

theorem GlobalTheory.UMin.KeyOne.lbIso_pull_O1_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (io : M.Z ⟶ Y.X), IsOpenImmersion io → io ≫ Y.s = M.s → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)).pull io) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial * (n + 1).factorial)).pull io) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf Y g hg Ω _ _ M io hio hs
  haveI := hio
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap c.F Ω).injective
  have hMn : Geo.Tor.IsNormalScheme M.Z := GlobalTheory.UMin.KeyOne.isNormalScheme_of_isOpenImmersion io Y.normal
  obtain ⟨y, hy⟩ := GlobalTheory.UMin.KeyOne.exists_pt_eq Y M io
  have hpol := GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c Ω (y ≫ pullback.fst _ _)
  obtain ⟨⟨θ, hθ⟩, hθup⟩ := GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.isLB _ Ω _ hpol
  obtain ⟨Ω', _, _, pt, cc, hfd, -, hdeg, hlist, -⟩ := GlobalTheory.T.theta_constants_listed_finite_galois_extension Xo.X Xo.univ.t.G Xo.univ.t.PP.L
    Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen _ m (n + 1) Ω _ θ hm hn hpol
  letI : Algebra c.F Ω' := ((algebraMap Ω Ω').comp (algebraMap c.F Ω)).toAlgebra
  haveI : IsScalarTower c.F Ω Ω' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective
  obtain ⟨M', π, hM'n, hπf, hπ⟩ := GlobalTheory.T.exists_normalization_model_finiteExtension c.F Ω M Ω' hMn
  have hup := GlobalTheory.T.thetaKeyFormula_normalCover_rational_thetaConstants E H Dw l Xo c o m n f hm hm3 hmu hn hf Y g hg Ω' M' (π ≫ io)
    (spMap (algebraMap Ω Ω') ≫ y) cc hM'n
    (by rw [← Category.assoc, hπ, Category.assoc, hy, Category.assoc])
    (by rw [Category.assoc]; exact ⟨_, pt, hθup _ hθ Ω' (algebraMap Ω Ω'), hlist⟩)
  have hO : ((ProjSpace.O1 o n).pull g).IsLB := pull_isLB (ProjSpace.O1_isLB o n) g
  have hH := (GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y).2.isLB_det
  have hA := pull_isLB (isLB_lbPow hO 8) io
  have hB := pull_isLB (isLB_lbPow hH (4 * (n + 1).factorial)) io
  have key := GlobalTheory.T.lineBundleIso_pow_multiple_degree_descends_normal c.F Ω M Ω' M' π _ _ (n + 1).factorial hMn hπf hπ hA hB hdeg
    (GlobalTheory.UMin.KeyOne.lbIso_pull_pull (isLB_lbPow hO 8) (isLB_lbPow hH _) io π hup)
  exact GlobalTheory.UMin.KeyOne.lbIso_pull_lbPow hO hH io 8 (4 * (n + 1).factorial) (n + 1).factorial key
