import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionIsUnitGermOfLocalIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmoothProjectiveModificationOfNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBijectiveStalkMapOverDvrPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemRangeStalkOfPullbackMulLocalIsoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.ModifCanon
open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin

theorem stalkMap_bijective_of_isIso_restrict : ∀ (Y X : Scheme.{0}) (σ : X ⟶ Y) (U : Y.Opens), IsIso (σ ∣_ U) →
    ∀ x : X, x ∈ σ ⁻¹ᵁ U → Function.Bijective (σ.stalkMap x).hom := by
  intro Y X σ U h x hx
  have e := morphismRestrictStalkMap σ U ⟨x, hx⟩
  have h1 : IsIso ((σ ∣_ U).stalkMap ⟨x, hx⟩) := ((isIso_iff_isIso_stalkMap (σ ∣_ U)).1 h).2 _
  have h2 : IsIso (σ.stalkMap x) := ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).1 h1
  exact ConcreteCategory.bijective_of_isIso _

theorem isUnit_val_of_isUnit_germ : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y) (O : Y.Opens)
    (x : Sp ℂ ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) (e : Sp ℂ)
    (hy : x e ∈ O) (hiy : x e ∈ B.U i), IsUnit (H0.germ i (x e) hy hiy f) → IsUnit (H0.val x i hO hi f) := by
  intro k _ Y p B O x i hO hi f e hy hiy hu
  have hb : x e ∈ Y.basicOpen (f.loc i) := (Y.mem_basicOpen _ _ (Vanishing.memInf hy hiy)).2 hu
  have hV : ⊤ ≤ x ⁻¹ᵁ Y.basicOpen (f.loc i) := fun y _ => by rw [Subsingleton.elim y e]; exact hb
  rw [H0.val_apply, ← evalPt_res x (Y.basicOpen_le (f.loc i)) _ hV]
  exact (RingedSpace.isUnit_res_basicOpen Y.toLocallyRingedSpace.toRingedSpace (f.loc i)).map _

end GlobalTheory.ModifCanon

namespace GlobalTheory.ModifCanon

open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin

variable {X Y : Scheme.{0}}

abbrev jacChart {K' : LB X} {K B : LB Y} (σ : X ⟶ Y) (hK' : K'.IsLB) (hK : K.IsLB) (hB : B.IsLB) :
    ProdChart (LB.div K' (K.pull σ)) ((tens K B).pull σ) (tens K' (B.pull σ)) where
  isLB₁ := LB.isLB_div hK' (LB.isLB_pull hK σ)
  isLB₂ := LB.isLB_pull (isLB_tens hK hB) σ
  isLB₃ := isLB_tens hK' (LB.isLB_pull hB σ)
  τ := K'.ι × K.ι × B.ι
  a t := (t.1, pIdx K σ t.2.1)
  b t := pIdx (tens K B) σ (t.2.1, t.2.2)
  c t := (t.1, pIdx B σ t.2.2)
  cover x := by
    obtain ⟨i, hi⟩ := exists_chart hK' x
    obtain ⟨j, hj⟩ := exists_chart hK (σ x)
    obtain ⟨l, hl⟩ := exists_chart hB (σ x)
    exact ⟨(i, j, l), ⟨hi, mem_pIdx.2 hj⟩, mem_pIdx.2 ⟨hj, hl⟩, hi, mem_pIdx.2 hl⟩
  rule x t t' e e' := by
    rw [tr_tens _ _ x e.2.2 e'.2.2, tr_div _ _ x e.1 e'.1, tr_pull _ σ x e.2.1 e'.2.1,
      tr_pull _ σ x e.2.2.2 e'.2.2.2, tr_pull _ σ x e.1.2 e'.1.2,
      tr_tens _ _ (σ x) (mem_pull.1 e.2.1) (mem_pull.1 e'.2.1), map_mul, mul_assoc]
    exact congrArg (tr K' x t.1 t'.1 * ·) (inv_mul_cancel_left _ _).symm

theorem val_restr {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens} (x : Sp ℂ ⟶ Y) (i : B.ι)
    (h : O' ≤ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  evalPt_res x (inf_le_inf_right _ h) _ _ (f.loc i)

theorem exists_push_sections : ∀ (F : Type) [Field F] [CharZero F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) [SmoothOfRelativeDimension d p] (U : Y.Opens) (M : Modif p U d) (K : CanonLB p d) (K' : CanonLB M.str d) (B : LB Y), IsProjOver p → (U : Set Y).Nonempty → B.IsLB → ∃ Ψ : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤ → H0 p (tens K.bundle B) ⊤, ∀ (z : Sp ℂ ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ M.opn → ∀ (k' : (tens K'.bundle (B.pull M.σ)).ι) (hk' : ⊤ ≤ z ⁻¹ᵁ (tens K'.bundle (B.pull M.σ)).U k') (k : (tens K.bundle B).ι) (hk : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U k), ∃ lam : ℂˣ, ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) = lam * H0.val z k' le_top hk' g := by
  intro F _ _ Y _ p d _ U M K K' B hproj hU hB
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth p
  have : Nonempty U := hU.to_subtype
  have := M.iso
  have hXi : IsIntegral M.X := GlobalTheory.T.isIntegral_smoothProjectiveModification_of_nonempty F Y p U d M hU
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_jacobian_section_isUnit_germ_of_localIso F Y M.X p M.σ d K K'
  have hL : (tens K.bundle B).IsLB := isLB_tens K.isLB hB
  let C := jacChart M.σ K'.isLB K.isLB hB
  have hopn : ∀ x ∈ M.opn, Function.Bijective (M.σ.stalkMap x).hom :=
    stalkMap_bijective_of_isIso_restrict Y M.X M.σ U M.iso
  have hJU : NowhereZero (H0.restr (le_top : M.opn ≤ ⊤) J) := fun x hx a ha => by
    rw [germ_restr]; exact hJ x (hopn x hx) a ha
  have hT : M.opn ≤ M.σ ⁻¹ᵁ (⊤ : Y.Opens) := fun x _ => memTop (M.σ x)
  have ext : ∀ g : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤, ∃ s : H0 p (tens K.bundle B) ⊤,
      C.mul (H0.restr le_top J) (H0.pull M.σ hT s) = H0.restr le_top g := by
    intro g
    obtain ⟨s₀, hs₀⟩ := (M.bijective_pull hL).2 ((C.mulEquiv hJU).symm (H0.restr le_top g))
    have rel : C.mul (H0.restr le_top J) (H0.pull M.σ le_rfl s₀) = H0.restr le_top g := by
      rw [hs₀]; exact (C.mulEquiv hJU).apply_symm_apply _
    obtain ⟨t, ht⟩ := (exists_sec_res_eq_iff hL (W := U) (LB.coord_mem s₀)).2 (fun x hx1 _ => by
      have := IsNormalScheme.isDiscreteValuationRing_stalk hx1
      obtain ⟨x', rfl, hb⟩ := GlobalTheory.T.exists_bijective_stalkMap_over_dvrPoint F Y p U d M hproj hU x this
      obtain ⟨i, hi⟩ := exists_chart hL (M.σ x')
      have : Nonempty ((tens K.bundle B).U i) := ⟨⟨_, hi⟩⟩
      have hne := nonempty_inf_of_isIntegral U ((tens K.bundle B).U i)
      exact ⟨i, hne, hi, GlobalTheory.T.germ_mem_range_stalk_of_pullback_mul_localIso F Y M.X p M.σ U _ _ _ C J g s₀ rel x' hb (hJ x' hb) i hi⟩)
    refine ⟨H0.ofSec p ⊤ t, ?_⟩
    have e : H0.restr (le_top : U ≤ ⊤) (H0.ofSec p ⊤ t) = s₀ := by
      rw [restr_ofSec]; exact LB.sec_ext fun i => ht i
    rw [← rel, ← e, pull_restr]
  choose Ψ hΨ using ext
  refine ⟨Ψ, fun z hz k' hk' k hk => ?_⟩
  obtain ⟨e⟩ : Nonempty (Sp ℂ) := inferInstance
  have all : ∀ (V : M.X.Opens), z e ∈ V → ⊤ ≤ z ⁻¹ᵁ V := fun V hV y _ => by
    rw [Subsingleton.elim y e]; exact hV
  have he : z e ∈ M.opn := hz trivial
  obtain ⟨t, ha, hb, hc⟩ := C.cover (z e)
  have ha' := all _ ha
  have hb' := all _ hb
  have hc' := all _ hc
  have hb'' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U ((C.b t) PUnit.unit) := fun y _ => by
    rw [Subsingleton.elim y e]; exact mem_pull.1 hb
  have hJv := isUnit_val_of_isUnit_germ F M.X M.str _ M.opn z (C.a t) hz ha' (H0.restr le_top J) e he ha
    (hJU _ he _ ha)
  obtain ⟨T1, hT1, e2⟩ : ∃ T1 : ℂ, T1 ≠ 0 ∧ ∀ g, H0.val z k' le_top hk' g = T1 * H0.val z (C.c t) le_top hc' g :=
    ⟨_, ((Units.isUnit _).map _).ne_zero, fun g => val_change (p := M.str) (O := ⊤) z k' (C.c t) le_top hk' hc' g⟩
  obtain ⟨T2, hT2, e1⟩ : ∃ T2 : ℂ, T2 ≠ 0 ∧ ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) =
      T2 * H0.val (z ≫ M.σ) ((C.b t) PUnit.unit) le_top hb'' (Ψ g) :=
    ⟨_, ((Units.isUnit _).map _).ne_zero, fun g => val_change (p := p) (O := ⊤) (z ≫ M.σ) k ((C.b t) PUnit.unit) le_top hk hb'' (Ψ g)⟩
  refine ⟨Units.mk0 (T2 / (H0.val z (C.a t) hz ha' (H0.restr le_top J) * T1))
    (div_ne_zero hT2 (mul_ne_zero hJv.ne_zero hT1)), fun g => ?_⟩
  have e3 := C.val_mul (H0.restr le_top J) (H0.pull M.σ hT (Ψ g)) t z hz ha' hb' hc'
  rw [hΨ g, val_restr z _ le_top hz le_top] at e3
  have e4 := val_pull M.σ hT z (C.b t) hz hb' le_top hb'' (Ψ g)
  rw [e1, e2, e3, ← e4, Units.val_mk0]
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hJv.ne_zero hT1)]
  ring

end GlobalTheory.ModifCanon
