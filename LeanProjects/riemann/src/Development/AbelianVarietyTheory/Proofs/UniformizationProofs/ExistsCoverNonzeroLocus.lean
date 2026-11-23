import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SquareUnits
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSecValueIsUnit
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SquareOfCubical

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CubeFree

section General
variable {X Y : Scheme.{0}} {L : LB X}

theorem gs_g_single (φ : Y ⟶ X) (n : ℤ) (j j' : Fin 1 → L.ι) (y : Y)
    (h : y ∈ LB.wchart L (fun _ : Fin 1 => φ) j) (h' : y ∈ LB.wchart L (fun _ : Fin 1 => φ) j') :
    (trF (L := L) (fun _ : Fin 1 => φ) (fun _ => n) (𝟙 Y) y j j').val =
      gs (𝟙 Y ≫ φ) y (L.U (j 0) ⊓ L.U (j' 0)) ((pw L n).g (j 0) (j' 0)).val := by
  have hm : (𝟙 Y ≫ φ) y ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨Set.mem_iInter.1 h 0, Set.mem_iInter.1 h' 0⟩
  refine Eq.trans ?_ (gs_unit _ y _ hm _).symm
  rw [trF, Fin.prod_univ_one]
  exact congrArg Units.val (map_zpow _ _ n).symm

theorem unitAt_of_pw {n : ℤ} (s : LB.Sec (pw L n)) (φ : Y ⟶ X) (y : Y) (i : L.ι)
    (h : φ y ∈ X.basicOpen (s.f i)) : UnitAt L (K := Fin 1) (fun _ => φ) (fun _ => n) y := by
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L _ j 0
  have v : ∀ (j : Fin 1 → L.ι) (z : Y), z ∈ LB.wchart L (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z _ ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) =
        gs (𝟙 Y ≫ φ) z (L.U (j 0)) (s.f (j 0)) := fun j z hj =>
    (gs_res _ z _ hj _).trans (gs_pull _ φ z _ (l j hj) _)
  let s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => n)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        have hm : (𝟙 Y ≫ φ) z ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨l j hz.1, l j' hz.2⟩
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            ((congrArg Units.val (gm_linComb L _ _ (𝟙 Y) z j j' hz.1 hz.2)).trans
              (gs_g_single φ n j j' z hz.1 hz.2))) ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        exact (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg _ (gs_res _ z _ hm _)))) }
  refine ⟨s', fun J hJ => isUnit_sval s' (𝟙 Y) y hJ (fun _ => i) ?_⟩
  have hi : y ∈ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => i) :=
    Set.mem_iInter.2 fun _ => X.basicOpen_le _ h
  change y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (l fun _ => i)).op).hom ((φ.app _).hom (s.f i)))
  rw [Scheme.basicOpen_res]
  exact ⟨hi, (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f i)) y).1 h⟩

theorem exists_sec_of_unitAt (hL : L.IsLB) {n : ℤ} {x : X}
    (h : UnitAt L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => n) x) :
    ∃ t : LB.Sec (pw L n), x ∈ nonzeroLocus t := by
  obtain ⟨s, hs⟩ := h
  have l : ∀ i : L.ι, L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  let t : LB.Sec (pw L n) :=
    { f := fun i => (X.presheaf.map (homOfLE (l i)).op).hom (s.f fun _ => i)
      compat := fun i i' => fn_ext fun z hz => by
        refine ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (l i) hz.1 _)).trans (Eq.trans ?_
          ((gs_mul (𝟙 X) z _ hz _ _).trans (congrArg _
            ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (l i') hz.2 _)))).symm)
        refine (sec_trans s (𝟙 X) z (l i hz.1) (l i' hz.2)).trans ?_
        rw [gs_g_single (𝟙 X) n _ _ z (l i hz.1) (l i' hz.2), Category.id_comp]
        rfl }
  obtain ⟨i, hi⟩ := exists_chart hL x
  refine ⟨t, TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩⟩
  obtain ⟨J, hJ, e⟩ := sval_trans hL s x (fun _ => i) (l i hi)
  have u : IsUnit (gs (𝟙 X) x (L.U i) (t.f i)) :=
    (congrArg IsUnit ((gs_res _ x (l i) hi _).trans e)).mpr ((Units.isUnit _).mul (hs J hJ))
  exact (X.mem_basicOpen _ x hi).2 ((congrArg IsUnit (gs_eq (𝟙 X) x _ hi _)).mp u)

theorem unitAt_of_triv (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {ε : I → ℤ}
    (h : Triv (LB.LinComb L φ ε)) {Y' : Scheme.{0}} (e : Y' ⟶ Y) (k : ℕ) (y : Y') :
    UnitAt L (fun i => e ≫ φ i) (fun i => k * ε i) y := by
  obtain ⟨t, ht⟩ := h
  refine UnitAt.congr hL ?_ ⟨powSec (I := Fin k) fun _ => pullSec (genSec t ht) e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_smul, natCast_zsmul]
  · rw [sval_powSec _ _ _ hJ]
    refine IsUnit.prod_univ_iff.2 fun _ => ?_
    rw [sval_pullSec _ _ _ _ hJ, sval_genSec _ _ _ _ hJ]
    exact Units.isUnit _

end General

theorem exists_cover_nonzeroLocus : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (k : ℕ) (s : LB.Sec (pw L.L k)), (∃ j, s.f j ≠ 0) → ∃ (n : ℕ) (t : Fin (n + 1) → LB.Sec (pw L.L (2 * k : ℕ))), ⨆ i, nonzeroLocus (t i) = ⊤ := by
  intro K _ _ B _ _ hB L c k s ⟨j, hj⟩
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  let T : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  have : IsIntegral (T ⊗ B).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 _) _ _ (IsPullback.of_hasPullback (𝟙 _) B.hom).flip
  have : IsIntegral B.left :=
    GeometricallyIntegral.geometrically_isIntegral (f := B.hom) (𝟙 _) _ _ (IsPullback.id_horiz B.hom)
  let q : B ⟶ T := Over.homMk B.hom (Category.comp_id _)
  let e : B ⟶ T ⊗ B := lift q (𝟙 B)
  have he : e ≫ snd T B = 𝟙 B := lift_snd _ _
  have hD : ((((snd T B).left ⁻¹ᵁ B.left.basicOpen (s.f j)) : (T ⊗ B).left.Opens) : Set (T ⊗ B).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((B.left.basicOpen (s.f j) : B.left.Opens) : Set B.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨e.left d, ?_⟩
    show (snd T B).left (e.left d) ∈ B.left.basicOpen (s.f j)
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, he]
    exact hd
  have key : ∀ (x : T ⟶ B) (p : T.left), ∃ t : LB.Sec (pw L.L (2 * k : ℕ)), x.left p ∈ nonzeroLocus t := by
    intro x p
    have hq : x ≫ q = 𝟙 T := Over.OverMorphism.ext (Over.w x)
    have good : ∀ a : T ⟶ B, (ptSecT B (a * x)).left p ∈ (snd T B).left ⁻¹ᵁ B.left.basicOpen (s.f j) →
        UnitAt L.L (K := Fin 1) (fun _ => e.left ≫ (translPt B a).left) (fun _ => (k : ℤ)) (x.left p) := by
      intro a ha
      refine unitAt_of_pw s _ _ j ?_
      have E : x ≫ e ≫ translPt B a = ptSecT B (a * x) ≫ snd T B := by
        simp [e, ptSecT, NoBasePoint.translPt_eq, MonObj.comp_mul, reassoc_of% hq]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, E]
      exact ha
    obtain ⟨a, h₁, h₂⟩ := NoBasePoint.exists_two_points (𝟙 _) _ hD x x
    have sq := unitAt_of_triv L.isLB (Square.triv_square c a a⁻¹) e.left k (x.left p)
    have e1 : translPt B (1 : T ⟶ B) = snd _ _ := by
      rw [NoBasePoint.translPt_eq, MonObj.comp_one, _root_.one_mul]
    have e2 : e.left ≫ (snd T B).left = 𝟙 _ := by rw [← Over.comp_left, he]; rfl
    refine exists_sec_of_unitAt L.isLB (UnitAt.congr L.isLB (formEq_of_add fun U _ hh => ?_)
      (((good a (h₁ p)).mul (good a⁻¹ (h₂ p))).mul sq))
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one, Fin.sum_univ_four,
      Matrix.cons_val, _root_.mul_inv_cancel]
    rw [e1, e2]
    push_cast
    module
  have top : ⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t = ⊤ := by
    have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
    by_contra h
    have hne : ((⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t : B.left.Opens) : Set B.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h' => h (SetLike.coe_injective h')
    obtain ⟨z, hz, hc⟩ := nonempty_inter_closedPoints hne
      (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed
    obtain ⟨t, ht⟩ := key (Over.homMk (pointOfClosedPoint B.hom z hc) (pointOfClosedPoint_comp B.hom z hc))
      (IsLocalRing.closedPoint K)
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨t,
      (congrArg (· ∈ nonzeroLocus t) (pointOfClosedPoint_apply B.hom z hc _)).mp ht⟩)
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun t : LB.Sec (pw L.L (2 * k : ℕ)) => (nonzeroLocus t : Set B.left)) (fun t => (nonzeroLocus t).isOpen)
    (fun z _ => by
      have : z ∈ (⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t) := by rw [top]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 this))
  refine ⟨F.card, Fin.cons (secZero _) (fun i => (F.equivFin.symm i).1), top_unique fun z _ => ?_⟩
  obtain ⟨t, ht, hz⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ z))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨t, ht⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hz

end GlobalTheory.CubeFree
end
