import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TranslateDivAdditive
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.KerPow

namespace GlobalTheory.NoSec

variable {X Y Z : Scheme.{0}}

theorem hasGen_of_iso_tw (M : LB X) (p q m : Y ⟶ X)
    (h : ∃ w : LB.Iso (M.pull m) (tw (M.pull p) (M.pull q) 1), w.IsGen) :
    HasGen M (K := Fin 3) ![p, q, m] ![1, 1, -1] := by
  refine gen_transfer (M := LB.div (tw (M.pull p) (M.pull q) 1) (M.pull m))
    (M' := LB.LinComb M (K := Fin 3) ![p, q, m] ![1, 1, -1])
    (fun j => ((fun _ => j 0, fun _ => j 1), fun _ => j 2)) (fun j y hy => ?_) ?_ h
  · exact ⟨⟨mem_pull.2 (Set.mem_iInter.1 hy 0), mem_pull.2 (Set.mem_iInter.1 hy 1)⟩,
      mem_pull.2 (Set.mem_iInter.1 hy 2)⟩
  · intro i j y hi hj
    have i0 : (𝟙 Y : Y ⟶ Y) y ∈ (M.pull p).U (fun _ => i 0) := mem_pull.2 (Set.mem_iInter.1 hi 0)
    have i1 : (𝟙 Y : Y ⟶ Y) y ∈ (M.pull q).U (fun _ => i 1) := mem_pull.2 (Set.mem_iInter.1 hi 1)
    have i2 : (𝟙 Y : Y ⟶ Y) y ∈ (M.pull m).U (fun _ => i 2) := mem_pull.2 (Set.mem_iInter.1 hi 2)
    have j0 : (𝟙 Y : Y ⟶ Y) y ∈ (M.pull p).U (fun _ => j 0) := mem_pull.2 (Set.mem_iInter.1 hj 0)
    have j1 : (𝟙 Y : Y ⟶ Y) y ∈ (M.pull q).U (fun _ => j 1) := mem_pull.2 (Set.mem_iInter.1 hj 1)
    have j2 : (𝟙 Y : Y ⟶ Y) y ∈ (M.pull m).U (fun _ => j 2) := mem_pull.2 (Set.mem_iInter.1 hj 2)
    have e1 := gm_div (M.pull m) (tw (M.pull p) (M.pull q) 1) (𝟙 Y) y
      ((fun _ => i 0, fun _ => i 1), fun _ => i 2) ((fun _ => j 0, fun _ => j 1), fun _ => j 2)
      ⟨⟨⟨i0, i1⟩, i2⟩, ⟨j0, j1⟩, j2⟩
    have e2 := gm_div (pw (M.pull q) (-1)) (M.pull p) (𝟙 Y) y
      (fun _ => i 0, fun _ => i 1) (fun _ => j 0, fun _ => j 1) ⟨⟨i0, i1⟩, j0, j1⟩
    have e3 : gm (𝟙 Y) y _ ((pw (M.pull q) (-1)).g (fun _ => i 1) (fun _ => j 1)) =
        (gm (𝟙 Y ≫ q) y _ (M.g (i 1) (j 1))) ^ (-1 : ℤ) :=
      (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull_g M q (𝟙 Y) y _ _ i1 j1))
    refine (gm_linComb M (K := Fin 3) ![p, q, m] ![1, 1, -1] (𝟙 Y) y i j hi hj).trans ?_
    refine Eq.trans ?_ (e1.trans (congrArg₂ (fun a b => a * b⁻¹) (e2.trans (congrArg₂ (fun a b => a * b⁻¹)
      (gm_pull_g M p (𝟙 Y) y _ _ i0 j0) e3)) (gm_pull_g M m (𝟙 Y) y _ _ i2 j2))).symm
    rw [Fin.prod_univ_three]
    simp

theorem gs_sec {M : LB X} (σ : LB.Sec M) (r : Z ⟶ X) (z : Z) {i j : M.ι} (hi : r z ∈ M.U i) (hj : r z ∈ M.U j) :
    gs r z (M.U i) (σ.f i) = (gm r z (M.U i ⊓ M.U j) (M.g i j)).val * gs r z (M.U j) (σ.f j) := by
  have hm : r z ∈ M.U i ⊓ M.U j := ⟨hi, hj⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (σ.compat i j)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem isUnit_gs (r : Z ⟶ X) (z : Z) {U : X.Opens} (a : Γ(X, U)) (h : r z ∈ X.basicOpen a) :
    IsUnit (gs r z U a) := by
  have hU : r z ∈ U := X.basicOpen_le a h
  rw [gs_eq r z U hU]
  have : z ∈ Z.basicOpen ((r.app U).hom a) := by
    rw [← Scheme.preimage_basicOpen]; exact h
  exact (Z.mem_basicOpen _ z hU).1 this

theorem exists_global {M : LB X} (hM : M.IsLB) (ν : X ⟶ X)
    (H : HasGen M (K := Fin 2) ![𝟙 X, ν] ![1, 1]) (σ : LB.Sec M) :
    ∃ F : Γ(X, ⊤), ∀ (y : X) (i j : M.ι), y ∈ M.U i → ν y ∈ M.U j → ∃ u : (X.presheaf.stalk y)ˣ,
      gs (𝟙 X) y ⊤ F = gs (𝟙 X) y (M.U i) (σ.f i) * gs (𝟙 X ≫ ν) y (M.U j) (σ.f j) * u.val := by
  obtain ⟨t, ht⟩ := H
  let W : (Fin 2 → M.ι) → X.Opens := LB.wchart M (K := Fin 2) ![𝟙 X, ν]
  have l0 : ∀ j, W j ≤ M.U (j 0) := fun j y hy => Set.mem_iInter.1 hy 0
  have l1 : ∀ j, W j ≤ ν ⁻¹ᵁ M.U (j 1) := fun j y hy => Set.mem_iInter.1 hy 1
  have mem : ∀ (y : X) (i j : M.ι), y ∈ M.U i → ν y ∈ M.U j → y ∈ W ![i, j] := fun y i j hi hj =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact hi
      · exact hj
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(X, W j), ∀ j y, y ∈ W j → gs (𝟙 X) y (W j) (u j) =
      gs (𝟙 X) y (M.U (j 0)) (σ.f (j 0)) * gs (𝟙 X ≫ ν) y (M.U (j 1)) (σ.f (j 1)) *
        ((gm (𝟙 X) y (W j) (t.s j))⁻¹).val :=
    ⟨fun j => (X.presheaf.map (homOfLE (l0 j)).op).hom (σ.f (j 0)) *
        (X.presheaf.map (homOfLE (l1 j)).op).hom ((ν.app _).hom (σ.f (j 1))) * (show Γ(X, W j) from ((t.s j)⁻¹).val),
      fun j y hy => (gs_mul (𝟙 X) y (W j) hy _ _).trans (congrArg₂ (· * ·)
        ((gs_mul (𝟙 X) y (W j) hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 X) y (l0 j) hy _)
          ((gs_res (𝟙 X) y (l1 j) hy _).trans (gs_pull (𝟙 X) ν y (M.U (j 1)) (l1 j (show y ∈ W j from hy)) _))))
        ((gs_unit (𝟙 X) y (W j) hy _).trans (congrArg Units.val (map_inv _ _))))⟩
  obtain ⟨F, hF, -⟩ := X.sheaf.existsUnique_gluing' W ⊤ (fun _ => homOfLE le_top) (fun y _ => by
      obtain ⟨i, hi⟩ := exists_chart hM y
      obtain ⟨j, hj⟩ := exists_chart hM (ν y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, mem y i j hi hj⟩) u
    (fun I J => fn_ext (V := W I ⊓ W J) fun y hy => by
      refine (gs_res (𝟙 X) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy _).symm)
      have e : gm (𝟙 X) y (W I) (t.s I) = _ * gm (𝟙 X) y (W J) (t.s J) := gen_trans ht (𝟙 X) y hy.1 hy.2
      have e' : trF (L := M) (K := Fin 2) ![𝟙 X, ν] ![1, 1] (𝟙 X) y I J =
          gm (𝟙 X) y _ (M.g (I 0) (J 0)) * gm (𝟙 X ≫ ν) y _ (M.g (I 1) (J 1)) := by
        rw [trF, Fin.prod_univ_two]
        simp
      rw [hu I y hy.1, hu J y hy.2, e, e', gs_sec σ (𝟙 X) y (l0 I hy.1) (l0 J hy.2),
        gs_sec σ (𝟙 X ≫ ν) y (l1 I hy.1) (l1 J hy.2)]
      generalize gm (𝟙 X) y _ (M.g (I 0) (J 0)) = a
      generalize gm (𝟙 X ≫ ν) y _ (M.g (I 1) (J 1)) = b
      simp only [mul_inv, Units.val_mul]
      have ha := a.mul_inv
      have hb := b.mul_inv
      linear_combination (exp := 1) (gs (𝟙 X) y (M.U (J 0)) (σ.f (J 0)) * gs (𝟙 X ≫ ν) y (M.U (J 1)) (σ.f (J 1)) *
        ((gm (𝟙 X) y (W J) (t.s J))⁻¹).val) * ((b.val * (b⁻¹).val) * ha + hb))
  refine ⟨F, fun y i j hi hj => ?_⟩
  have hy := mem y i j hi hj
  exact ⟨_, (gs_res (𝟙 X) y (le_top : W ![i, j] ≤ ⊤) hy F).symm.trans
    ((congrArg (gs (𝟙 X) y (W ![i, j])) (hF _)).trans (hu _ y hy))⟩

theorem gen_of_sec_ne_zero [IsIntegral X] (hX : IsField Γ(X, ⊤)) {M : LB X} (hM : M.IsLB) (ν : X ⟶ X)
    (hν : Function.Surjective ν) (H : HasGen M (K := Fin 2) ![𝟙 X, ν] ![1, 1]) (σ : LB.Sec M) (i : M.ι)
    (hi : σ.f i ≠ 0) : ∃ t : LB.Gen M, t.IsGen := by
  obtain ⟨F, hF⟩ := exists_global hM ν H σ
  have hD : (X.basicOpen (σ.f i) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hi ((basicOpen_eq_bot_iff _).1 (TopologicalSpace.Opens.ext h))
  have hD' : ((ν ⁻¹ᵁ X.basicOpen (σ.f i) : X.Opens) : Set X).Nonempty := by
    obtain ⟨y, hy⟩ := hD
    obtain ⟨z, rfl⟩ := hν y
    exact ⟨z, hy⟩
  obtain ⟨y, hy, hy'⟩ := nonempty_preirreducible_inter (X.basicOpen (σ.f i)).isOpen
    (ν ⁻¹ᵁ X.basicOpen (σ.f i)).isOpen hD hD'
  have hF0 : F ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu⟩ := hF y i i (X.basicOpen_le _ hy) (X.basicOpen_le _ hy')
    have h1 := ((isUnit_gs (𝟙 X) y (σ.f i) hy).mul (isUnit_gs (𝟙 X ≫ ν) y (σ.f i) hy')).mul u.isUnit
    rw [← hu, gs_eq (𝟙 X) y ⊤ trivial, map_zero, map_zero] at h1
    exact not_isUnit_zero h1
  have hFu : IsUnit F := by
    obtain ⟨G, hG⟩ := hX.mul_inv_cancel hF0
    exact IsUnit.of_mul_eq_one G hG
  have hu : ∀ k, IsUnit (σ.f k) := fun k => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z hz => by
    obtain ⟨j, hj⟩ := exists_chart hM (ν z)
    obtain ⟨u, hu⟩ := hF z k j hz hj
    have h1 : IsUnit (gs (𝟙 X) z ⊤ F) := by
      rw [gs_eq (𝟙 X) z ⊤ trivial]
      exact (hFu.map _).map _
    rw [hu] at h1
    have h2 := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h1)
    exact (congrArg IsUnit (gs_eq (𝟙 X) z (M.U k) hz _)).mp h2
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (σ.compat i j)⟩

end GlobalTheory.NoSec

namespace GlobalTheory

open NoSec

theorem sec_translDiff_eq_zero :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A), x ≠ η[P.A] → ∀ (σ : LB.Sec (LB.LinComb P.L (K := Fin 2) ![(lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A]).left, 𝟙 P.A.left] ![1, -1])) i, σ.f i = 0 := by
  intro K _ _ P x hx σ i
  by_contra hi
  have hab := P.isAb
  have hgi : GeometricallyIntegral P.A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hab.smooth hab.geomConnected
  have hint : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have hfield : IsField Γ(P.A.left, ⊤) :=
    MulEquiv.isField (Field.toIsField K)
      ((RingEquiv.ofBijective _ (globalFns_holds _ P.A hab)).symm.trans
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv).toMulEquiv
  have H3 := hasGen_of_iso_tw _ _ _ _ (GlobalTheory.TranslateAdditive.translate_div_additive K P x)
  let M := LB.LinComb P.L (K := Fin 2) ![(lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A]).left, 𝟙 P.A.left] ![1, -1]
  have hM : M.IsLB := LB.isLB_linComb P.isLB _ _
  have H3' := H3.pull (lift (𝟙 P.A) ι[P.A]).left
    (φ' := ![𝟙 P.A.left, ι[P.A].left, P.A.hom ≫ η[P.A].left]) (fun k => by
      fin_cases k
      · exact congrArg (fun q => q.left) (lift_fst (𝟙 P.A) ι[P.A])
      · exact congrArg (fun q => q.left) (lift_snd (𝟙 P.A) ι[P.A])
      · exact congrArg (fun q => q.left) (GrpObj.right_inv P.A))
  have H0 : HasGen M (K := Fin 1) ![η[P.A].left] ![-1] := DVR.exists_gen_of_local (V := K) M hM _ _
  have H0' := H0.pull P.A.hom (φ' := ![P.A.hom ≫ η[P.A].left]) (fun k => by fin_cases k; rfl)
  have H2 : HasGen M (K := Fin 2) ![𝟙 P.A.left, ι[P.A].left] ![1, 1] :=
    H3'.comb hM H0' fun U _ h => by
      rw [Fin.prod_univ_three, Fin.prod_univ_two, Fin.prod_univ_one]
      simp
  have hsurj : Function.Surjective ι[P.A].left := fun y =>
    ⟨ι[P.A].left y, congrArg (fun q : P.A ⟶ P.A => q.left y) (GrpObj.inv_comp_inv P.A)⟩
  have G : HasGen P.L (K := Fin 2) ![(lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A]).left, 𝟙 P.A.left] ![1, -1] :=
    gen_of_sec_ne_zero hfield hM _ hsurj H2 σ i hi
  have e := eq_one_of_locGen P.ktriv x fun p => ⟨⊤, trivial,
    G.pull (((fst (𝟙_ _) P.A).left ⁻¹ᵁ ⊤).ι ≫ (snd (𝟙_ _) P.A).left) fun k => by
      rw [Category.assoc]
      congr 1
      fin_cases k
      · refine congrArg (fun q => q.left) (show snd (𝟙_ _) P.A ≫ lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A] =
          translPt P.A x from ?_)
        rw [translPt, comp_lift_assoc, Category.comp_id, ← Category.assoc,
          Subsingleton.elim (snd (𝟙_ _) P.A ≫ toUnit P.A) (fst _ _)]
      · exact Category.comp_id _⟩
  apply hx
  rw [e, Hom.one_def, toUnit_unit, Category.id_comp]

end GlobalTheory
