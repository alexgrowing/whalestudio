import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusGenCubical
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSemiAbelianPolarised
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveAppTopOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianAndTqOfIsGt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.MultiplicativeTorusSetting

section Sections
variable {X Y Z : Scheme.{0}} {L : LB X}

theorem isUnit_gs_of_mem {M : LB X} (θ : LB.Sec M) (r : Z ⟶ X) (z : Z) {k : M.ι} (hk : r z ∈ M.U k)
    (h : r z ∈ nonzeroLocus θ) : IsUnit (gs r z _ (θ.f k)) := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hj' : r z ∈ M.U j := X.basicOpen_le _ hj
  rw [gs_compat θ r z hk hj']
  refine (Units.isUnit _).mul ?_
  rw [gs_stalkMap r z _ hj', gs_eq (𝟙 X) (r z) _ hj']
  exact IsUnit.map _ ((X.mem_basicOpen _ _ hj').1 hj)

theorem exists_sec_of_pow_one (θ : H0 L 1) : ∃ s : LB.Sec L, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J),
    Good L z J → gs r z _ (s.f (J r)) = sval θ r z J := by
  have le : ∀ j, L.U j ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := fun j y hy =>
    Set.mem_iInter.2 fun _ => hy
  refine ⟨⟨fun j => resG X (le j) (θ.f fun _ => j), fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => ?_⟩
  · rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy]
    refine (gs_res (𝟙 X) y (le j) hy.1 _).trans ((sec_trans θ (𝟙 X) y (le j hy.1) (le j' hy.2)).trans
      (congrArg₂ (· * ·) ?_ (gs_res (𝟙 X) y (le j') hy.2 _).symm))
    rw [trF, Fintype.prod_unique]
    simp only [Category.comp_id, Nat.cast_one, zpow_one]
  · rw [sval_of θ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
    exact gs_res r z _ (hJ r) _

theorem exists_gen_of_isUnit (hL : L.IsLB) (s : LB.Sec L) (h : ∀ j, ∀ y ∈ L.U j, IsUnit (gs (𝟙 X) y _ (s.f j))) :
    ∃ t : LB.Gen (L.pull (𝟙 X)), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
      (val (L := L) (φ := fun _ : PUnit => 𝟙 X) (ε := fun _ => 1) t r z J).val = gs r z _ (s.f (J r)) := by
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff _).1 (pullIso_isGen hL (𝟙 X))) hL (pull_isLB hL _) s
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) j, r z ∈ L.U j →
      gs r z _ (s'.f fun _ => j) = gs r z _ (s.f j) := fun Z r z j hj => by
    have e := hs' Z r z j (fun _ => j) hj (mem_pull.2 hj)
    have a : gw (pullIso L (𝟙 X)) r z j (fun _ => j) = 1 := gm_self (pull_isLB hL _) r z (mem_pull.2 hj)
    rw [a, Units.val_one, _root_.one_mul, Category.comp_id] at e
    exact e.symm
  have hu : ∀ k, IsUnit (s'.f k) := fun k => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have e := (congrArg IsUnit (key _ (𝟙 X) y (k PUnit.unit) (mem_pull.1 hy))).mpr (h _ y (mem_pull.1 hy))
    rw [gs_eq _ _ _ (show (𝟙 X : X ⟶ X) y ∈ _ from hy)] at e
    exact e
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s'.compat i j), fun Z r z J hJ => ?_⟩
  rw [val_of _ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
  exact (gs_unit r z _ (mem_pull.2 (hJ r)) _).symm.trans (key Z r z _ (hJ r))

end Sections

theorem sec_eq_of_value (hT : SecTwistSt) {V : Type} [CommRing V] [IsDomain V]
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) {X : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of V)} [Flat p]
    {d : A.A.left ⟶ X} (hd : IsPullback d A.A.hom p (jK V)) {L : LB X} (hL : L.IsLB) (hw : LBIso A.L (L.pull d))
    (e : Spec (CommRingCat.of (FractionRing V)) ⟶ A.A.left) (he : e ≫ A.A.hom = 𝟙 _) (s s' : LB.Sec L)
    (z : Spec (CommRingCat.of (FractionRing V))) (j : L.ι) (hj : (e ≫ d) z ∈ L.U j)
    (hu : IsUnit (gs (e ≫ d) z _ (s.f j))) (h : gs (e ≫ d) z _ (s.f j) = gs (e ≫ d) z _ (s'.f j)) (i : L.ι) :
    s.f i = s'.f i := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT A
  have key : ∀ s : LB.Sec L, ∃ a : FractionRing V, ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) j k,
      d (r z) ∈ L.U j → r z ∈ A.L.U k → gs (r ≫ d) z _ (s.f j) =
        (gw w r z j k).val * (cst (r ≫ A.A.hom) z a * gs r z _ (b.f k)) := fun s => by
    obtain ⟨t, ht⟩ := sec_pull_down ((isGen_iff w).1 hw) hL A.isLB s
    obtain ⟨a, ha, -⟩ := hb t
    refine ⟨a, fun Z r z j k h₁ h₂ => ?_⟩
    rw [ht Z r z j k h₁ h₂, ha k, gs_mul _ _ _ h₂, gs_constFn _ _ _ _ h₂]
  obtain ⟨a, ha⟩ := key s
  obtain ⟨a', ha'⟩ := key s'
  obtain ⟨k, hk⟩ := exists_chart A.isLB (e z)
  rw [ha _ e z j k hj hk] at hu h
  rw [ha' _ e z j k hj hk, Units.mul_right_inj,
    (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu)).mul_left_inj, he] at h
  obtain rfl : a = a' := by
    by_contra hne
    have r := cst_regular (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z (sub_ne_zero.2 hne)
    rw [cst_sub, h, sub_self] at r
    exact not_isLeftRegular_zero r
  refine Exist.CubicalExtension.app_injective_generic hd (L.U i) (fn_ext fun y hy => ?_)
  obtain ⟨k, hk⟩ := exists_chart A.isLB y
  exact (gs_pull (𝟙 _) d y _ hy _).trans ((ha _ (𝟙 _) y i k hy hk).trans
    ((ha' _ (𝟙 _) y i k hy hk).symm.trans (gs_pull (𝟙 _) d y _ hy _).symm))

theorem not_isProper_torus (k : Type) [Field k] [CharZero k] :
    ¬ IsProper (splitTorus (Spec (CommRingCat.of k)) ℤ).hom := fun h => by
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  obtain ⟨p, hp, h0⟩ := isIntegral_appTop_of_universallyClosed (splitTorus (Spec (CommRingCat.of k)) ℤ).hom
    (charUnit (Spec (CommRingCat.of k)) ℤ 1).val
  have root : ∀ a : kˣ, (p.map e.symm.toRingHom).IsRoot a.val := fun a => by
    let t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ splitTorus (Spec (CommRingCat.of k)) ℤ :=
      (splitTorusPointsEquiv _ ℤ _).symm (zpowersHom _ (Units.map e.toMonoidHom a))
    have h₁ : t.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) ℤ 1).val = e a.val := by
      rw [← chV_val, chV, MulEquiv.apply_symm_apply]
      exact congrArg Units.val (zpow_one (Units.map e.toMonoidHom a))
    have h₂ : t.left.appTop.hom.comp (splitTorus (Spec (CommRingCat.of k)) ℤ).hom.appTop.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, Over.w]
      exact congrArg CommRingCat.Hom.hom Scheme.Hom.id_appTop
    have h₃ := congrArg t.left.appTop.hom h0
    rw [Polynomial.hom_eval₂, h₂, h₁, map_zero] at h₃
    have h₄ := congrArg e.symm.toRingHom h₃
    rw [Polynomial.hom_eval₂, map_zero] at h₄
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    simpa using h₄
  have inf : Set.Infinite {x | (p.map e.symm.toRingHom).IsRoot x} :=
    Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + 1 : ℕ) : k))
      (fun a b h => by simpa using h) fun n => root (Units.mk0 _ (Nat.cast_ne_zero.2 n.succ_ne_zero))
  exact (hp.map _).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ inf)

def tqOfIso {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ≅ G)
    [IsMonHom i.hom] : TQ G X :=
  have e : G.hom = i.inv.left ≫ (splitTorus S X).hom := (Over.w i.inv).symm
  have : IsIso i.inv.left := inferInstanceAs (IsIso ((Over.forget S).map i.inv))
  { B := 𝟙_ (Over S)
    isAb := isAbelianScheme_unit S
    q := toUnit _
    i := i.hom
    q_hom := inferInstance
    i_hom := inferInstance
    q_flat := by rw [Rosenlicht.toUnit_left, e]; have := Diag.flat_hom S X; infer_instance
    q_surj := by rw [Rosenlicht.toUnit_left, e]; have := Diag.surjective_hom S X; infer_instance
    q_affine := by rw [Rosenlicht.toUnit_left, e]; have := Diag.isAffineHom_hom S X; infer_instance
    isKernel := by
      have : IsIso (η[𝟙_ (Over S)]) := by rw [toUnit_unique η[𝟙_ (Over S)] (𝟙 _)]; infer_instance
      exact IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
    loc := fun _ χ => ⟨⊤, trivial, chV i.inv χ, isWt_of_retraction i.inv i.hom_inv_id χ⟩ }

theorem exists_even_sec (hT : SecTwistSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
    [IsCommMonObj G] [Flat G.hom] {d : A.A.left ⟶ G.left} (gp : IsGrpPullback A.A G (jK V) d) (P : CP G)
    (hw : LBIso A.L (P.L.L.pull d)) (θ : H0 P.L.L 1) (h0 : eSec G (IsLocalRing.closedPoint V) ∈ nonzeroLocus θ) :
    ∃ s : LB.Sec P.L.L, ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good P.L.L z J →
      (r z ∈ nonzeroLocus θ → IsUnit (gs r z _ (s.f (J r)))) ∧
      gs (r ≫ (ι[G]).left) z _ (s.f (J (r ≫ (ι[G]).left))) = (val P.sym r z J).val * gs r z _ (s.f (J r)) := by
  have := A.isAb.comm
  obtain ⟨θ', hθ'⟩ := exists_sec (φ' := fun _ : Fin 1 => 𝟙 G.left) (ε' := fun _ => ((1 : ℕ) : ℤ)) P.L.isLB
    (fun U _ h => (Fintype.prod_sum_type _).trans (by simp [Fin.prod_univ_two]))
    (pullMulSec θ (ι[G]).left (LB.invGen _ _ _ P.sym) (DVR.invGen_isGen _ _ _ _ P.sym_gen))
  obtain ⟨s, hs⟩ := exists_sec_of_pow_one θ
  obtain ⟨s', hs'⟩ := exists_sec_of_pow_one θ'
  have un : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good P.L.L z J →
      r z ∈ nonzeroLocus θ → IsUnit (gs r z _ (s.f (J r))) := fun Z r z J hJ h => by
    rw [hs Z r z J hJ]
    exact isUnit_gs_of_mem θ r z (hJ.mem _ r) h
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good P.L.L z J →
      gs (r ≫ (ι[G]).left) z _ (s.f (J (r ≫ (ι[G]).left))) = (val P.sym r z J).val * gs r z _ (s'.f (J r)) :=
    fun Z r z J hJ => by
      rw [hs Z _ z J hJ, hs' Z r z J hJ, hθ' Z r z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, val_inv, mul_comm (sval _ _ _ _),
        Units.mul_inv_cancel_left]
  have he : eSec A.A ≫ d = (1 : Over.mk (jK V) ⟶ G).left := (cubeMapOf gp).e_comm.trans (one_left G (Over.mk (jK V))).symm
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V))) := inferInstance
  obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
  have top : eSec G ⁻¹ᵁ nonzeroLocus θ = ⊤ := (IsLocalRing.closed_point_mem_iff (R := V)).1 h0
  have key := sec_eq_of_value hT A gp.1 P.L.isLB hw (eSec A.A) (Over.w η[A.A]) s s' z (J (eSec A.A ≫ d)) (hJ _)
    (un _ _ z J hJ (by
      rw [he, one_left]
      exact top.ge (show jK V z ∈ (⊤ : (Spec (CommRingCat.of V)).Opens) from trivial))) (by
      have e := ev _ (eSec A.A ≫ d) z J hJ
      have e₁ : (eSec A.A ≫ d) ≫ (ι[G]).left = eSec A.A ≫ d := by
        rw [he, ← Over.comp_left, ← Hom.inv_def, inv_one]
      have e₂ : val P.sym (eSec A.A ≫ d) z J = 1 := by
        rw [he]; exact P.val_sym_one (T := Over.mk (jK V)) hJ
      rwa [e₁, e₂, Units.val_one, _root_.one_mul] at e)
  exact ⟨s, fun Z r z J hJ => ⟨un Z r z J hJ, by rw [ev Z r z J hJ, key]⟩⟩

theorem exists_even_cubTriv {k : Type} [Field k] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G₀ : Over (Spec (CommRingCat.of k))} [GrpObj G₀]
    [IsCommMonObj G₀] (i : splitTorus (Spec (CommRingCat.of k)) X ≅ G₀) [IsMonHom i.hom] {P : CP G} {P₀ : CP G₀}
    {f : Spec (CommRingCat.of k) ⟶ S} {F : G₀.left ⟶ G.left} {hF : F ≫ G.hom = G₀.hom ≫ f}
    {w : LB.Iso P₀.L.L (P.L.L.pull F)} (hw : IsCPMap P₀ P f F hF w) (s : LB.Sec P.L.L)
    (hu : ∀ (y : G₀.left) (J), Good P.L.L y J → IsUnit (gs F y _ (s.f (J F))))
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good P.L.L z J →
      gs (r ≫ (ι[G]).left) z _ (s.f (J (r ≫ (ι[G]).left))) = (val P.sym r z J).val * gs r z _ (s.f (J r))) :
    ∃ σ : CubTriv P₀.c i.hom, σ.Even := by
  obtain ⟨s₀, hs₀⟩ := sec_pull_down ((isGen_iff w).1 hw.gen) P.L.isLB P₀.L.isLB s
  obtain ⟨t, ht, vt⟩ := exists_gen_of_isUnit P₀.L.isLB s₀ fun j y hy => by
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB y
    have e := hs₀ _ (𝟙 _) y (J F) j (hJ F) hy
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ hu y J hJ)
  obtain ⟨σ, hσ, vσ⟩ := exists_gen (φ' := ![i.hom.left, (1 : splitTorus _ X ⟶ G₀).left]) (ε' := ![1, -1]) P₀.L.isLB
    (fun U _ h => (Fintype.prod_sum_type _).trans (by simp [Fin.prod_univ_two]))
    (LB.mulGen _ _ _ _ _ (LB.pullGen P₀.L.L (fun _ : PUnit => 𝟙 _) (fun _ => 1) t i.hom.left)
      (LB.invGen _ _ _ (LB.pullGen P₀.L.L (fun _ : PUnit => 𝟙 _) (fun _ => 1) t (1 : splitTorus _ X ⟶ G₀).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  have v : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ splitTorus _ X) (z : T.left) (J), Good P₀.L.L z J →
      val σ x.left z J = val (L := P₀.L.L) (φ := fun _ : PUnit => 𝟙 _) (ε := fun _ => 1) t (x ≫ i.hom).left z J *
        (val (L := P₀.L.L) (φ := fun _ : PUnit => 𝟙 _) (ε := fun _ => 1) t (1 : T ⟶ G₀).left z J)⁻¹ :=
    fun T x z J hJ => by
      rw [vσ _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left,
        MonObj.comp_one]
  refine ⟨⟨σ, hσ, fun T x y u z J hJ => ?_⟩, fun T x z J' hJ' => ?_⟩
  · have a := splitTorus_gen_cubical k X G₀ i inferInstance P₀.L P₀.c t ht T (x ≫ i.hom) (y ≫ i.hom) (u ≫ i.hom) z J hJ
    simp only [v T _ z J hJ, MonObj.mul_comp] at a ⊢
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    simp only [ofMul_mul, ofMul_inv] at a' ⊢
    linear_combination (norm := abel) a'
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (hw.vals T z J' J hJ' hJ W hW).2.1 (x ≫ i.hom)
    have b : ∀ y : T ⟶ G₀, gs (y.left ≫ F) z _ (s.f (J (y.left ≫ F))) = (W y *
        val (L := P₀.L.L) (φ := fun _ : PUnit => 𝟙 _) (ε := fun _ => 1) t y.left z J').val := fun y => by
      rw [Units.val_mul, vt _ _ z J' hJ', hW]
      exact hs₀ _ y.left z _ _ (hJ (y.left ≫ F)) (hJ' _)
    have c := hs _ ((x ≫ i.hom).left ≫ F) z J hJ
    rw [← inv_left_comp hw.mul, b, b, ← Units.val_mul, Units.val_inj, ← _root_.mul_assoc, a, _root_.mul_assoc,
      mul_right_inj] at c
    show val σ _ z J' = _ * val σ _ z J'
    rw [v T _ z J' hJ', v T _ z J' hJ', GrpObj.inv_comp, c, _root_.mul_assoc]

theorem main : ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries ℚ))))) (G : Over (Spec (CommRingCat.of (PowerSeries ℚ)))) (_ : GrpObj G) (_ : IsCommMonObj G) (s : HidaSetting (PowerSeries ℚ) A G), A.g = 1 ∧ Module.finrank ℤ s.X = 1 ∧ ¬ IsProper (thickObj (PowerSeries ℚ) (IsLocalRing.maximalIdeal (PowerSeries ℚ)) 0 G).hom := by
  obtain ⟨laws, laws₂, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨G, _, _, A, eA, i, hG, hA, hi, hg, L, -, -, -, -, hw, θ, hθ⟩ :=
    MultiplicativeReduction.exists_semiAbelian_polarised laws
  have hV : CDVR (PowerSeries ℚ) := ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance, algebraRat.charZero _⟩
  obtain ⟨P, rfl⟩ := CubicalPackage.exists_package laws _ hV A G hG eA hA L hw
  have := hG.smooth
  have : IsMonHom eA.symm.hom := inferInstanceAs (IsMonHom eA.inv)
  have gp : IsGrpPullback A.A G (jK _) (eA.inv.left ≫ pullback.fst G.hom (jK _)) :=
    ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback G (jK _))).congr (Category.id_comp _) rfl
  have hinv : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, eA.inv_hom_id, Over.id_left]
  obtain ⟨s, hs⟩ := exists_even_sec laws₂.secTwist A gp P
    (LBIso.chartPull (chartPullSec A.L _ eA.inv.left hinv) (chartPullSame P.L.L _ _ _ eA.inv.left fun _ => rfl) hw) θ
    (hθ _ (congrArg (fun q => q (IsLocalRing.closedPoint (PowerSeries ℚ))) (Over.w η[G])))
  obtain ⟨r, hr⟩ := thick_zero_factor (PowerSeries ℚ)
  obtain ⟨i₀, hi₀, -⟩ := grpPullback_iso
    (((SplitTorus.isGrpPullback_bcMap r ℤ).comp ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback G _))).congr
      ((congrArg (r ≫ ·) (Category.id_comp _)).trans hr.symm) rfl)
    (isGrpPullback_pullback G (thick _ (IsLocalRing.maximalIdeal (PowerSeries ℚ)) 0))
  obtain ⟨P₀, w₀, h₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal (PowerSeries ℚ)) 0 P
  have hm : (IsLocalRing.maximalIdeal (PowerSeries ℚ) ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (PowerSeries ℚ ⧸ IsLocalRing.maximalIdeal (PowerSeries ℚ) ^ (0 + 1)) := Ideal.Quotient.field _
  have : CharZero (PowerSeries ℚ ⧸ IsLocalRing.maximalIdeal (PowerSeries ℚ) ^ (0 + 1)) := algebraRat.charZero _
  obtain ⟨wA, hwA⟩ := hw
  refine ⟨A, G, inferInstance, inferInstance, ⟨hV, hG, eA, hA, P, wA, hwA, ℤ, tqOfIso i₀, P₀, ⟨w₀, h₀⟩,
    exists_even_cubTriv i₀ h₀ s (fun y J hJ => (hs _ _ y J hJ).1 (hθ _ ?_)) fun Z r z J hJ => (hs Z r z J hJ).2⟩,
    hg, Module.finrank_self ℤ, fun h => not_isProper_torus
      (PowerSeries ℚ ⧸ IsLocalRing.maximalIdeal (PowerSeries ℚ) ^ (0 + 1)) ?_⟩
  · exact (congrArg (fun q => q y) (pullback.condition.trans (congrArg (_ ≫ ·) hr))).trans
      (IsLocalRing.PrimeSpectrum.comap_residue _ (r (pullback.snd G.hom _ y)))
  · have : IsIso i₀.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i₀.hom))
    rw [← Over.w i₀.hom]
    infer_instance

end GlobalTheory.MultiplicativeTorusSetting

end
