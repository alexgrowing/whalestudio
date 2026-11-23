import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormalStatement

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.NormalCubeExt

open GlobalTheory.CubTransport GlobalTheory.PolExtension GlobalTheory.CechPic

theorem appTop_injective {Y Y' : Scheme.{0}} [IsIntegral Y] (h : Y' ⟶ Y) [IsOpenImmersion h] [Nonempty Y'] :
    Function.Injective h.appTop.hom := by
  have : Nonempty (h ''ᵁ ⊤) := by
    obtain ⟨y⟩ := ‹Nonempty Y'›
    exact ⟨⟨h y, y, trivial, rfl⟩⟩
  intro a b e
  apply map_injective_of_isIntegral Y (homOfLE (le_top : h ''ᵁ ⊤ ≤ ⊤))
  have e₁ := h.app_appIso_inv (⊤ : Y.Opens)
  have k := fun x => congrArg (fun q => q.hom x) e₁
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k
  exact (k a).symm.trans ((congrArg _ e).trans (k b))

theorem val_eq_of_open {X Y Y' : Scheme.{0}} [IsIntegral Y] (h : Y' ⟶ Y) [IsOpenImmersion h] [Nonempty Y']
    {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hf : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (H : ∀ y J, Good M y J → val u h y J = val u' h y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ k => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hf U k, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ : ∃ a, a = (res le (t.s PEmpty.elim)).val := ⟨_, rfl⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ a := by
    intro Z r z J hJ
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      (congrArg (gs r z ⊤) ha.symm))
  have a1 : a = 1 := appTop_injective h ((fn_ext (V := ⊤) fun y _ => by
    choose I hI using fun χ : Y' ⟶ X => exists_chart hM (χ y)
    have := key _ h y I hI
    rw [H y I hI, mul_inv_cancel] at this
    refine (gs_pull (𝟙 Y') h y ⊤ trivial a).trans ?_
    rw [Category.id_comp, ← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]).trans (map_one _).symm)
  have := key Z r z J hJ
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

section Base

variable {S U : Scheme.{0}} [IsIntegral S] [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j]

theorem corr_of_open {X : Scheme.{0}} (T : Over S) [Smooth T.hom] [GeometricallyConnected T.hom]
    {L : LB X} (hL : L.IsLB) {I I' : Type} [Fintype I] [Fintype I']
    {φ : I → (T.left ⟶ X)} {ε : I → ℤ} {φ' : I' → (T.left ⟶ X)} {ε' : I' → ℤ} (hf : FormEq φ ε φ' ε')
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen)
    (H : ∀ (y : (pullback T.hom j :)) J, Good L y J →
      val t (pullback.fst T.hom j) y J = val t' (pullback.fst T.hom j) y J) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  have gi := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ T.hom inferInstance inferInstance
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have : IsIntegral T.left := GlobalTheory.isIntegral_of_geometricallyIntegral T.hom
  have : IsIntegral (pullback T.hom j) := GlobalTheory.isIntegral_of_geometricallyIntegral (pullback.snd T.hom j)
  exact corr_of_val hL fun y J hJ => val_eq_of_open (pullback.fst T.hom j) hL hf ht ht' H _ _ y J hJ

end Base

section Group

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem isCub_formal (T : Over S) {V : Type} [CommGroup V] (k : (T.left ⟶ G.left) → V) :
    IsCub (fun a b c : T ⟶ G => ∏ I : thK, k ((lift a (lift b c)).left ≫ thφ G (x3 G) I) ^ thε I) :=
  isCub_mul_diff (θ := fun _ _ _ => 1) ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    (fun a => k a.left) fun a b c => (prod_cub a b c k).trans (_root_.mul_one _).symm

variable {U : Scheme.{0}} [IsIntegral S] [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j]
  [Smooth G.hom] [GeometricallyConnected G.hom]

theorem exists_cubical_of_open (L : RigLB G) (t : LB.Gen (Theta G L.L)) (ht : t.IsGen)
    (h : ∀ (T : Over U) (z : T.left) (J), Good L.L z J →
      IsCub (thV t (T := Over.mk (T.hom ≫ j)) z J)) : ∃ c : CubicalStr G L, c.t = t := by
  have s₂ := CubeExtension.smooth_tensor G G
  have s₃ := CubeExtension.smooth_tensor G (G ⊗ G)
  have s₄ := CubeExtension.smooth_tensor G (G ⊗ G ⊗ G)
  have c₂ := CubeExtension.geometricallyConnected_tensor G G
  have c₃ := CubeExtension.geometricallyConnected_tensor G (G ⊗ G)
  have c₄ := CubeExtension.geometricallyConnected_tensor G (G ⊗ G ⊗ G)
  let ρ : ∀ T : Over S, Over.mk (pullback.snd T.hom j ≫ j) ⟶ T := fun T =>
    Over.homMk (pullback.fst T.hom j) pullback.condition
  have v : ∀ (T : Over S) (y : (pullback T.hom j :)) J, Good L.L y J →
      ∀ a b c : T ⟶ G, val (LB.pullGen L.L (thφ G (x3 G)) thε t (lift a (lift b c)).left)
        (pullback.fst T.hom j) y J =
        thV t (T := Over.mk (pullback.snd T.hom j ≫ j)) y J (ρ T ≫ a) (ρ T ≫ b) (ρ T ≫ c) := by
    intro T y J hJ a b c
    refine (val_pull hJ _ _ _).trans ?_
    rw [thV, ← comp_lift, ← comp_lift]; rfl
  have e : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
    ext <;> simp [x3]
  have v' : ∀ (y : (pullback (G3 G).hom j :)) J,
      val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (pullback.fst (G3 G).hom j) y J =
        thV t (T := Over.mk (pullback.snd (G3 G).hom j ≫ j)) y J
          (ρ _ ≫ x3 G 0) (ρ _ ≫ x3 G 1) (ρ _ ≫ x3 G 2) := by
    intro y J
    rw [thV, ← comp_lift, ← comp_lift, e, Category.comp_id]; rfl
  have w : ∀ (V : Type) [CommGroup V] (k : ((G3 G).left ⟶ G.left) → V), ∏ I : thK, k (thφ G (x3 G) I) ^ thε I =
      ∏ I : thK, k ((lift (x3 G 0) (lift (x3 G 1) (x3 G 2))).left ≫ thφ G (x3 G) I) ^ thε I := fun V _ k => by
    rw [e]
    exact Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) (Category.id_comp _).symm
  have g : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 G).left), (LB.pullGen L.L (thφ G (x3 G)) thε t r).IsGen := fun r =>
    DVR.pullGen_isGen _ _ _ _ ht r
  refine ⟨⟨t, ht, fun i => corr_of_open j (G2 G) L.isLB (fun V _ k => ?_) (g _) (LB.isGen_oneGen _) fun y J hJ => ?_,
    corr_of_open j (G3 G) L.isLB (fun V _ k => ?_) ht (g _) fun y J hJ => ?_,
    corr_of_open j (G3 G) L.isLB (fun V _ k => ?_) ht (g _) fun y J hJ => ?_,
    corr_of_open j (G4 G) L.isLB (fun V _ k => ?_) (DVR.mulGen_isGen _ _ _ _ _ _ _ (g _) (g _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (g _) (g _)) fun y J hJ => ?_⟩, rfl⟩
  · refine Eq.trans ?_ (Fintype.prod_empty _).symm
    have C := isCub_formal (G := G) (G2 G) k
    fin_cases i
    · exact C.face _ _
    · exact C.face₂ _ _
    · exact C.face₃ _ _
  · refine Eq.trans ?_ (val_one _).symm
    have C := h (Over.mk (pullback.snd (G2 G).hom j)) y J hJ
    have o : ρ (G2 G) ≫ pzero G _ = 1 := map_one (preHom (ρ (G2 G)))
    fin_cases i
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face _ _)
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face₂ _ _)
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face₃ _ _)
  · exact (w V k).trans ((isCub_formal (G := G) (G3 G) k).s01 _ _ _)
  · exact (v' y J).trans (((h (Over.mk (pullback.snd (G3 G).hom j)) y J hJ).s01 _ _ _).trans
      (v _ y J hJ _ _ _).symm)
  · exact (w V k).trans ((isCub_formal (G := G) (G3 G) k).s12 _ _ _)
  · exact (v' y J).trans (((h (Over.mk (pullback.snd (G3 G).hom j)) y J hJ).s12 _ _ _).trans
      (v _ y J hJ _ _ _).symm)
  · refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
    exact (isCub_formal (G := G) (G4 G) k).coc (x4 G 0) (x4 G 1) (x4 G 2) (x4 G 3)
  · have C := h (Over.mk (pullback.snd (G4 G).hom j)) y J hJ
    have m : ∀ a b : G4 G ⟶ G, ρ (G4 G) ≫ padd G a b = (ρ (G4 G) ≫ a) * (ρ (G4 G) ≫ b) := fun a b =>
      MonObj.comp_mul _ _ _
    refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v _ y J hJ _ _ _) (v _ y J hJ _ _ _))).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v _ y J hJ _ _ _) (v _ y J hJ _ _ _))).symm)
    rw [m, m]
    exact C.coc _ _ _ _

end Group

section Pull

variable {S U : Scheme.{0}} {j : U ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
  {A : Over U} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left}

theorem groupPullback_tripleProductMap_lift (gp : IsGrpPullback A G j F) (T : Over U) (a b d : T ⟶ A) :
    (lift a (lift b d)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp T a) (lift (pushHom gp T b) (pushHom gp T d))).left := hom_ext_triple _ fun i => by
  rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
  fin_cases i <;> simp [x3] <;> rfl

theorem isPullback_tripleProduct_groupPullback (gp : IsGrpPullback A G j F) :
    IsPullback (cubeMapOf gp).F3 (G3 A).hom (G3 G).hom j := by
  have hp := gp.1
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have w : (cubeMapOf gp).F3 ≫ (G3 G).hom = (G3 A).hom ≫ j :=
    Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2))))
  have ex : ∀ s : PullbackCone (G3 G).hom j, ∃ l : s.pt ⟶ (G3 A).left,
      l ≫ (cubeMapOf gp).F3 = s.fst ∧ l ≫ (G3 A).hom = s.snd := by
    intro s
    let P : Over U := Over.mk s.snd
    let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ F = s.fst ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
    have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
    refine ⟨l.left, hom_ext_triple _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f3, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => hom_ext_triple _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f3, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

end Pull

theorem exists_extension {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S)
    {U H HU X X' : Scheme.{0}} [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H)
    (pU : HU ⟶ U) (eU : U ⟶ HU) (hs : Smooth p) (hc : GeometricallyConnected p) (he : e ≫ p = 𝟙 _)
    (hp : IsPullback jH pU p j) (heU : eU ≫ jH = j ≫ e) {L : LB X} (hL : L.IsLB) {L' : LB X'} (hL' : L'.IsLB)
    {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w) {K : Type} [Fintype K] (φ : K → (H ⟶ X))
    (φ' : K → (HU ⟶ X')) (ε : K → ℤ) (hφ : ∀ k, φ' k ≫ F = jH ≫ φ k)
    (f₁ : FormEq (K := PEmpty) (PEmpty.elim : PEmpty → (S ⟶ X)) PEmpty.elim (fun k => e ≫ φ k) ε)
    (f₂ : FormEq (K := PEmpty) (PEmpty.elim : PEmpty → (U ⟶ X')) PEmpty.elim (fun k => eU ≫ φ' k) ε)
    (s : LB.Gen (LB.LinComb L' φ' ε)) (hg : s.IsGen) (h1 : ∀ y J, Good L' y J → val s eU y J = 1) :
    ∃ c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ PMaps w φ' φ ε s c jH := by
  have key : ∀ (ψ : K → (HU ⟶ X)) (_ : ∀ k, φ' k ≫ F = ψ k),
      ∃ t : LB.Gen (LB.LinComb L ψ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ HU) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L ψ p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L ψ p) (t.s p) = pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (s.s q) := by
    intro ψ hψ
    obtain rfl : (fun k => φ' k ≫ F) = ψ := funext hψ
    exact exists_up hw hL hL' s hg
  obtain ⟨t, ht, hv⟩ := key _ hφ
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen hL f₁ (LB.oneGen L) (LB.isGen_oneGen L)
  obtain ⟨c, ⟨hc₁, hc₂⟩, -⟩ := GlobalTheory.T.existsUnique_rigidified_generator_extend_normal S hS U H HU X j p e jH pU eU hs
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hs hc) he hp heU L hL K φ ε t ρ ht hρ
    (corr_of_val hL fun y J hJ => by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_
        ((val_pull hJ ρ _ _).trans ((vρ _ _ y J hJ).trans (val_one _))).symm)
      rw [Category.id_comp]
      choose J' hJ' using fun χ : U ⟶ X' => exists_chart hL' (χ y)
      refine (hv _ eU y _ _ (hJ.mem _ _) (Good.mem hJ' _ _)).trans ?_
      refine (congrArg₂ (· * ·) ?_ (h1 y J' hJ')).trans (_root_.mul_one 1)
      refine Eq.trans ?_ ((f₂ _ (fun q => gw w q y (J (q ≫ F)) (J' q))).symm.trans (Fintype.prod_empty _))
      exact Finset.prod_congr rfl fun k _ => by rw [Category.assoc, hφ])
  subst hc₂
  refine ⟨c, hc₁, fun Z r z p q hp hq => ?_⟩
  have hm : r z ∈ LB.wchart L (fun k => jH ≫ φ k) p := Set.mem_iInter.2 fun k => by
    show φ k (jH (r z)) ∈ L.U (p k)
    rw [pt_eq hφ]; exact hp k
  refine Eq.trans ?_ (hv Z r z p q hm (Set.mem_iInter.2 hq))
  exact ((gm_res r z _ hm _).trans (gm_pull r jH z (LB.wchart L φ p)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)).symm

section Main

variable {S U : Scheme.{0}} {j : U ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
  {A : Over U} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left}

theorem exists_rigidified (gp : IsGrpPullback A G j F) (L : RigLB A) {M : LB G.left} (hM : M.IsLB)
    (H : LBIso (M.pull F) L.L) : ∃ L' : RigLB G, LBIso L.L (L'.L.pull F) := by
  have h' := LB.isLB_linComb hM (K := Fin 2) ![𝟙 G.left, G.hom ≫ eSec G] ![1, -1]
  have c : cls _ h' = cls M hM - pull (G.hom ≫ eSec G) (cls M hM) := by
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp [pull_id, sub_eq_add_neg]
  have he : eSec A ≫ F = j ≫ eSec G := (cubeMapOf gp).e_comm
  obtain ⟨r, hr⟩ := (cls_eq_zero_iff (pull_isLB h' (eSec G))).1 (by
    rw [cls_pull h', c, map_sub, ← pull_comp, ← Category.assoc, CubeExtension.eSec_comp]
    exact sub_eq_zero.2 (congrArg (fun q => pull q (cls M hM)) (Category.id_comp _).symm))
  refine ⟨⟨_, r, h', hr⟩, (cls_eq_iff L.isLB (pull_isLB h' F)).1 ?_⟩
  have a : pull F (cls M hM) = cls L.L L.isLB := (cls_eq_iff (pull_isLB hM F) L.isLB).2 H
  have b : pull (eSec A) (cls L.L L.isLB) = 0 := (cls_eq_zero_iff (pull_isLB L.isLB _)).2 ⟨L.rig, L.rigGen⟩
  have d : F ≫ G.hom ≫ eSec G = A.hom ≫ eSec A ≫ F := by
    rw [← Category.assoc, gp.1.w, he]
    exact Category.assoc _ _ _
  rw [cls_pull h', c, map_sub, ← pull_comp, d, pull_comp, pull_comp, a, b, map_zero, sub_zero]

variable [IsIntegral S] [IsLocallyNoetherian S] [Nonempty U] [IsOpenImmersion j]
  [Smooth G.hom] [GeometricallyConnected G.hom]

theorem exists_cubical (hS : Geo.Tor.IsNormalScheme S) (gp : IsGrpPullback A G j F) {L : RigLB A} (c : CubicalStr A L)
    (L' : RigLB G) {w : LB.Iso L.L (L'.L.pull F)} (hw : PGen w) :
    ∃ c' : CubicalStr G L', PMaps w (thφ A (x3 A)) (thφ G (x3 G)) thε c.t c'.t (cubeMapOf gp).F3 := by
  have s₂ := CubeExtension.smooth_tensor G G
  have s₃ := CubeExtension.smooth_tensor G (G ⊗ G)
  have c₂ := CubeExtension.geometricallyConnected_tensor G G
  have c₃ := CubeExtension.geometricallyConnected_tensor G (G ⊗ G)
  have hc : ∀ I : thK.{0}, thφ A (x3 A) I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨t, ht, Ht⟩ := exists_extension hS j (G3 G).hom (eSec (G3 G)) (cubeMapOf gp).F3 (G3 A).hom (eSec (G3 A))
    s₃ c₃ (CubeExtension.eSec_comp _) (isPullback_tripleProduct_groupPullback gp) (by
      rw [CubeExtension.eSec_three, groupPullback_tripleProductMap_lift, map_one, CubeExtension.eSec_three]
      refine hom_ext_triple _ fun i => ?_
      rw [Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3, Hom.one_def]) L'.isLB L.isLB hw (thφ G (x3 G)) (thφ A (x3 A)) thε hc
    (CubeExtension.formEq_origin G) (CubeExtension.formEq_origin A) c.t c.isGen (fun y J hJ => by
      rw [CubeExtension.eSec_three]
      exact (isCub_cubV c (T := 𝟙_ _) hJ).face 1 1)
  obtain ⟨c', rfl⟩ := exists_cubical_of_open j L' t ht fun T z J hJ => by
    refine isCub_of_surjective (pushHom gp T) (fun a => ?_) ?_
    · exact ⟨Over.homMk (gp.1.lift a.left T.hom (Over.w a)) (gp.1.lift_snd _ _ _),
        Over.OverMorphism.ext (gp.1.lift_fst _ _ _)⟩
    · choose J' hJ' using fun χ : T.left ⟶ A.left => exists_chart L.isLB (χ z)
      refine isCub_mul_diff (isCub_cubV c hJ') (fun q => gw w q.left z (J (q.left ≫ F)) (J' q.left)) fun a b d => ?_
      have e := val_pmaps hc Ht (lift a (lift b d)).left hJ hJ'
      rw [groupPullback_tripleProductMap_lift] at e
      exact e.trans (congrArg₂ (· * ·) (prod_cub a b d (fun q => gw w q z (J (q ≫ F)) (J' q))) rfl)
  exact ⟨c', Ht⟩

theorem isSymmetric (hS : Geo.Tor.IsNormalScheme S) (gp : IsGrpPullback A G j F) {L : RigLB A}
    (L' : RigLB G) {w : LB.Iso L.L (L'.L.pull F)} (hw : PGen w) (h : L.IsSymmetric) : L'.IsSymmetric := by
  obtain ⟨s, hs, h1⟩ := (isSymmetric_iff_exists_gen U A L).1 h
  have hι : (ι[A]).left ≫ F = F ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp A) (𝟙 A))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ F) ≫ _ = _
    rw [Category.id_comp]
  have e₁ : eSec A ≫ (ι[A]).left = eSec A := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  have e₂ : eSec G ≫ (ι[G]).left = eSec G := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  obtain ⟨t, ht, -⟩ := exists_extension hS j G.hom (eSec G) F A.hom (eSec A) inferInstance inferInstance
    (CubeExtension.eSec_comp _) gp.1 (cubeMapOf gp).e_comm L'.isLB L.isLB hw (K := Fin 2)
    ![(ι[G]).left, 𝟙 G.left] ![(ι[A]).left, 𝟙 A.left] ![1, -1] (fun k => by
      fin_cases k
      · exact hι
      · exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (fun V _ k => by simp [Fin.prod_univ_two, e₂]) (fun V _ k => by simp [Fin.prod_univ_two, e₁]) s hs
    (fun y J hJ => by
      have := (val_pull hJ s (eSec A) (𝟙 _)).symm.trans ((val_corr hJ h1 (𝟙 _)).trans (val_one _))
      rwa [Category.id_comp] at this)
  have z := (cls_eq_zero_iff (LB.isLB_linComb L'.isLB _ _)).2 ⟨t, ht⟩
  rw [cls_linComb L'.isLB, Fin.sum_univ_two] at z
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, ← sub_eq_add_neg,
    sub_eq_zero] at z
  have he : eSec G ≫ (ι[G]).left = 𝟙 _ ≫ eSec G := e₂.trans (Category.id_comp _).symm
  exact ⟨he, Unif.RigidifyIso.exists_rigidified_iso S S (𝟙 S) G G _ he L' L'
    ((cls_eq_iff L'.isLB (pull_isLB L'.isLB _)).1 z.symm)⟩

end Main

theorem exists_cubical_extension : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (U : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (a : A.left ⟶ G.left), IsGrpPullback A G j a → ∀ (L : RigLB A) (c : CubicalStr A L) (M : LB G.left), M.IsLB → LBIso (M.pull a) L.L → ∃ (L' : RigLB G) (c' : CubicalStr G L') (m : CubeMap A G), m.F = a ∧ m.e = j ∧ m.IsPullCubical c c' ∧ (L.IsSymmetric → L'.IsSymmetric) := by
  intro S _ _ hS U _ j _ G _ _ _ _ A _ _ a gp L c M hM H
  obtain ⟨L', h'⟩ := exists_rigidified gp L hM H
  obtain ⟨w, hw, hr⟩ := Unif.RigidifyIso.exists_rigidified_iso S U j G A a (cubeMapOf gp).e_comm L' L h'
  have hw' := (isGen_iff w).1 hw
  obtain ⟨c', hc'⟩ := exists_cubical hS gp c L' hw'
  refine ⟨L', c', cubeMapOf gp, rfl, rfl, ⟨w, hw, hr, ?_⟩, isSymmetric hS gp L' hw'⟩
  exact (maps_iff w _ (thφ G (x3 G)) _ c.t c'.t (cubeMapOf gp).F3 _ ((cubeMapOf gp).theta_le L'.L) (fun _ => rfl)).2 hc'

end GlobalTheory.NormalCubeExt
