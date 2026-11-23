import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiEvenPull

theorem val_eq_of_app_injective {X Y Y' : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    (κ : Y' ⟶ Y) (hκ : ∀ U : Y.Opens, Function.Injective (κ.app U).hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u κ y J = val u' κ y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J)
    (hJ : Good M z J) : val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen hM hF u' hu'
  have e : ∀ j, u.s j = t.s j := fun j => by
    have : pullU κ (LB.wchart M φ j) (u.s j) = pullU κ (LB.wchart M φ j) (t.s j) := unit_ext fun y hy => by
      choose I hI using fun χ : Y' ⟶ X => exists_chart hM (χ y)
      refine (gm_pull (𝟙 Y') κ y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') κ y _ hy _).symm)
      rw [Category.id_comp]
      exact (gen_trans hu κ y hy (Good.mem hI φ κ)).trans ((congrArg _ ((h y I hI).trans (hv _ κ y I hI).symm)).trans
        (gen_trans ht κ y hy (Good.mem hI φ κ)).symm)
    exact Units.ext (hκ _ (congrArg Units.val this))
  exact (congrArg (gm r z _) (e _)).trans (hv Z r z J hJ)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem c_neg (D : DegPre R) (χ : D.X) : D.c (-χ) = D.c χ ≫ ι[D.P.A] := by
  have m : ∀ a b, D.c (a + b) = D.c a * D.c b := fun a b => D.c_add a b
  have z : D.c 0 = 1 := mul_eq_left.1 ((m 0 0).symm.trans (congrArg D.c (add_zero 0)))
  rw [← Hom.inv_def]
  exact eq_inv_of_mul_eq_one_left ((m _ _).symm.trans ((congrArg D.c (neg_add_cancel χ)).trans z))

theorem app_injective_generic (W : (Spec (CommRingCat.of R)).Opens) (U : W.toScheme.Opens) :
    Function.Injective ((jK R ∣_ W).app U).hom := by
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (jK R ∣_ W) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (jK R) W).flip
  exact (jK R ∣_ W).app_injective U

theorem even_on (h : D.PsiEven) {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) (χ : D.X) {Z : Scheme.{0}}
    (r : Z ⟶ (TW W).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    val (ψW.psi (-χ)) r z J * val D.sym (r ≫ (toUnit (TW W) ≫ D.c χ).left) z J = val (ψW.psi χ) r z J := by
  have cn : (toUnit (TW W) ≫ D.c (-χ)).left = (toUnit (TW W) ≫ D.c χ).left ≫ (ι[D.P.A]).left := by
    rw [c_neg, ← Category.assoc, Over.comp_left]
  have key := val_eq_of_app_injective D.P.isLB (u' := LB.mulGen D.P.L _ _ _ _ (ψW.psi (-χ))
      (LB.pullGen D.P.L _ _ D.sym (toUnit (TW W) ≫ D.c χ).left)) (u := ψW.psi χ) (fun V _ k => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Fintype.prod_unique]
      show k (toUnit (TW W) ≫ D.c (-χ)).left ^ (-1 : ℤ) * (k ((toUnit (TW W) ≫ D.c χ).left ≫ (ι[D.P.A]).left) ^ (1 : ℤ) *
        k ((toUnit (TW W) ≫ D.c χ).left ≫ 𝟙 _) ^ (-1 : ℤ)) = k (toUnit (TW W) ≫ D.c χ).left ^ (-1 : ℤ)
      rw [cn, Category.comp_id]
      simp) (jK R ∣_ W) (app_injective_generic W) (ψW.psi_gen χ)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _) (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)) (fun y I hI => by
      have p : ∀ a, val (ψW.psi a) (jK R ∣_ W) y I = val (D.psi a) (jK R ⁻¹ᵁ W).ι y I := fun a => by
        have := val_corr hI (ψW.psi_eq a) (𝟙 _)
        rwa [val_pull hI, val_pull hI, Category.id_comp, Category.id_comp] at this
      have q : (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ D.xK χ := by
        show (jK R ∣_ W) ≫ W.ι ≫ (D.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ jK R ≫ (D.c χ).left
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
      have e := val_corr hI (h χ) (jK R ⁻¹ᵁ W).ι
      rw [val_mul hI, val_pull hI] at e
      rw [val_mul hI, val_pull hI, p, p, q]
      exact e.symm) Z r z J hJ
  rw [val_mul hJ, val_pull hJ] at key
  exact key.symm

abbrev proj (hD : IsPullDeg φ D D') : D'.P.A.left ⟶ D.P.A.left :=
  hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)

theorem inv_proj (hD : IsPullDeg φ D D') : (ι[D'.P.A]).left ≫ proj hD = proj hD ≫ (ι[D.P.A]).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom (pull_grp hD) D'.P.A) (𝟙 _))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine e.trans ?_
  show ((𝟙 D'.P.A : D'.P.A ⟶ D'.P.A).left ≫ proj hD) ≫ _ = _
  rw [Over.id_left, Category.id_comp]

theorem sym_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D.sym (r ≫ proj hD) z J =
      gw hD.w (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ proj hD)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw hD.w r z (J (r ≫ proj hD)) (J' r))⁻¹ * val D'.sym r z J' := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB D'.sym D'.sym_gen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J =
      gw hD.w (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ proj hD)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw hD.w r z (J (r ≫ proj hD)) (J' r))⁻¹ * val D'.sym r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
    rw [pw, Fin.prod_univ_two]
    show gw hD.w (r ≫ (ι[D'.P.A]).left) z (J (r ≫ (ι[D'.P.A]).left ≫ proj hD)) (J' (r ≫ (ι[D'.P.A]).left)) ^ (1 : ℤ) *
      gw hD.w (r ≫ 𝟙 _) z (J (r ≫ 𝟙 _ ≫ proj hD)) (J' (r ≫ 𝟙 _)) ^ (-1 : ℤ) = _
    rw [Category.comp_id, Category.id_comp, Category.assoc r, zpow_one, zpow_neg_one]
  have oi : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A := by
    have : η[D'.P.A] ≫ ι[D'.P.A] = η[D'.P.A] := by simp
    exact congrArg (fun q => q.left) this
  have key := gen_unique' D.P.isLB
    (φ := fun k => proj hD ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) (ε := ![1, -1])
    (fun V _ k => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      show k ((ι[D'.P.A]).left ≫ proj hD) ^ (1 : ℤ) * k (𝟙 _ ≫ proj hD) ^ (-1 : ℤ) =
        k (proj hD ≫ (ι[D.P.A]).left) ^ (1 : ℤ) * k (proj hD ≫ 𝟙 _) ^ (-1 : ℤ)
      rw [inv_proj, Category.id_comp, Category.comp_id])
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (DVR.pullGen_isGen _ _ _ _ D.sym_gen (proj hD)) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Spec (CommRingCat.of R')))).left ⟶ D'.P.A.left =>
        exists_chart D'.P.isLB (χ y)
      have a := val_corr hI' D'.sym_rig (𝟙 _)
      rw [val_pull hI', val_one, Category.id_comp] at a
      have b := val_corr hI D.sym_rig (specOf φ)
      rw [val_pull hI, val_one, ← hD.he] at b
      refine ((val_pull hI _ _ _).trans b).trans (Eq.symm ((hv' _ _ y I I' hI hI').trans ?_))
      rw [a, oi, mul_inv_cancel, _root_.one_mul]) Z r z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))

theorem psi_pull (hD : IsPullDeg φ D D') (x : D'.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R').left) (z : Z) {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val (hD.psiW.psi (hD.xe x)) (r ≫ hD.g) z J =
      (gw hD.w (r ≫ D'.xK x) z (J ((r ≫ D'.xK x) ≫ proj hD)) (J' (r ≫ D'.xK x)))⁻¹ * val (D'.psi x) r z J' := by
  obtain ⟨b, hb, hcorr⟩ := hD.psi_pr x
  have m₁ : r z ∈ D'.xK x ⁻¹ᵁ ((D.P.L.pull (proj hD)).U (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) ⊓
      D'.P.L.U (J' (r ≫ D'.xK x))) := ⟨mem_pull.2 (hJ ((r ≫ D'.xK x) ≫ proj hD)), hJ' (r ≫ D'.xK x)⟩
  have e₁ := congrArg (gm r z (D'.xK x ⁻¹ᵁ ((D.P.L.pull (proj hD)).U (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) ⊓
      D'.P.L.U (J' (r ≫ D'.xK x))))) (hb (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) (J' (r ≫ D'.xK x)))
  have e₁' := (gm_res _ z _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK x) z
      ((D.P.L.pull (proj hD)).U (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) ⊓ D'.P.L.U (J' (r ≫ D'.xK x))) m₁ _)))
      (gm_res _ z _ m₁ _))))
  refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ hcorr r).symm.trans ((val_of b r z J
    (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) (fun _ => by rw [Category.assoc])).trans (e₁'.trans ?_)))
  rw [zpow_neg_one]
  rfl

theorem psiEven_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), D.PsiEven → D'.PsiEven := by
  intro hG R R' _ _ _ _ φ D D' hD h x
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ using fun χ : (TK R').left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have cW : hD.g ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left = D'.xK x ≫ proj hD := by
    have hx : D'.xK x ≫ proj hD = jK R' ≫ specOf φ ≫ (D.c (hD.xe x)).left := by
      rw [← hD.c_pr x, ← Category.assoc]; rfl
    rw [hx, ← Category.assoc (jK R'), ← hD.g_comm, Category.assoc]; rfl
  have cn : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit _ ≫ D'.c (-x)).left = _
    rw [c_neg, ← Category.assoc, Over.comp_left]
  have e := even_on h hD.psiW (hD.xe x) (𝟙 _ ≫ hD.g) y J hJ
  rw [← map_neg, psi_pull hD _ _ y hJ hJ', psi_pull hD _ _ y hJ hJ', Category.assoc (𝟙 _) hD.g, cW,
    ← Category.assoc (𝟙 _) (D'.xK x), sym_pull hG hD _ y hJ hJ'] at e
  have c' : 𝟙 _ ≫ D'.xK (-x) = (𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left := by rw [cn, Category.assoc]
  rw [c'] at e
  rw [val_mul hJ', val_pull hJ']
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory.PsiEvenPull
