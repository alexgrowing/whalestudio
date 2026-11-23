import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

theorem gen_unique_scal {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) (c : Γ(S₀, ⊤))
    (h : ∀ y J, Good M y J → (val u e y J).val = gs (𝟙 _) y ⊤ c * (val u' e y J).val) (Z : Scheme.{0}) (r : Z ⟶ Y)
    (z : Z) (J) (hJ : Good M z J) : (val u r z J).val = gs (r ≫ p) z ⊤ c * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs (r ≫ p) z ⊤ a * (val u' r z J).val := by
    intro Z r z J hJ
    rw [← Units.mul_inv_eq_iff_eq_mul, ← Units.val_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ,
      val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = c := fn_ext fun y _ => by
    obtain ⟨I, hI⟩ := exists_good' hM y
    have := key _ e y I hI
    rw [h y I hI, he] at this
    exact ((Units.mul_left_inj _).1 this).symm
  rw [← a1]; exact key Z r z J hJ

theorem gs_comp_stalkMap {X Y Z : Scheme.{0}} (σ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (σ z) ∈ U)
    (a : Γ(X, U)) : gs (σ ≫ r) z U a = (σ.stalkMap z).hom (gs r (σ z) U a) := by
  rw [← gs_pull σ r z U h, gs_stalkMap σ z _ h, gs_pull (𝟙 _) r (σ z) U h, Category.id_comp]

theorem gm_comp_stalkMap {X Y Z : Scheme.{0}} (σ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (σ z) ∈ U)
    (a : Γ(X, U)ˣ) : gm (σ ≫ r) z U a = Units.map (σ.stalkMap z).hom.toMonoidHom (gm r (σ z) U a) :=
  Units.ext ((gs_unit (σ ≫ r) z U h a).symm.trans ((gs_comp_stalkMap σ r z U h _).trans
    (congrArg _ (gs_unit r (σ z) U h a))))

theorem stalkMap_injective_of_flat {Y Z : Scheme.{0}} (r : Z ⟶ Y) [Flat r] (z : Z) :
    Function.Injective (r.stalkMap z).hom := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)

theorem toStk_eq {F : Type} [Field F] (z : Sp F) (a : F) : toStk z a = constVal (𝟙 _) z a :=
  (gs_eq (𝟙 _) z ⊤ trivial _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)

theorem toF_X_ne_zero : toF (R := PowerSeries k) F PowerSeries.X ≠ 0 :=
  (map_ne_zero (algebraMap (FractionRing (PowerSeries k)) F)).2
    ((map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries k) _)).2 PowerSeries.X_ne_zero)

def xUnit (k : Type) [Field k] (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (y : Sp F) :
    ((Sp F).presheaf.stalk y)ˣ := Units.map (toStk y).toMonoidHom (Units.mk0 _ (toF_X_ne_zero (k := k) F))

theorem xUnit_zpow (y : Sp F) (n : ℤ) :
    (xUnit k F y ^ n).val = toStk y (toF (R := PowerSeries k) F PowerSeries.X ^ n) := by
  rw [xUnit, ← map_zpow]
  show toStk y _ = _
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

section Values

variable [Algebra (FractionRing k) F]
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) = constF k F x)
  {y : Sp F} {J₀ : (Sp F ⟶ a.D₀.P.A.left) → a.D₀.P.L.ι} {J : (Sp F ⟶ P.toPre.P.A.left) → P.toPre.P.L.ι}
  (hJ₀ : Good a.D₀.P.L y J₀) (hJ : Good P.toPre.P.L y J)

include hW hF hJ₀ hJ

theorem val_psi (χ : a.D₀.X) : val (L := P.toPre.P.L) (P.toPre.psi (e χ)) (jFK (R := PowerSeries k) F) y J =
    wVal w y J₀ J (cP P.toPre (TF (R := PowerSeries k) F) (e χ)).left *
      (xUnit k F y ^ (a.be χ χ / 2) * val (L := a.D₀.P.L) (a.D₀.psi χ) (jFK (R := k) F) y J₀) := by
  let F' := AlgebraicClosure F
  let σ : Sp F' ⟶ Sp F := spMap (algebraMap F F')
  have : Flat σ := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField F) _
  have z : Sp F' := (default : PrimeSpectrum F')
  have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain rfl : y = σ z := Subsingleton.elim _ _
  have s₁ : jFK (R := PowerSeries k) F' = σ ≫ jFK (R := PowerSeries k) F := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have s₂ : jFK (R := k) F' = σ ≫ jFK (R := k) F := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨hp, hv⟩ := (genRel_iff w _ _ _ z).1 (hW.2.2.2.2.2 F' _ (fun x => by
    rw [IsScalarTower.algebraMap_apply (FractionRing k) F F', hF,
      IsScalarTower.algebraMap_apply (FractionRing (PowerSeries k)) F F']; rfl) rfl χ)
  let m : Sp F ⟶ P.toPre.P.A.left := (cP P.toPre (TF (R := PowerSeries k) F) (e χ)).left
  have a₁ : jFK (R := PowerSeries k) F ≫ P.toPre.xK (e χ) = m := (Category.assoc _ _ _).symm
  have a₁' : jFK (R := PowerSeries k) F' ≫ ptK (P.toPre.c (e χ)) = σ ≫ m := by rw [s₁, Category.assoc, a₁]
  have a₂ : jFK (R := k) F ≫ a.D₀.xK χ = m ≫ φ := by
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (a.D₀.c χ).left) ?_)).trans
      (congrArg (fun q => q.left) (push_cP hW (TF (R := PowerSeries k) F) χ)).symm
    show (TF (R := k) F).hom = (TF (R := PowerSeries k) F).hom ≫ _
    rw [TF_hom, TF_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext hF)
  have m₁ : jFK (R := PowerSeries k) F (σ z) ∈ LB.wchart P.toPre.P.L (K := PUnit) (fun _ => ptK (P.toPre.c (e χ)))
      (fun _ => J m) := Set.mem_iInter.2 fun _ => by have := hJ m; rw [← a₁] at this ⊢; exact this
  have m₂ : jFK (R := k) F (σ z) ∈ LB.wchart a.D₀.P.L (K := PUnit) (fun _ => ptK (a.D₀.c χ))
      (fun _ => J₀ (m ≫ φ)) := Set.mem_iInter.2 fun _ => by have := hJ₀ (m ≫ φ); rw [← a₂] at this ⊢; exact this
  have H := hv (fun _ => J m) (fun _ => J₀ (m ≫ φ)) (fun _ => by rw [a₁']; exact hJ₀ (m ≫ φ))
    (fun _ => by rw [a₁']; exact hJ m)
  rw [gm_pullGen _ _ _ _ _ _ _ _ (Set.mem_iInter.2 fun _ => by
      show (jFK (R := PowerSeries k) F' ≫ ptK (P.toPre.c (e χ))) z ∈ P.toPre.P.L.U (J m)
      rw [a₁']; exact hJ m),
    gm_pullGen _ _ _ _ _ _ _ _ (Set.mem_iInter.2 fun _ => by
      show (jFK (R := k) F' ≫ ptK (a.D₀.c χ)) z ∈ a.D₀.P.L.U (J₀ (m ≫ φ))
      rw [s₂, Category.assoc, a₂]; exact hJ₀ (m ≫ φ)),
    Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp, a₁', s₁, s₂] at H
  have g₁ := gm_comp_stalkMap σ _ z _ m₁ ((P.toPre.psi (e χ)).s fun _ => J m)
  have g₂ := gm_comp_stalkMap σ _ z _ m₂ ((a.D₀.psi χ).s fun _ => J₀ (m ≫ φ))
  have g₃ := gm_comp_stalkMap σ m z ((a.D₀.P.L.pull φ).U (fun _ => J₀ (m ≫ φ)) ⊓ P.toPre.P.L.U (J m))
    ⟨mem_pull.2 (hJ₀ (m ≫ φ)), hJ m⟩ (w.s (fun _ => J₀ (m ≫ φ), J m))
  replace H := (congrArg Units.val (congrArg₂ (· * ·) (congrArg (·⁻¹) g₃) g₁)).symm.trans
    (H.trans (congrArg₂ (· * ·) rfl (congrArg Units.val g₂)))
  have hx : toStk z (algebraMap (FractionRing (PowerSeries k)) F' (algebraMap (PowerSeries k) _ PowerSeries.X) ^
      (a.be χ χ / 2)) = (σ.stalkMap z).hom (xUnit k F (σ z) ^ (a.be χ χ / 2)).val := by
    rw [xUnit_zpow, toStk_eq, toStk_eq, IsScalarTower.algebraMap_apply (FractionRing (PowerSeries k)) F F',
      ← map_zpow₀, ← constVal_specMap, Category.id_comp]
    exact (congrArg (fun q => gs q z ⊤ _) (Category.comp_id σ).symm).trans (gs_comp_stalkMap σ (𝟙 _) z ⊤ trivial _)
  rw [hx] at H
  rw [val_of _ _ _ J (fun _ => J m) (fun _ => congrArg J a₁),
    val_of _ _ _ J₀ (fun _ => J₀ (m ≫ φ)) (fun _ => congrArg J₀ a₂), ← inv_mul_eq_iff_eq_mul]
  refine Units.ext (stalkMap_injective_of_flat σ z ?_)
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
  rw [← map_inv, Units.val_mul] at H
  exact H

theorem val_rig : val (L := a.D₀.P.L) a.D₀.rigK (jFK (R := k) F) y J₀ =
    wVal w y J₀ J (1 : TF (R := PowerSeries k) F ⟶ P.toPre.P.A).left *
      val (L := P.toPre.P.L) P.toPre.rigK (jFK (R := PowerSeries k) F) y J := by
  have pm := (maps_iff w _ (fun _ => eSec a.D₀.P.A) _ P.toPre.rig a.D₀.rig (spMap (PowerSeries.C (R := k))) _
    (rigPull_le φ (spMap (PowerSeries.C (R := k))) he a.D₀.P.L) (fun _ => rfl)).1 hW.2.2.1
  have e₁ := pmaps_val (fun _ => he) pm (TF (R := PowerSeries k) F).hom hJ₀ hJ
  have hT : (TF (R := PowerSeries k) F).hom ≫ spMap (PowerSeries.C (R := k)) = (TF (R := k) F).hom := by
    rw [TF_hom, TF_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext hF).symm
  rw [Fintype.prod_unique, zpow_one] at e₁
  refine (val_pull hJ₀ _ _ _).trans (Eq.trans ?_ (e₁.trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _).symm)))
  exact congrArg (fun q => val (L := a.D₀.P.L) a.D₀.rig q y J₀) hT.symm

end Values

theorem val_tau {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z}
    {J} (hJ : Good D.P.L z J) (x x' : D.X) : val (D.tau x x') r z J =
      val (D.psi (x + x')) r z J * (val (D.psi x) r z J)⁻¹ * (val (D.psi x') r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem fe_alg {U : Type} [CommGroup U] (j : ℕ) (n₁ n₂ n₃ : ℤ) {u u' x ψ₁ ψ₂ ψ₃ ρ χ₁ χ₂ χ₃ ρ₀ o m a s t : U}
    (v₁ : χ₁ * χ₂⁻¹ * χ₃⁻¹ * ρ₀⁻¹ * (χ₂ ^ j * ρ₀ ^ j) =
      o ^ ((j : ℤ) - 1) * t * t⁻¹ * o * (m ^ ((j : ℤ) - 1) * s * a⁻¹ * o)⁻¹ * u')
    (v₂ : u = ψ₁ * ψ₂⁻¹ * ψ₃⁻¹ * ρ⁻¹ * (ψ₂ ^ j * ρ ^ j)) (q₁ : ψ₁ = s * (x ^ (n₁ + n₂ + n₃) * χ₁))
    (q₂ : ψ₂ = m * (x ^ n₁ * χ₂)) (q₃ : ψ₃ = a * (x ^ n₂ * χ₃)) (q₄ : ρ₀ = o * ρ) :
    u = x ^ (j * n₁ + n₃) * u' := by
  apply Additive.ofMul.injective
  have b₁ := congrArg Additive.ofMul v₁
  have b₂ := congrArg Additive.ofMul v₂
  have c₁ := congrArg Additive.ofMul q₁
  have c₂ := congrArg Additive.ofMul q₂
  have c₃ := congrArg Additive.ofMul q₃
  have c₄ := congrArg Additive.ofMul q₄
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow] at b₁ b₂ c₁ c₂ c₃ c₄ ⊢
  linear_combination (norm := module) b₂ + b₁ + c₁ + ((j : ℤ) - 1) • c₂ - c₃ - ((j : ℤ) - 1) • c₄

theorem be_add_div_two (a : ArcIn D l β k b) (x x' : a.D₀.X) :
    a.be (x + x') (x + x') / 2 = a.be x x / 2 + a.be x' x' / 2 + a.be x x' := by
  have d₁ : (2 : ℤ) ∣ a.be x x := (Dvd.intro _ rfl).trans (a.be_dvd x x)
  have d₂ : (2 : ℤ) ∣ a.be x' x' := (Dvd.intro _ rfl).trans (a.be_dvd x' x')
  have s := a.be_symm x' x
  simp only [map_add, LinearMap.add_apply]
  omega

include hW in
theorem trF_comp_φ (mu : a.D₀.X) : (DegPre.trF P.toPre F (e mu)).left ≫ (DegPre.prB P.toPre F).left ≫ φ =
    ((DegPre.prB P.toPre F).left ≫ φ) ≫ (trB a.D₀ mu).left := by
  rw [← Category.assoc, ← Over.comp_left, trF_prB, Over.comp_left, Category.assoc, Category.assoc]
  exact congrArg _ (famφB_comp hW mu 1)

include hW in
theorem deltaφ_comp (α mu : a.D₀.X) (i : Fin 4 ⊕ Fin 4) : DegPre.deltaφ P.toPre F j (e α) (e mu) i ≫ φ =
    ((DegPre.prB P.toPre F).left ≫ φ) ≫
      Sum.elim (a.D₀.famφB (α + j • mu)) (fun i => (trB a.D₀ mu).left ≫ a.D₀.famφB α i) i := by
  rcases i with i | i
  · show DegPre.famφ P.toPre F (e α + j • e mu) i ≫ φ = _
    rw [← map_nsmul, ← map_add]
    exact famφ_comp hW F _ i
  · show ((DegPre.trF P.toPre F (e mu)).left ≫ DegPre.famφ P.toPre F (e α) i) ≫ φ = _ ≫ _ ≫ _
    rw [Category.assoc, famφ_comp hW, ← Category.assoc, trF_comp_φ hW, Category.assoc]

include hW hG in

theorem val_fe (α mu : a.D₀.X)
    (u u' : LB.Gen (LB.LinComb P.toPre.P.L (DegPre.deltaφ P.toPre F j (e α) (e mu)) (DegPre.deltaε j)))
    (hu : u.IsGen) (hc : LB.Gen.Corr P.toPre.P.L _ _ _ _ (LB.pullGen P.toPre.P.L _ _ u (DegPre.zF P.toPre F).left)
      (DegPre.famMult P.toPre F j (e mu) (e α))) (hu' : u'.IsGen)
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF P.toPre F).left) (z : Z) J₀ J, Good a.D₀.P.L z J₀ →
      Good P.toPre.P.L z J → val (feGen a.D₀ j mu α) (r ≫ (DegPre.prB P.toPre F).left ≫ φ) z J₀ =
        (∏ i, wVal w z J₀ J (r ≫ DegPre.deltaφ P.toPre F j (e α) (e mu) i) ^ DegPre.deltaε j i) * val u' r z J)
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF P.toPre F).left) {z : Z} {J} (hJ : Good P.toPre.P.L z J) :
    (val u r z J).val = constVal (r ≫ strF P.toPre F) z
      (toF (R := PowerSeries k) F PowerSeries.X ^ expo a j α mu) * (val u' r z J).val := by
  let _ : Algebra (FractionRing k) F := (IsFractionRing.lift (K := FractionRing k) (constF k F).injective).toAlgebra
  have hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) = constF k F x := fun x =>
    IsFractionRing.lift_algebraMap (constF k F).injective x
  have z₁ : DegPre.zF P.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF P.toPre F ≫ DegPre.prB P.toPre F = 1 := lift_snd _ _
  refine gen_unique_scal P.toPre.P.isLB (strF P.toPre F) (DegPre.zF P.toPre F).left (congrArg (fun q => q.left) z₁)
    (surj_appTop P.toPre F hG) hu hu' _ (fun y J hJ => ?_) Z r z J hJ
  obtain ⟨J₀, hJ₀⟩ := exists_good' a.D₀.P.isLB y
  let κ : Over.mk ((TF (R := PowerSeries k) F).hom ≫ spMap (PowerSeries.C (R := k))) ⟶ TK k :=
    Over.homMk (jFK (R := k) F) (by
      show (TF (R := k) F).hom = (TF (R := PowerSeries k) F).hom ≫ _
      rw [TF_hom, TF_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext hF))
  have C : IsCub (th a.D₀ (T := Over.mk ((TF (R := PowerSeries k) F).hom ≫ spMap (PowerSeries.C (R := k)))) y J₀) :=
    isCub_cubV a.D₀.cub hJ₀
  have v₀ := val_feGen a.D₀ j mu α (pushHom hW.1 (TF (R := PowerSeries k) F) 1) κ hJ₀
  have p₀ : (DegPre.zF P.toPre F).left ≫ (DegPre.prB P.toPre F).left ≫ φ =
      (pushHom hW.1 (TF (R := PowerSeries k) F) 1).left := by
    rw [← Category.assoc, ← Over.comp_left, z₂]; rfl
  have v₁ := hv _ (DegPre.zF P.toPre F).left y J₀ J hJ₀ hJ
  rw [p₀] at v₁
  replace v₁ := v₀.symm.trans v₁
  rw [map_one, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul, val_tau _ _ hJ₀] at v₁
  have p₁ := prod_fam P.toPre F (DegPre.zF P.toPre F) (e α + j • e mu) j (wVal w y J₀ J)
  have p₂ := prod_fam P.toPre F (DegPre.zF P.toPre F ≫ DegPre.trF P.toPre F (e mu)) (e α) j (wVal w y J₀ J)
  have p₃ : (DegPre.zF P.toPre F ≫ DegPre.trF P.toPre F (e mu)) ≫ DegPre.prB P.toPre F = cP P.toPre _ (e mu) := by
    rw [Category.assoc, trF_prB, ← Category.assoc, z₂, MonObj.comp_mul, comp_cP, Category.comp_id, _root_.one_mul]
  rw [z₂, _root_.mul_one] at p₁
  rw [p₃] at p₂
  simp only [Over.comp_left, Category.assoc] at p₂
  have p₄ := prod_sum₂ (K := Fin 4) (K' := Fin 4) (fun i => wVal w y J₀ J ((DegPre.zF P.toPre F).left ≫
    DegPre.deltaφ P.toPre F j (e α) (e mu) i) ^ DegPre.deltaε j i) p₁ (prod_neg _ _ p₂)
  replace v₁ := v₁.trans (congrArg (· * _) p₄)
  have v₂ := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at v₂
  replace v₂ := v₂.trans (val_famMult (𝟙 (TF (R := PowerSeries k) F)) hJ j (e mu) (e α))
  rw [UUA.val_powGen', UUA.val_powGen', val_tau _ _ hJ, Over.id_left, Category.id_comp, ← map_add] at v₂
  have q₁ := val_psi hW F hF hJ₀ hJ (mu + α)
  have q₂ := val_psi hW F hF hJ₀ hJ mu
  have q₃ := val_psi hW F hF hJ₀ hJ α
  have q₄ := val_rig hW F hF hJ₀ hJ
  rw [be_add_div_two, map_add, cPoint_add, mul_comm (cP P.toPre _ (e mu)), ← map_add] at q₁
  refine Eq.trans ?_ (congrArg (· * _) ((xUnit_zpow F y _).trans (toStk_eq y _)))
  rw [← Units.val_mul]
  exact congrArg Units.val (fe_alg j _ _ _ v₁ v₂ q₁ q₂ q₃ q₄)

theorem constFam_add_nsmul (α mu : a.D₀.X) (s₀ : SecBMod a.D₀ j α) :
    famComp P.toPre F j (e (α + j • mu)) (constFam hW F hG hj α s₀) =
      toF (R := PowerSeries k) F PowerSeries.X ^ expo a j α mu •
        pullF hW F j (α + j • mu) (feTranslate a.D₀ j mu α s₀) := by
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := P.toPre) (F := F) hG j (e mu) (e α)
  obtain ⟨u', hu', hv⟩ := exists_gen_through hW.2.1 a.D₀.P.isLB P.toPre.P.isLB (deltaφ_comp hW F α mu)
    (feGen a.D₀ j mu α) (feGen_isGen a.D₀ j mu α)
  refine sec_ext' P.toPre.P.isLB fun y J hJ => ?_
  obtain ⟨J₀, hJ₀⟩ := exists_good' a.D₀.P.isLB y
  have key : ∀ χ, e α + j • e mu = χ → sval ((constFam hW F hG hj α s₀).s χ) (𝟙 _) y J =
      sval ((constFam hW F hG hj α s₀).s (e α)) (𝟙 _ ≫ (DegPre.trF P.toPre F (e mu)).left) y J *
        (val u (𝟙 _) y J).val := by
    rintro _ rfl
    exact (secRel_iff P.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 ((constFam hW F hG hj α s₀).fe _ _ u hu hc) _ _ y J hJ
  have hi : e α + j • e mu = e (α + j • mu) := by rw [map_add, map_nsmul]
  refine (key _ hi).trans (Eq.trans ?_ (sval_smul' hJ _ _ _).symm)
  rw [show (constFam hW F hG hj α s₀).s (e α) = pullF hW F j α s₀ from constFam_self hW F hG hj α s₀,
    val_fe hW F hG α mu u u' hu hc hu' hv _ hJ, mul_left_comm]
  refine congrArg _ ?_
  have a₁ := (secThrough_pullF hW F j (α + j • mu) (feTranslate a.D₀ j mu α s₀)).sval (famφ_comp hW F _) (𝟙 _) hJ₀ hJ
  have a₂ := (secThrough_pullF hW F j α s₀).sval (famφ_comp hW F _)
    (𝟙 _ ≫ (DegPre.trF P.toPre F (e mu)).left) hJ₀ hJ
  have a₃ := hv _ (𝟙 _) y J₀ J hJ₀ hJ
  have a₄ := sval_feTranslate a.D₀ j mu α s₀ (𝟙 _ ≫ (DegPre.prB P.toPre F).left ≫ φ) hJ₀
  rw [Category.assoc, trF_comp_φ hW, ← Category.assoc] at a₂
  have a₅ := prod_sum₂ (K := Fin 4) (K' := Fin 4) (fun i => wVal w y J₀ J (𝟙 _ ≫
    DegPre.deltaφ P.toPre F j (e α) (e mu) i) ^ DegPre.deltaε j i)
    (c := ∏ i, wVal w y J₀ J (𝟙 _ ≫ DegPre.famφ P.toPre F (e (α + j • mu)) i) ^ DegPre.famε j i) (by rw [← hi]; rfl)
    (prod_neg _ _ (c := ∏ i, wVal w y J₀ J ((𝟙 _ ≫ (DegPre.trF P.toPre F (e mu)).left) ≫
      DegPre.famφ P.toPre F (e α) i) ^ DegPre.famε j i) (by simp only [Category.assoc]; rfl))
  rw [a₁, a₂, a₃, a₅] at a₄
  refine (Units.mul_right_inj (∏ i, wVal w y J₀ J (𝟙 _ ≫ DegPre.famφ P.toPre F (e (α + j • mu)) i) ^
    DegPre.famε j i)).1 (Eq.trans ?_ a₄.symm)
  generalize (∏ i, wVal w y J₀ J ((𝟙 _ ≫ (DegPre.trF P.toPre F (e mu)).left) ≫
      DegPre.famφ P.toPre F (e α) i) ^ DegPre.famε j i) = W
  simp only [Units.val_mul]
  linear_combination (-(sval (pullF hW F j α s₀) (𝟙 _ ≫ (DegPre.trF P.toPre F (e mu)).left) y J *
    (val u' (𝟙 _) y J).val * (∏ i, wVal w y J₀ J (𝟙 _ ≫ DegPre.famφ P.toPre F (e (α + j • mu)) i) ^
    DegPre.famε j i).val)) * W.mul_inv

end GlobalTheory.ConstFam
