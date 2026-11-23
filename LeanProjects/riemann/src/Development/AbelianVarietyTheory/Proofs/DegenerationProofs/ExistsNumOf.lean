import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultPsiEvenOverExtensionField

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.GaugeValues

theorem vF_eq {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (z : Sp F) (t : LB.Gen (LB.LinComb L φ ε))
    (r : Sp F ⟶ Y) : (((TorusExt.stalkUnits z).symm (val t r z J) : Fˣ) : F) = vF t r J := by
  have h : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ φ k)) := fun w _ =>
    Good.mem (L := L) (z := w) (J := J) (fun ψ => hJ ψ trivial) φ r
  refine (TorusExt.stalkConst z).injective ?_
  rw [← TorusExt.stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (gs_unit r z _ (h trivial) _).symm.trans (TorusExt.gs_eq_stalkConst r z h _)

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem val_sym_one {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J} (hJ : Good D.P.L z J) :
    val D.sym (1 : T ⟶ D.P.A).left z J = 1 := by
  have s := val_corr hJ D.sym_rig (toUnit T).left
  rw [val_pull hJ, val_one] at s
  exact s

theorem prod_sym {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i : Fin 2, h (x.left ≫ ![(ι[D.P.A]).left, 𝟙 D.P.A.left] i) ^ (![1, -1] : Fin 2 → ℤ) i =
      h (x⁻¹).left * (h x.left)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (x ≫ ι[D.P.A]).left ^ (1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (-1 : ℤ) = _
  rw [zpow_one, zpow_neg_one, Category.comp_id]; rfl

theorem val_sym_mul (hG : GlobalFnsSt) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J} (hJ : Good D.P.L z J)
    (x y : T ⟶ D.P.A) :
    val D.sym (x * y).left z J * cubV D.cub z J x x⁻¹ y⁻¹ =
      val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J y y⁻¹ x := by
  let p : D.P.A ⊗ D.P.A ⟶ D.P.A := fst _ _
  let q : D.P.A ⊗ D.P.A ⟶ D.P.A := snd _ _
  have ev : ∀ {T' : Over (Spec (CommRingCat.of R))} (a b : T' ⟶ D.P.A) {z : T'.left} {J}, Good D.P.L z J →
      val (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.sym (p * q).left)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift p (lift p⁻¹ q⁻¹)).left)) (lift a b).left z J =
        val D.sym (a * b).left z J * cubV D.cub z J a a⁻¹ b⁻¹ ∧
      val (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.sym p.left)
        (LB.pullGen D.P.L _ _ D.sym q.left))
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift q (lift q⁻¹ p)).left)) (lift a b).left z J =
        val D.sym a.left z J * val D.sym b.left z J * cubV D.cub z J b b⁻¹ a := by
    intro T' a b z J hJ
    have e₁ : lift a b ≫ p = a := lift_fst _ _
    have e₂ : lift a b ≫ q = b := lift_snd _ _
    have e₃ : lift a b ≫ (p * q) = a * b := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂])
    have e₄ : lift a b ≫ p⁻¹ = a⁻¹ := (map_inv (preHom (lift a b)) p).trans (congrArg (·⁻¹) e₁)
    have e₅ : lift a b ≫ q⁻¹ = b⁻¹ := (map_inv (preHom (lift a b)) q).trans (congrArg (·⁻¹) e₂)
    have vs : ∀ w : D.P.A ⊗ D.P.A ⟶ D.P.A, val (LB.pullGen D.P.L _ _ D.sym w.left) (lift a b).left z J =
        val D.sym (lift a b ≫ w).left z J := fun w => val_pull hJ _ _ _
    refine ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs _) (val_cub D.cub _ hJ _ _ _))).trans ?_,
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs _) (vs _)))
        (val_cub D.cub _ hJ _ _ _))).trans ?_⟩
    · rw [e₁, e₃, e₄, e₅]
    · rw [e₁, e₂, e₅]
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A ⊗ D.P.A := lift 1 1
  have he : e.left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  refine (ev x y hJ).1.symm.trans (Eq.trans (gen_unique' D.P.isLB (fun V _ k => ?_) _ e.left he
    (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.sym_gen _) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)
      (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (fun w I hI => ?_) _ (lift x y).left z J hJ) (ev x y hJ).2)
  · refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := thK) (U := V) _
      (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym D p k) (prod_sym D q k))
      (prod_cub q q⁻¹ p k)).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 2) (K' := thK) (U := V) _
        (prod_sym D (p * q) k) (prod_cub p p⁻¹ q⁻¹ k)).symm)
    rw [mul_inv_cancel, mul_inv_cancel, _root_.one_mul, _root_.one_mul, mul_inv, mul_comm q p, mul_comm q⁻¹ p]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) w I) := isCub_cubV D.cub hI
    refine (ev 1 1 hI).1.trans (Eq.trans ?_ (ev 1 1 hI).2.symm)
    rw [_root_.mul_one, C.face, C.face, val_sym_one D hI, _root_.mul_one, _root_.mul_one]

theorem exists_numOf : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∀ th : H0 D.P.L 1, (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → ∃ (N : NumD F) (ν : NumOf D F N), ν.J = J ∧ ν.th = th := by
  intro hL R _ _ D hE hB F _ _ J hJ th hth
  let z : (TF (R := R) F).left := IsLocalRing.closedPoint F
  have g : Good D.P.L z J := fun ψ => hJ ψ trivial
  let u : ((TF (R := R) F).left.presheaf.stalk z)ˣ ≃* Fˣ := (TorusExt.stalkUnits (F := F) z).symm
  have C : IsCub (cubV D.cub (T := TF (R := R) F) z J) := isCub_cubV D.cub g
  let ρ : ((TF (R := R) F).left.presheaf.stalk z)ˣ := val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A)
    (ε := fun _ => 1) D.rig (TF (R := R) F).hom z J
  let P : D.X → ((TF (R := R) F).left.presheaf.stalk z)ˣ := fun χ =>
    val (Z := (TF (R := R) F).left) (D.psi χ) (jFK (R := R) F) z J
  obtain ⟨b, e⟩ := TauValues.main R D F
  let N : NumD F :=
    { A := TF (R := R) F ⟶ D.P.A
      θ := fun x y w => u (cubV D.cub z J x y w)
      cub := ⟨fun x y => (congrArg u (C.face x y)).trans (map_one u), fun x y w => congrArg u (C.s01 x y w),
        fun x y w => congrArg u (C.s12 x y w), fun x x' x'' y =>
          (map_mul u _ _).symm.trans ((congrArg u (C.coc x x' x'' y)).trans (map_mul u _ _))⟩
      σ := fun x => u (val D.sym x.left z J)
      σ_one := (congrArg u (val_sym_one D g)).trans (map_one u)
      σ_mul := fun x y => by
        simpa only [map_mul] using congrArg u (val_sym_mul D hL.globalFns g x y)
      th := fun x => sF th x.left J * ((u ρ)⁻¹ : Fˣ)
      X := D.X
      c := DegPre.cF D F
      c_add := fun a a' => (congrArg (toUnit _ ≫ ·) (D.c_add a a')).trans (MonObj.comp_mul _ _ _)
      ψ := fun χ => u (P χ * ρ)
      even := fun χ => by
        have h : P (-χ) * val D.sym (DegPre.cF D F χ).left z J = P χ := e.2 hE z J g χ
        rw [← map_mul, mul_right_comm, h]
      bimult := fun a a' m => by
        have h : P (a + a' + m) * P a * P a' * P m * ρ *
            cubV D.cub z J (DegPre.cF D F a) (DegPre.cF D F a') (DegPre.cF D F m) =
            P (a + a') * P (a + m) * P (a' + m) := b.2 hB z J g a a' m
        simp only [← map_div, ← map_mul]
        refine congrArg u (Additive.ofMul.injective ?_)
        have h' := congrArg Additive.ofMul h
        simp only [ofMul_mul, ofMul_div] at h' ⊢
        linear_combination (norm := abel) h' }
  have hρ : ((u ρ : Fˣ) : F) = vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
      (TF (R := R) F).hom J := vF_eq hJ z _ _
  exact ⟨N,
    { J := J, good := hJ, th := th, th_gen := hth, eA := MulEquiv.refl _, eX := AddEquiv.refl _
      c_eq := fun _ => rfl
      θ_eq := fun _ _ _ => vF_eq hJ z _ _
      σ_eq := fun _ => vF_eq hJ z _ _
      th_eq := fun x => (congrArg (N.th x * ·) hρ.symm).trans (Units.inv_mul_cancel_right _ _)
      ψ_eq := fun χ => (congrArg Units.val (map_mul u _ _)).trans ((Units.val_mul _ _).trans
        (congrArg₂ (· * ·) (vF_eq hJ z _ _) hρ)) }, rfl, rfl⟩

end GlobalTheory.GaugeValues
