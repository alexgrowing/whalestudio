import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProductStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.CupA

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem spOver_left {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (spOver (R := R) φ).left = spMap (φ : D →+* D') := rfl

theorem pointWithZeroSecondCoord_left_comp_fst {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (pt0 B x).left ≫ (fst A B).left = x.left := by
  rw [← Over.comp_left]; unfold pt0; rw [lift_fst]

theorem ptV_fst (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (ptV v x).left ≫ (fst A B).left = spMap (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) ≫ x.left := by
  rw [← Over.comp_left]; unfold ptV; rw [lift_fst]; rfl

theorem ptV_snd (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (ptV v x).left ≫ (snd A B).left = spMap (EpsWeil.epsMap R D : DualNumber R →+* DualNumber D) ≫ v.left := by
  rw [← Over.comp_left]; unfold ptV; rw [lift_snd]; rfl

theorem pointWithZeroSecondCoord_left_comp_snd (v : epsR R ⟶ B) (hv : IsTangent v) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (pt0 B x).left ≫ (snd A B).left =
      spMap (TrivSqZeroExt.fstHom R D D : DualNumber D →+* D) ≫ spMap (EpsWeil.epsMap R D : DualNumber R →+* DualNumber D) ≫ v.left := by
  rw [← Over.comp_left]; unfold pt0; rw [lift_snd]
  have e1 : (spOver (TrivSqZeroExt.fstHom R D D) ≫ spOver (EpsWeil.epsMap R D) ≫ v) = (1 : Pt B D) := by
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R D D).comp (EpsWeil.epsMap R D) = (Algebra.ofId R D).comp (TrivSqZeroExt.fstHom R R R) := by
      apply AlgHom.ext; intro c
      simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']
    rw [this, ← spOver_comp, Category.assoc]
    have h1 : spOver (TrivSqZeroExt.fstHom R R R) ≫ v = (1 : Over.mk (spMap (algebraMap R R)) ⟶ B) := by
      refine Over.OverMorphism.ext ?_
      rw [Over.comp_left, spOver_left, Hom.one_def, Over.comp_left]
      have : (CartesianMonoidalCategory.toUnit (Over.mk (spMap (algebraMap R R)))).left = 𝟙 (Sp R) := by
        have h := Over.w (CartesianMonoidalCategory.toUnit (Over.mk (spMap (algebraMap R R))))
        refine (Category.comp_id _).symm.trans (h.trans ?_)
        exact Spec.map_id _
      rw [this]
      exact hv.trans (Category.id_comp _).symm
    rw [h1, MonObj.comp_one]
  rw [← e1]; rfl

theorem epsMap_fst {D : Type} [CommRing D] [Algebra R D] (c : DualNumber R) :
    (EpsWeil.epsMap R D c).fst = algebraMap R D c.fst := by
  simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem epsMap_inl {D : Type} [CommRing D] [Algebra R D] (b : R) :
    EpsWeil.epsMap R D (TrivSqZeroExt.inl b) = TrivSqZeroExt.inl (algebraMap R D b) := by
  simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem epsMap_inr {D : Type} [CommRing D] [Algebra R D] (b : R) :
    EpsWeil.epsMap R D (TrivSqZeroExt.inr b) = TrivSqZeroExt.inr (algebraMap R D b) := by
  ext <;> simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl', Algebra.smul_def]

theorem snd_epsHom' {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z : DualNumber D) : (epsHom φ z).snd = φ z.snd := by
  simp [epsHom, DualNumber.lift_apply_apply]

theorem epsHom_inl' {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (r : D) : epsHom φ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (φ r) := by
  ext
  · simp [epsHom, DualNumber.lift_apply_apply]
  · simp [snd_epsHom']

theorem dualVal_eq (v : epsR R ⟶ B) (β : Form (B.hom ≫ 𝟙 _)) :
    (SqExt.dual R).val v.left (pt_w v) β.1 = TrivSqZeroExt.inr (tanVal v β) := by
  ext
  · exact (SqExt.dual R).π_val v.left (pt_w v) β
  · exact (tanVal_apply v β).symm

def eA (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    m₁.functor.obj (trivAt (pt0 B x)) ⟶ m₁.functor.obj (trivAt (ptV v x)) where
  φ := { (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) with
    commutes' := fun r ↦ (TrivSqZeroExt.inlAlgHom R D D).commutes r }
  φ₀ := (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D)
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) ≫ (pt0 B x).left ≫ (fst A B).left =
      (ptV v x).left ≫ (fst A B).left
    rw [pointWithZeroSecondCoord_left_comp_fst, ptV_fst]

def uA (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    trivAt x ⟶ m₁.functor.obj (trivAt (pt0 B x)) where
  φ := { RingHom.id D with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id D
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (RingHom.id D) ≫ x.left = (pt0 B x).left ≫ (fst A B).left
    rw [pointWithZeroSecondCoord_left_comp_fst, spMap_id]
    exact Category.id_comp _

abbrev yV (v : epsR R ⟶ B) (D : Type) [CommRing D] [Algebra R D] : Sp (DualNumber D) ⟶ B.left :=
  spMap (EpsWeil.epsMap R D : DualNumber R →+* DualNumber D) ≫ v.left

theorem yV_w (v : epsR R ⟶ B) (D : Type) [CommRing D] [Algebra R D] :
    yV v D ≫ B.hom ≫ 𝟙 _ = spMap (algebraMap R (epsExt R D).C) :=
  pt_w (spOver (EpsWeil.epsMap R D) ≫ v)

section Bside

variable (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
  (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D)

def cB (hv : IsTangent v) : (epsExt R D).thick _ ((epsExt R D).red_w (yV_w v D)) ⟶ m₂.functor.obj (thickAt B x) where
  φ := { RingHom.id (DualNumber D) with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id D
  comm := fun _ ↦ rfl
  dp := (DividedPowers.DPMorphism.id _).isDPMorphism
  pt := by
    change spMap (RingHom.id D) ≫ spMap (TrivSqZeroExt.fstHom R D D : DualNumber D →+* D) ≫ yV v D =
      (pt0 B x).left ≫ (snd A B).left
    rw [pointWithZeroSecondCoord_left_comp_snd v hv, spMap_id]
    exact Category.id_comp _

def u0B (hv : IsTangent v) : Thick.triv (epsExt R D).B _ ((epsExt R D).red_w (yV_w v D)) ⟶ m₂.functor.obj (trivAt (pt0 B x)) where
  φ := { RingHom.id D with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id D
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (RingHom.id D) ≫ spMap (TrivSqZeroExt.fstHom R D D : DualNumber D →+* D) ≫ yV v D =
      (pt0 B x).left ≫ (snd A B).left
    rw [pointWithZeroSecondCoord_left_comp_snd v hv, spMap_id]
    exact Category.id_comp _

def u1B : Thick.triv (epsExt R D).C (yV v D) (yV_w v D) ⟶ m₂.functor.obj (trivAt (ptV v x)) where
  φ := { RingHom.id (DualNumber D) with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id (DualNumber D)
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (RingHom.id (DualNumber D)) ≫ yV v D = (ptV v x).left ≫ (snd A B).left
    rw [ptV_snd, spMap_id]
    exact Category.id_comp _

theorem bval (hv : IsTangent v) (β : Form (B.hom ≫ 𝟙 _)) (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x)
    (hs : ∀ r, s.φ r = TrivSqZeroExt.inl r) (hi : ∀ r, i.φ r = r) :
    ev β.1 (m₂.functor.map s) - ev β.1 (m₂.functor.map i) =
      TrivSqZeroExt.inr (algebraMap R D (tanVal v β)) := by
  let E := epsExt R D
  have k1 := Form.ev_sq β (u0B m₂ v x hv) (m₂.functor.map s) (E.secHom (E.red_w (yV_w v D)) E.i E.π_i)
    (cB m₂ v x hv) rfl rfl (fun r ↦ by
      change s.φ r = TrivSqZeroExt.inl r
      exact hs r)
  have k2 := Form.ev_sq β (u1B m₂ v x) (m₂.functor.map i) (E.idHom (yV_w v D))
    (cB m₂ v x hv) rfl rfl (fun r ↦ by
      change i.φ r = r
      exact hi r)
  rw [k1, k2]
  rw [add_sub_add_right_eq_sub, ← map_sub]
  have vm := (SqExt.dual R).val_map E (EpsWeil.epsMap R D) (Algebra.ofId R D)
    (fun c ↦ (epsMap_fst c).symm) (fun b ↦ epsMap_inl b) v.left (pt_w v) (yV v D) (yV_w v D) rfl β
  calc _ = E.val (yV v D) (yV_w v D) β.1 := rfl
    _ = _ := by rw [vm, dualVal_eq]; exact epsMap_inr _

end Bside

theorem alg {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (t : R)
    (Ae Ai As Bi : DualNumber D) (Bτ Bi' Bs' Ab Ae' X1 X2 X3 X4 Y1 Y2 W : DualNumber D') (Aa fvv fvt C' Z : D') (C : D)
    (hX1 : X1 = epsHom φ As) (hX2 : X2 = TrivSqZeroExt.inl Aa) (hX3 : X3 = epsHom φ Ai) (hX4 : Ab = X4)
    (hY1 : Y1 = TrivSqZeroExt.inl Aa) (hY2 : Y2 = epsHom φ Ae) (hW : W = epsHom φ Bi) (hZ : Z = φ C)
    (hfvt : fvt = (-t) • fvv)
    (hAs : As = Ae + Ai) (hAb : Y1 + Ae' = Y2 + Ab) (hAa : fvv + C' = Z + Aa)
    (hBτ : Bi' = W + Bτ) (hBs : Bs' - Bi' = TrivSqZeroExt.inr (algebraMap R D' t)) :
    (X1 * Bτ - X2 * Bs' - X3 * Bτ + X4 * Bi').snd + -fvt =
      ((Ae' * Bi').snd - algebraMap R D' t * C') - φ ((Ae * Bi).snd - algebraMap R D t * C) := by
  subst hX1 hX2 hX3 hX4 hY1 hY2 hW hZ hfvt
  have h1 : epsHom φ As = epsHom φ Ae + epsHom φ Ai := by rw [hAs, map_add]
  have key : epsHom φ As * Bτ - TrivSqZeroExt.inl Aa * Bs' - epsHom φ Ai * Bτ + Ab * Bi' =
      Ae' * Bi' - epsHom φ (Ae * Bi) - TrivSqZeroExt.inl Aa * TrivSqZeroExt.inr (algebraMap R D' t) := by
    rw [map_mul]
    linear_combination Bτ * h1 - Bi' * hAb - epsHom φ Ae * hBτ - TrivSqZeroExt.inl Aa * hBs
  rw [key, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_sub, snd_epsHom', TrivSqZeroExt.inl_mul_inr,
    TrivSqZeroExt.snd_inr, smul_eq_mul, map_sub, map_mul, AlgHom.commutes, Algebra.smul_def, map_neg]
  linear_combination (algebraMap R D' t) * hAa

open Classical in

def kFn (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (v : epsR R ⟶ B) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Form (B.hom ≫ 𝟙 _)) : Fn0 A := fun D _ _ x ↦
  if h : ∃ i : trivAt (ptV v x) ⟶ thickAt B x, ∀ r, i.φ r = r then
    ((show DualNumber D from ev a (eA m₁ v x)) * (show DualNumber D from ev β.1 (m₂.functor.map h.choose))).snd -
      algebraMap R D (tanVal v β) * (show D from ev a (uA m₁ x))
  else 0

theorem kFn_eq (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (v : epsR R ⟶ B) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Form (B.hom ≫ 𝟙 _)) {D : Type} [CommRing D]
    [Algebra R D] (x : Pt A D) (i : trivAt (ptV v x) ⟶ thickAt B x) (hi : ∀ r, i.φ r = r) :
    kFn m₁ m₂ v a β D x =
      ((show DualNumber D from ev a (eA m₁ v x)) * (show DualNumber D from ev β.1 (m₂.functor.map i))).snd -
        algebraMap R D (tanVal v β) * (show D from ev a (uA m₁ x)) := by
  have h : ∃ i : trivAt (ptV v x) ⟶ thickAt B x, ∀ r, i.φ r = r := ⟨i, hi⟩
  unfold kFn
  rw [dif_pos h, show h.choose = i from Thick.hom_ext fun r ↦ (h.choose_spec r).trans (hi r).symm]

end GlobalTheory.PtExt.CupA

open GlobalTheory.PtExt.CupA in
theorem GlobalTheory.PtExt.cohom_contr_cupA : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (v : epsR R ⟶ B), IsTangent v → ∀ (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Form (B.hom ≫ 𝟙 _)) (κ : Fn1 A), IsContr (cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle β.1)).1 v κ → Cohom (whole A) κ (fv ((-tanVal v β) • a)) := by
  intro R _ A B _ _ m₁ m₂ v hv a β κ hκ
  refine ⟨kFn m₁ m₂ v a β, ?_⟩
  intro D _ _ D' _ _ φ x _
  obtain ⟨s, i, s', i', a', b, τ, hs, hi, hs', hi', ha, hb, hτ⟩ := (GlobalTheory.T.exists_tangentVector_contraction_twoCochain_product R A B v hv).1 D D' φ x
  have hK := hκ D D' φ x s i s' i' a' b τ hs hi hs' hi' ha hb hτ
  change κ D D' φ x = TrivSqZeroExt.snd (R := D')
    ((show DualNumber D' from τ.φ (ev a (m₁.functor.map s))) * (show DualNumber D' from ev β.1 (m₂.functor.map τ)) -
      (show DualNumber D' from s'.φ (ev a (m₁.functor.map a'))) * (show DualNumber D' from ev β.1 (m₂.functor.map s')) -
      (show DualNumber D' from τ.φ (ev a (m₁.functor.map i))) * (show DualNumber D' from ev β.1 (m₂.functor.map τ)) +
      (show DualNumber D' from i'.φ (ev a (m₁.functor.map b))) * (show DualNumber D' from ev β.1 (m₂.functor.map i'))) at hK
  have fAs : (show DualNumber D from ev a (m₁.functor.map s)) = (show DualNumber D from ev a (eA m₁ v x)) + (show DualNumber D from ev a (m₁.functor.map i)) := by
    rw [show m₁.functor.map s = eA m₁ v x ≫ m₁.functor.map i from Thick.hom_ext fun r ↦ by
      change s.φ r = i.φ (TrivSqZeroExt.inl r)
      exact (hs r).trans (hi _).symm, ev_comp]
    change i.φ _ + _ = _
    erw [hi]
  have fAb := ev_sq a (m₁.functor.map a') (eA m₁ v (spOver φ ≫ x)) (eA m₁ v x) (m₁.functor.map b) (fun r ↦ by
    change TrivSqZeroExt.inl (a'.φ r) = b.φ (TrivSqZeroExt.inl r)
    exact (congrArg TrivSqZeroExt.inl (ha r)).trans ((hb _).trans (epsHom_inl' φ r)).symm)
  have fAa := ev_sq a (trivMap φ x) (uA m₁ (spOver φ ≫ x)) (uA m₁ x) (m₁.functor.map a') (fun r ↦ by
    change φ r = a'.φ r
    exact (ha r).symm)
  have fBτ := Form.ev_sq β (m₂.functor.map b) (m₂.functor.map i') (m₂.functor.map i) (m₂.functor.map τ) rfl rfl
    (fun r ↦ by
      change i'.φ (b.φ r) = τ.φ (i.φ r)
      exact (hi' _).trans ((hb r).trans (((congrArg τ.φ (hi r)).trans (hτ r)).symm)))
  have fBs := bval m₂ v (spOver φ ≫ x) hv β s' i' hs' hi'
  have e1 := kFn_eq m₁ m₂ v a β x i hi
  have e2 := kFn_eq m₁ m₂ v a β (spOver φ ≫ x) i' hi'
  change (Fn1.add κ (fv ((-tanVal v β) • a)).neg) D D' φ x = _
  unfold Fn1.add Fn1.neg
  rw [hK, e1, e2]
  exact alg φ (tanVal v β) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fv a D D' φ x) _ _ _ _ (hτ _) (hs' _) (hτ _) (hi' _).symm
    rfl (hb _) (hτ _) (ha _) rfl fAs fAb fAa fBτ fBs
