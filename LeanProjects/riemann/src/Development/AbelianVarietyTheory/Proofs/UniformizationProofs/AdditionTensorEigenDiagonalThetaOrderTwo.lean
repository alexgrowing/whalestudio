import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSumTmulLinearIndependent
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.AddEig

theorem gen_ratio {F : Type} [CommRing F] {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (q : Y ⟶ Spec (CommRingCat.of F)) (hq : Function.Surjective q.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : F, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ (scal q c) * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hq (res le (t.s PEmpty.elim)).val
  obtain ⟨c, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective a
  refine ⟨c, fun Z r z J hJ => ?_⟩
  have key : (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ (scal q c) := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      (congrArg (gs r z ⊤) ha.symm))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

theorem surj_fst_sq {S : Scheme.{0}} (hG : GlobalFnsSt) {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    (T : Over S) : Function.Surjective (fst T (A ⊗ A)).left.appTop.hom := by
  let m : T ⊗ (A ⊗ A) ⟶ A ⊗ (A ⊗ T) := lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _) (fst _ _))
  let n : A ⊗ (A ⊗ T) ⟶ T ⊗ (A ⊗ A) := lift (snd _ _ ≫ snd _ _) (lift (fst _ _) (snd _ _ ≫ fst _ _))
  have e₀ : m ≫ snd _ _ ≫ snd _ _ = fst T (A ⊗ A) := by simp [m]
  have e₁ : m ≫ n = 𝟙 _ := by ext <;> simp [m, n]
  rw [← e₀, Over.comp_left, Over.comp_left]
  refine surj_comp (fun a => ⟨n.left.appTop.hom a, ?_⟩) (surj_comp (surj_snd hG hA _) (surj_snd hG hA T))
  have e : m.left ≫ n.left = 𝟙 _ := by rw [← Over.comp_left, e₁]; rfl
  have := congrArg (fun q => (Scheme.Hom.appTop q).hom a) e
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_appTop,
    CommRingCat.hom_id, RingHom.id_apply] using this

theorem kappa_translate (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) {F : Type} [CommRing F]
    (p : Spec (CommRingCat.of F) ⟶ S)
    (κ : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(snd (Over.mk p) (P.A ⊗ P.A) ≫ fst P.A P.A).left, (snd (Over.mk p) (P.A ⊗ P.A) ≫ snd P.A P.A).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A)).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹)).left] ![2, 2, -1, -1])) (hκ : κ.IsGen)
    (c : Over.mk p ⟶ P.A) (hc : c ^ 2 = 1)
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk p) P.A).left, (translPt P.A c).left] ![2, -2]))
    (hα : α.IsGen) :
    ∃ r : F, ∀ (T : Over S) (ρ : T ⟶ Over.mk p) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      (val α (lift ρ x).left z J * val α (lift ρ y).left z J *
        val κ (lift ρ (lift ((ρ ≫ c) * x) ((ρ ≫ c) * y))).left z J).val =
      gs (𝟙 _) z ⊤ (scal (R := F) ρ.left r) * (val κ (lift ρ (lift x y)).left z J).val := by
  have := P.isAb.comm
  let a : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := snd _ _ ≫ fst _ _
  let b : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := snd _ _ ≫ snd _ _
  let d : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := fst _ _ ≫ c
  have hd : d * d = 1 := by
    rw [← MonObj.comp_mul, ← pow_two, hc, MonObj.comp_one]
  have tp : translPt P.A c = (fst _ P.A ≫ c) * snd _ P.A := rfl
  obtain ⟨r, hr⟩ := gen_ratio (F := F) P.isLB (fun U _ h => by
      have e₁ : lift (fst _ _) a ≫ translPt P.A c = d * a := by
        rw [tp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₂ : lift (fst _ _) b ≫ translPt P.A c = d * b := by
        rw [tp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₃ : lift (fst _ _) (lift (d * a) (d * b)) ≫ snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A) =
          snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A) := by
        rw [lift_snd_assoc, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_mul, _root_.mul_mul_mul_comm, hd,
          _root_.one_mul]
      have e₄ : lift (fst _ _) (lift (d * a) (d * b)) ≫ snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹) =
          snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹) := by
        rw [lift_snd_assoc, MonObj.comp_mul, lift_fst, GrpObj.comp_inv, lift_snd, MonObj.comp_mul, GrpObj.comp_inv,
          _root_.mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ← Over.comp_left, e₁, e₂, e₃, e₄, lift_snd,
        lift_snd_assoc, lift_fst]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      abel)
    (fst (Over.mk p) (P.A ⊗ P.A)).left (surj_fst_sq hG P.isAb _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hα (lift (fst _ _) a).left) (DVR.pullGen_isGen _ _ _ _ hα (lift (fst _ _) b).left))
      (DVR.pullGen_isGen _ _ _ _ hκ (lift (fst _ _) (lift (d * a) (d * b))).left)) hκ
  refine ⟨r, fun T ρ x y z J hJ => ?_⟩
  have := hr _ (lift ρ (lift x y)).left z J hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, ThetaLin.gs_scal_comp] at this
  simp only [← Over.comp_left] at this
  have f₁ : lift ρ (lift x y) ≫ lift (fst _ _) a = lift ρ x := by simp [a]
  have f₂ : lift ρ (lift x y) ≫ lift (fst _ _) b = lift ρ y := by simp [b]
  have f₃ : lift ρ (lift x y) ≫ lift (fst _ _) (lift (d * a) (d * b)) =
      lift ρ (lift ((ρ ≫ c) * x) ((ρ ≫ c) * y)) := by simp [a, b, d, MonObj.comp_mul]
  rw [f₁, f₂, f₃, lift_fst] at this
  exact this

theorem tensor_eq_smul {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) [QuasiCompact q] [IsSeparated q] {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {n : ℕ} (u u' t t' : Fin n → SecMod q (LB.LinComb L φ ε)) (r : F)
    (H : ∀ (Z : Scheme.{0}) (r₁ r₂ : Z ⟶ Y), r₁ ≫ q = r₂ ≫ q → ∀ (z : Z) (J), Good L z J →
      ∑ i, sval (u i).sec r₁ z J * sval (u' i).sec r₂ z J =
        gs (𝟙 _) z ⊤ (scal (r₁ ≫ q) r) * ∑ i, sval (t i).sec r₁ z J * sval (t' i).sec r₂ z J) :
    ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  have key := (GlobalTheory.tensor_sections_eq_zero_iff F _ L hL _ _ q q K K φ ε φ ε (n + n) (Fin.append u (fun i => (-r) • t i))
    (Fin.append u' t')).2 (by
      intro Z r₁ r₂ h z J hJ
      have ng : gs r₁ z ⊤ (scal q (-r)) = - gs (𝟙 _) z ⊤ (scal (r₁ ≫ q) r) := by
        rw [ThetaLin.gs_scal_comp, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, scal, scal, map_neg, map_neg, map_neg,
          map_neg]
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, SecMod.sval_smul hJ, ng, _root_.mul_assoc, neg_mul]
      rw [H Z r₁ r₂ h z J hJ, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel])
  rw [Fin.sum_univ_add] at key
  simp only [Fin.append_left, Fin.append_right, ← TensorProduct.smul_tmul', neg_smul, TensorProduct.neg_tmul,
    Finset.sum_neg_distrib] at key
  rw [Finset.smul_sum]
  exact add_neg_eq_zero.1 key

theorem main : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' u u' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → ∀ θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p), θ.pt ^ 2 = 1 → (∀ i, IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t i).sec (u i).sec ∧ IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t' i).sec (u' i).sec) → ∃ r : F, ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  intro hG S P F _ p th n t t' u u' ⟨κ, hκ, hA⟩ θ hθ hact
  have := P.isAb.comm
  obtain ⟨r, hr⟩ := kappa_translate hG P p κ hκ θ.pt hθ θ.φ θ.isGen
  refine ⟨r, ?_⟩
  have pt : ∀ (T : Over S) (ρ : T ⟶ Over.mk p) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (u i).sec (lift ρ x).left z J *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (u' i).sec (lift ρ y).left z J =
      gs (𝟙 _) z ⊤ (scal (R := F) ρ.left r) *
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t i).sec (lift ρ x).left z J *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t' i).sec (lift ρ y).left z J := by
    intro T ρ x y z J hJ
    have hd : (ρ ≫ θ.pt) * (ρ ≫ θ.pt) = 1 := by
      rw [← MonObj.comp_mul, ← pow_two, hθ, MonObj.comp_one]
    have a₁ := hA T ρ x y z J hJ
    have a₂ := hA T ρ ((ρ ≫ θ.pt) * x) ((ρ ≫ θ.pt) * y) z J hJ
    rw [_root_.mul_mul_mul_comm (ρ ≫ θ.pt), hd, _root_.one_mul, _root_.mul_inv, _root_.mul_mul_mul_comm (ρ ≫ θ.pt),
      mul_inv_cancel, _root_.one_mul] at a₂
    have b := hr T ρ x y z J hJ
    have act : ∀ (v w : EA P p 2) (x : T ⟶ P.A), IsActOf P.A P.L ((2 : ℕ) : ℤ) θ v.sec w.sec →
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) w.sec (lift ρ x).left z J =
        (val (L := P.L) (K := Fin 2) (φ := ![(snd (Over.mk p) P.A).left, (translPt P.A θ.pt).left]) (ε := ![2, -2])
          θ.φ (lift ρ x).left z J).val *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) v.sec (lift ρ ((ρ ≫ θ.pt) * x)).left z J := fun v w x h => by
      refine (ThetaLin.sval_of_isTwistPull P.A h (lift ρ x).left z hJ).trans ?_
      rw [← Over.comp_left, ThetaLin.lift_translT]
    rw [a₁, ← _root_.mul_assoc, ← b, Units.val_mul, _root_.mul_assoc, ← a₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act _ _ x (hact i).1, act _ _ y (hact i).2, Units.val_mul]
    exact _root_.mul_mul_mul_comm _ _ _ _
  have : IsProper (fst (Over.mk p) P.A).left := by
    have := P.isAb.proper
    show IsProper (pullback.fst _ _)
    infer_instance
  refine tensor_eq_smul P.isLB (fst (Over.mk p) P.A).left (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left)
    (ε := fun _ => ((2 : ℕ) : ℤ)) u u' t t' r fun Z r₁ r₂ h z J hJ => ?_
  let T : Over S := Over.mk (r₁ ≫ (Over.mk p ⊗ P.A).hom)
  let R₁ : T ⟶ Over.mk p ⊗ P.A := Over.homMk r₁ rfl
  let R₂ : T ⟶ Over.mk p ⊗ P.A := Over.homMk r₂ (by
    show r₂ ≫ (Over.mk p ⊗ P.A).hom = r₁ ≫ (Over.mk p ⊗ P.A).hom
    rw [← Over.w (fst (Over.mk p) P.A), ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ p) h.symm)
  have hR : R₂ ≫ fst _ _ = R₁ ≫ fst _ _ := Over.OverMorphism.ext h.symm
  have q := pt T (R₁ ≫ fst _ _) (R₁ ≫ snd _ _) (R₂ ≫ snd _ _) z J hJ
  rw [lift_comp_fst_snd, show lift (R₁ ≫ fst _ _) (R₂ ≫ snd _ _) = R₂ by rw [← hR, lift_comp_fst_snd]] at q
  exact q

end GlobalTheory.AddEig

end
