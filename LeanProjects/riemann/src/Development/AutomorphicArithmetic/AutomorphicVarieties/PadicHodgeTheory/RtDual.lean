import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtFinFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtPoints
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualCr
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

namespace UpperTheory.V.Loc.RootDualTransport

open TrivSqZeroExt Matrix

variable {κ : Type} [CommRing κ] {m : ℕ}

private def fr (κ : Type) [CommRing κ] : DualNumber κ →+* κ := (TrivSqZeroExt.fstHom κ κ κ : DualNumber κ →+* κ)

private theorem sn_mul (X Y : Matrix (Fin m) (Fin m) (DualNumber κ)) :
    (X * Y).map snd = X.map snd * Y.map (fr κ) + X.map (fr κ) * Y.map snd := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, snd_sum, DualNumber.snd_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact add_comm _ _

private theorem sn_J : (Jmat (DualNumber κ) m).map snd = 0 := by
  ext i j
  simp only [Jmat, Matrix.map_apply]
  split_ifs <;> simp

private theorem sn_one : (1 : Matrix (Fin m) (Fin m) (DualNumber κ)).map snd = 0 := by
  ext i j
  simp only [Matrix.one_apply, Matrix.map_apply]
  split_ifs <;> simp

private theorem fs_inv_mul (a : GL (Fin m) (DualNumber κ)) :
    ((a⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ) *
      (a : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ) = 1 := by
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem fs_mul_inv (a : GL (Fin m) (DualNumber κ)) :
    (a : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ) *
      ((a⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ) = 1 := by
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem sn_inv (a : GL (Fin m) (DualNumber κ)) :
    ((a⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) (DualNumber κ)).map snd =
      -(((a⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ) *
        ((a : Matrix (Fin m) (Fin m) (DualNumber κ)).map snd *
          ((a⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ))) := by
  have h := sn_mul (a : Matrix (Fin m) (Fin m) (DualNumber κ)) ((a⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) _)
  rw [Units.mul_inv, sn_one] at h
  rw [eq_neg_of_add_eq_zero_left h.symm, Matrix.mul_neg, neg_neg, ← Matrix.mul_assoc, fs_inv_mul, Matrix.one_mul]

private def tc (x : GG m (DualNumber κ)) : Matrix (Fin m) (Fin m) κ :=
  x.mat.map snd * ((x.left⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ)

private theorem tc_mul (x y : GG m (DualNumber κ)) : tc (x * y) = tc x + (GG.map (fr κ) x).adFun (tc y) := by
  have h : ((-1 : ℤˣ) = 1) = False := by decide
  have hJ : ∀ Y : Matrix (Fin m) (Fin m) κ, Jmat κ m * (Jmat κ m * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
  obtain ⟨a, s⟩ := x
  obtain ⟨b, t⟩ := y
  have e : (((GG.map (fr κ) (⟨a, s⟩ : GG m (DualNumber κ))).left⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) κ) =
      ((a⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ) := rfl
  have h1 : ∀ Y : Matrix (Fin m) (Fin m) κ, (b : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ) *
      (((b⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ) * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, fs_mul_inv, Matrix.one_mul]
  have h2 : ∀ Y : Matrix (Fin m) (Fin m) κ, (((b⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ))ᵀ *
      (((b : Matrix (Fin m) (Fin m) (DualNumber κ)).map (fr κ))ᵀ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, fs_mul_inv, Matrix.transpose_one, Matrix.one_mul]
  unfold GG.adFun
  rw [e, GG.map_mat, GG.map_right]
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp only [tc, GG.mat, SemidirectProduct.mul_left, sgnAct_one, if_true, _root_.mul_inv_rev, Units.val_mul,
      sn_mul, Matrix.map_mul, Matrix.add_mul, Matrix.mul_assoc, h1]
  · simp only [tc, GG.mat, SemidirectProduct.mul_left, sgnAct_neg_one, h, if_false, _root_.mul_inv_rev,
      Units.val_mul, theta_val, theta_inv_val, thetaLie, sn_mul, sn_J, Matrix.map_mul, Jmat_map,
      Matrix.transpose_map, sn_inv, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.zero_mul,
      Matrix.mul_zero, zero_add, add_zero, Matrix.transpose_neg, Matrix.transpose_mul, Matrix.neg_mul,
      Matrix.mul_neg, hJ, h2]

private theorem tc_mul_mat (x : GG m (DualNumber κ)) : tc x * (GG.map (fr κ) x).mat = x.mat.map snd := by
  rw [tc, GG.map_mat, Matrix.mul_assoc, GG.mat, fs_inv_mul, Matrix.mul_one]

end UpperTheory.V.Loc.RootDualTransport

namespace UpperTheory.V.Loc.RootDualTransport

open TrivSqZeroExt Matrix TensorProduct

private theorem qcont_lin {l : ℕ} [Fact l.Prime] {X V W : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [TopologicalSpace W] [ContinuousAdd W] [ContinuousSMul ℚ_[l] W]
    (φ : V →ₗ[ℚ_[l]] W) (f : X → V) (hf : QCont l f) : Continuous fun x => φ (f x) := by
  letI : TopologicalSpace V := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap φ).comp hf

private theorem cont_inv {X E : Type} [TopologicalSpace X] [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    [ContinuousInv₀ E] {m : ℕ} (a : X → GL (Fin m) E) (ha : Continuous fun x => (a x : Matrix (Fin m) (Fin m) E)) :
    Continuous fun x => (((a x)⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) := by
  simp only [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  refine Continuous.smul (ha.matrix_det.inv₀ fun x => ?_) ha.matrix_adjugate
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (a x).isUnit).ne_zero

private theorem adFun_map {A B : Type} [CommRing A] [CommRing B] {m : ℕ} (f : A →+* B) (x : GG m A)
    (X : Matrix (Fin m) (Fin m) A) : (x.adFun X).map f = (GG.map f x).adFun (X.map f) := by
  have e : (((GG.map f x).left⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) B) =
      ((x.left⁻¹ : GL _ _) : Matrix (Fin m) (Fin m) A).map f := rfl
  unfold GG.adFun
  rw [e, GG.map_mat, GG.map_right, Matrix.map_mul, Matrix.map_mul]
  split_ifs
  · rfl
  · simp only [thetaLie, Matrix.map_neg _ (map_neg f), Matrix.map_mul, Jmat_map, Matrix.transpose_map]

private theorem map_mem_finiteCocycles_adRep_of_continuous {l : ℕ} [Fact l.Prime] {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ_[l] A]
    [Algebra ℚ_[l] B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    {m : ℕ} (ι : A →ₐ[ℚ_[l]] B) (hι : Continuous ι) (r : GQ l →* GG m A) (c : GQ l → Matrix (Fin m) (Fin m) A)
    (hc : c ∈ finiteCocycles (MonoidHom.id _) (adRep r)) :
    (fun g => (c g).map ι) ∈ finiteCocycles (MonoidHom.id _) (adRep ((GG.map (ι : A →+* B)).comp r)) := by
  obtain ⟨⟨hc, hcc⟩, x, hx⟩ := hc
  let f : Matrix (Fin m) (Fin m) A →ₗ[ℚ_[l]] Matrix (Fin m) (Fin m) B := ι.toLinearMap.mapMatrix
  have hf : ∀ g X, f (adRep r g X) = adRep ((GG.map (ι : A →+* B)).comp r) g (f X) := fun g X =>
    adFun_map (ι : A →+* B) (r g) X
  refine ⟨⟨hc.matrix_map hι, fun g h => ?_⟩, LinearMap.rTensor (Bcr l) f x, fun g => ?_⟩
  · show f (c (g * h)) = f (c g) + adRep _ g (f (c h))
    rw [hcc g h, map_add, hf]
  · have key : ∀ y : Matrix (Fin m) (Fin m) A ⊗[ℚ_[l]] Bcr l,
        LinearMap.rTensor (Bcr l) f (actC (MonoidHom.id _) (adRep r) g y) =
        actC (MonoidHom.id _) (adRep ((GG.map (ι : A →+* B)).comp r)) g (LinearMap.rTensor (Bcr l) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [actC, hf]
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
    rfl

private theorem fin_case (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (E : Type) [Field E] [Algebra ℚ_[l] E]
    [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] [ContinuousInv₀ E]
    (F : U.R →ₐ[O] DualNumber E) (hF : D.It U ≤ RingHom.ker F) :
    tanCoc F U.r.hom ∈ finiteCocycles (MonoidHom.id _) (adRep (push (dualFst F) U.r.hom)) := by
  haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
  obtain ⟨hc, -, hcr⟩ := rtPoints hP D U (DualNumber E) (push F U.r.hom) ⟨F, rfl, hF⟩
  have h1 : Continuous fun g => (push (dualFst F) U.r.hom g).mat :=
    continuous_matrix fun a b => qcont_lin (LinearMap.fst ℚ_[l] E E) _ (hc a b)
  have h2 : Continuous fun g => (U.r.hom g).mat.map fun x => (F x).snd :=
    continuous_matrix fun a b => qcont_lin (LinearMap.snd ℚ_[l] E E) _ (hc a b)
  have h3 := cont_inv (fun g => (push (dualFst F) U.r.hom g).left) h1
  have hz : tanCoc F U.r.hom ∈ Z1 (adRep (push (dualFst F) U.r.hom)) := by
    refine ⟨h2.matrix_mul h3, fun g h => ?_⟩
    have := tc_mul (push F U.r.hom g) (push F U.r.hom h)
    rw [← map_mul] at this
    exact this
  refine ((dualCr D E (push (dualFst F) U.r.hom) (fun g => U.r.hasMult g) h1 _ hz (push F U.r.hom)
    fun g => ⟨rfl, fun a b => ?_⟩).1 hcr).2
  refine TrivSqZeroExt.ext rfl ?_
  exact (congrFun (congrFun (tc_mul_mat (push F U.r.hom g)) a) b).symm

end UpperTheory.V.Loc.RootDualTransport

open UpperTheory.V.Loc.RootDualTransport in
theorem UpperTheory.V.Loc.rtDual :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] (F : U.R →ₐ[O] DualNumber (PadicAlgCl l)), D.It U ≤ RingHom.ker F → IsLocPt (dualFst F) → tanCoc F U.r.hom ∈ finiteCocycles (MonoidHom.id _) (adRep (push (dualFst F) U.r.hom)) := by
  intro hP l _ O _ _ _ _ _ _ _ D U _ _ F hF hloc
  obtain ⟨⟨K, hfin⟩, hE⟩ := ptFin U.R F hloc
  haveI : FiniteDimensional ℚ_[l] ↥K := hfin
  haveI : IsModuleTopology ℚ_[l] ↥K := isModuleTopologyOfFiniteDimensional
  have hO : ∀ x : O, algebraMap O (PadicAlgCl l) x ∈ K := fun x => by
    have := (hE (algebraMap O U.R x)).1
    rwa [F.commutes] at this
  letI : Algebra O ↥K := ((algebraMap O (PadicAlgCl l)).codRestrict K hO).toAlgebra
  haveI : IsScalarTower ℤ_[l] O ↥K := IsScalarTower.of_algebraMap_eq fun z =>
    Subtype.ext (IsScalarTower.algebraMap_apply ℤ_[l] O (PadicAlgCl l) z)
  let F' : U.R →ₐ[O] DualNumber ↥K :=
    { toFun := fun a => ⟨⟨(F a).fst, (hE a).1⟩, ⟨(F a).snd, (hE a).2⟩⟩
      map_one' := TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_one F)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_one F)))
      map_zero' := TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_zero F)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_zero F)))
      map_add' := fun a b => TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_add F a b)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_add F a b)))
      map_mul' := fun a b => TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_mul F a b)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_mul F a b)))
      commutes' := fun c => TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (F.commutes c)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (F.commutes c))) }
  have hF' : D.It U ≤ RingHom.ker F' := fun a ha => by
    have h : F a = 0 := hF ha
    exact TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst h)) (Subtype.ext (congrArg TrivSqZeroExt.snd h))
  have h := map_mem_finiteCocycles_adRep_of_continuous K.val continuous_subtype_val _ _ (fin_case hP D U ↥K F' hF')
  have e : (fun g => (tanCoc F' U.r.hom g).map K.val) = tanCoc F U.r.hom := by
    funext g
    exact Matrix.map_mul (f := (K.val : ↥K →+* PadicAlgCl l))
  rw [e] at h
  exact h
