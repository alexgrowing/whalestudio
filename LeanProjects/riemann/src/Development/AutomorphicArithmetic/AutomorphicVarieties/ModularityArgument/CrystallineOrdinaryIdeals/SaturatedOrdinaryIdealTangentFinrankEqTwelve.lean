import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatedOrdinaryIdealCutsOutCrystallineLocusStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnramifiedLiftDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualCr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsTypeAndIsLocallyCrystallineRz
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankLocalCocyclesAdjointUnitaryThreeEqTwelve
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefCoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.EntInMulRight
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.TangentDual

section Dual

variable {G E : Type} [Group G] [CommRing E]

private def mR (X : Matrix (Fin 3) (Fin 3) E) : Matrix (Fin 3) (Fin 3) (DualNumber E) :=
  X.map fun a => TrivSqZeroExt.inr a

private theorem mul_mR (A X : Matrix (Fin 3) (Fin 3) E) :
    A.map (algebraMap E (DualNumber E)) * mR X = mR (A * X) := by
  ext a b <;> simp [mR, Matrix.mul_apply, Fin.sum_univ_three, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]

private theorem mR_mul (A X : Matrix (Fin 3) (Fin 3) E) :
    mR X * A.map (algebraMap E (DualNumber E)) = mR (X * A) := by
  ext a b <;> simp [mR, Matrix.mul_apply, Fin.sum_univ_three, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]

private theorem mR_add (X Y : Matrix (Fin 3) (Fin 3) E) : mR (X + Y) = mR X + mR Y := by
  ext a b <;> simp [mR]

private theorem mR_inj {X Y : Matrix (Fin 3) (Fin 3) E} (h : mR X = mR Y) : X = Y := by
  ext a b
  exact congrArg TrivSqZeroExt.snd (congrFun (congrFun h a) b)

private theorem theta_mR (X : Matrix (Fin 3) (Fin 3) E) : thetaLie (mR X) = mR (thetaLie X) := by
  have h : (mR X).transpose = mR X.transpose := rfl
  unfold thetaLie
  rw [h, ← Jmat_map (algebraMap E (DualNumber E)), mul_mR, mR_mul]
  ext a b <;> simp [mR]

private theorem ad_mR (r : G →* GG 3 E) (g : G) (X : Matrix (Fin 3) (Fin 3) E) :
    adRep ((GG.map (algebraMap E (DualNumber E))).comp r) g (mR X) = mR (adRep r g X) := by
  show (GG.map (algebraMap E (DualNumber E)) (r g)).adFun (mR X) = mR ((r g).adFun X)
  unfold GG.adFun
  rw [← mR_mul, ← mul_mR, GG.map_right, GG.map_mat]
  congr 2
  split_ifs
  · rfl
  · exact theta_mR X

private theorem sq_ker : RingHom.ker (TrivSqZeroExt.fstHom E E E : DualNumber E →+* E) *
    RingHom.ker (TrivSqZeroExt.fstHom E E E : DualNumber E →+* E) = ⊥ := by
  rw [eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  have ha' : a.fst = 0 := ha
  have hb' : b.fst = 0 := hb
  rw [Ideal.mem_bot]
  ext <;> simp [ha', hb']

private theorem dualDef_of (r : G →* GG 3 E) (γ : G → Matrix (Fin 3) (Fin 3) E) (r' : G →* GG 3 (DualNumber E))
    (h : IsDeform ((GG.map (algebraMap E (DualNumber E))).comp r) (fun g => mR (γ g)) r') : DualDef r γ r' := by
  intro g
  refine ⟨(h g).1, fun a b => ?_⟩
  rw [(h g).2, MonoidHom.comp_apply, GG.map_mat, Matrix.add_mul, Matrix.one_mul, mR_mul]
  ext <;> simp [mR, TrivSqZeroExt.algebraMap_eq_inl]

private theorem dualEx (r : G →* GG 3 E) (γ : G → Matrix (Fin 3) (Fin 3) E) (hγ : IsCoc r γ) :
    ∃ r', DualDef r γ r' := by
  obtain ⟨r', h⟩ := exists_isDeform (RingHom.ker (TrivSqZeroExt.fstHom E E E : DualNumber E →+* E))
    ((GG.map (algebraMap E (DualNumber E))).comp r) (fun g => mR (γ g)) sq_ker (fun g a b => rfl)
    (fun g h => by simp only [hγ g h, mR_add, ad_mR])
  exact ⟨r', dualDef_of r γ r' h⟩

private theorem dualCoc (r : G →* GG 3 E) (r' : G →* GG 3 (DualNumber E))
    (h : (GG.map (TrivSqZeroExt.fstHom E E E : DualNumber E →+* E)).comp r' = r) :
    ∃ γ, IsCoc r γ ∧ DualDef r γ r' := by
  obtain ⟨γ, h1, h2, h3⟩ := exists_isCoc (RingHom.ker (TrivSqZeroExt.fstHom E E E : DualNumber E →+* E))
    ((GG.map (algebraMap E (DualNumber E))).comp r) r' sq_ker (by
      subst h
      refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
      ext a b
      refine Ideal.Quotient.eq.2 ?_
      show TrivSqZeroExt.fst ((r' g).mat a b - algebraMap E (DualNumber E) ((r' g).mat a b).fst) = 0
      simp [TrivSqZeroExt.algebraMap_eq_inl])
  have e : γ = fun g => mR ((γ g).map TrivSqZeroExt.snd) := by
    funext g
    ext a b
    · exact h1 g a b
    · rfl
  refine ⟨fun g => (γ g).map TrivSqZeroExt.snd, fun g h => mR_inj ?_, dualDef_of _ _ _ (e ▸ h3)⟩
  rw [mR_add, ← ad_mR, ← congrFun e, ← congrFun e, ← congrFun e]
  exact h2 g h

end Dual

section Main

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ)
  (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
  [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
  (x : U.R →ₐ[O] O) (hx : IsBase D.η D.Ψ U.r.hom x)
  (hPC : GlobalTheory.OrdLoc.PtsCr D U (GlobalTheory.OrdLoc.IY D U)) (hCP : GlobalTheory.OrdLoc.CrPts D U (GlobalTheory.OrdLoc.IY D U))

include hx in
private theorem push_base : push ((Algebra.ofId O E).comp x) U.r.hom = D.rz E := by
  unfold Dat3.rz
  rw [← (show push x U.r.hom = r0 D.η D.Ψ from hx)]
  rfl

section Pro

variable {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
  [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B]

private theorem push_cont (f : U.R →ₐ[O] B) (a b : Fin 3) : QCont l fun g => (push f U.r.hom g).mat a b :=
  (ptCont U.R B f).1 _ _ (U.r.cont a b)

variable [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E)

include hx in
private theorem push_red (f : U.R →ₐ[O] B) (hf : ∀ a, π (f a) = algebraMap O E (x a)) :
    (GG.map (π : B →+* E)).comp (push f U.r.hom) = D.rz E := by
  rw [← push_base D U E x hx]
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
  ext a b
  exact hf _

include hx hPC in
private theorem inDcr_push (f : U.R →ₐ[O] B) (hf : ∀ a, π (f a) = algebraMap O E (x a))
    (hI : GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f) : D.InDcr (π : B →+* E) (push f U.r.hom) where
  mult := U.r.hasMult
  red := push_red D U E x hx π f hf
  cont := push_cont D U f
  cr := hPC B f hI

variable (hπ : ∀ a, π a = 0 → IsNilpotent a)

include hx hπ in
private theorem push_inj (f f' : U.R →ₐ[O] B) (hf : ∀ a, π (f a) = algebraMap O E (x a))
    (h : push f' U.r.hom = push f U.r.hom) : f' = f :=
  (unramified_lift_deformation D U E B π hπ ((Algebra.ofId O E).comp x) (push f U.r.hom) U.r.hasMult
    ((push_red D U E x hx π f hf).trans (push_base D U E x hx).symm) (push_cont D U f)).unique h rfl

include hx hCP hπ in
private theorem exists_push (r : GQ l →* GG 3 B) (hr : D.InDcr (π : B →+* E) r) :
    ∃ f : U.R →ₐ[O] B, push f U.r.hom = r ∧ GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f ∧ ∀ a, π (f a) = algebraMap O E (x a) := by
  obtain ⟨f, hf, -⟩ := unramified_lift_deformation D U E B π hπ ((Algebra.ofId O E).comp x) r hr.mult
    (hr.red.trans (push_base D U E x hx).symm) hr.cont
  refine ⟨f, hf, hCP E B π hπ f (hf ▸ hr), fun a => ?_⟩
  have h := push_inj D U E x hx (AlgHom.id E E) (fun a h => by rw [show a = 0 from h]; exact IsNilpotent.zero)
    ((Algebra.ofId O E).comp x) ((π.restrictScalars O).comp f) (fun _ => rfl) (by
      rw [push_base D U E x hx, ← hr.red, ← hf]
      rfl)
  exact DFunLike.congr_fun h a

end Pro

include hx hCP in
private theorem le_ker [IsFractionRing O E] : GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker x := fun a ha => by
  have hd : D.InDcr ((AlgHom.id E E : E →ₐ[E] E) : E →+* E) (push ((Algebra.ofId O E).comp x) U.r.hom) :=
    { mult := U.r.hasMult
      red := push_red D U E x hx (AlgHom.id E E) ((Algebra.ofId O E).comp x) (fun _ => rfl)
      cont := push_cont D U _
      cr := by rw [push_base D U E x hx]; exact (isType_and_isLocallyCrystalline_rz D E).2 }
  have h := hCP E E (AlgHom.id E E) (fun a h => by rw [show a = 0 from h]; exact IsNilpotent.zero)
    ((Algebra.ofId O E).comp x) hd ha
  exact IsFractionRing.injective O E (h.trans (map_zero _).symm)

private noncomputable def dualPt {O R E : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing E] [Algebra O E]
    (x : R →ₐ[O] O) (δ : R →ₗ[O] E)
    (h : ∀ a b, δ (a * b) = algebraMap O E (x a) * δ b + algebraMap O E (x b) * δ a) : R →ₐ[O] DualNumber E :=
  AlgHom.ofLinearMap
    (show R →ₗ[O] DualNumber E from ((Algebra.linearMap O E).comp x.toLinearMap).prod δ)
    (TrivSqZeroExt.ext (show algebraMap O E (x 1) = 1 by simp) (show δ 1 = 0 by simpa using h 1 1))
    (fun a b => TrivSqZeroExt.ext
      (show algebraMap O E (x (a * b)) = algebraMap O E (x a) * algebraMap O E (x b) by simp)
      (show δ (a * b) = algebraMap O E (x a) * δ b + δ a * algebraMap O E (x b) by rw [h a b, mul_comm (δ a)]))

private noncomputable def cochain : (U.R →ₗ[O] E) →ₗ[E] (GQ l → Matrix (Fin 3) (Fin 3) E) where
  toFun δ g := (U.r.hom g).mat.map δ * (((D.rz E g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)
  map_add' δ δ' := by
    funext g
    rw [Pi.add_apply, ← Matrix.add_mul]
    rfl
  map_smul' c δ := by
    funext g
    rw [Pi.smul_apply, ← Matrix.smul_mul]
    rfl

private theorem cochain_mul (δ : U.R →ₗ[O] E) (g : GQ l) :
    cochain D U E δ g * (D.rz E g).mat = (U.r.hom g).mat.map δ :=
  Units.inv_mul_cancel_right _ _

private theorem cochain_eq (δ : U.R →ₗ[O] E) (γ : GQ l → Matrix (Fin 3) (Fin 3) E)
    (h : ∀ g, γ g * (D.rz E g).mat = (U.r.hom g).mat.map δ) : cochain D U E δ = γ := by
  funext g
  exact (Units.mul_left_inj (D.rz E g).left).1 ((cochain_mul D U E δ g).trans (h g).symm)

private theorem nil_fst (a : DualNumber E) (h : TrivSqZeroExt.fstHom E E E a = 0) : IsNilpotent a :=
  TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst.2 (by rw [show a.fst = 0 from h]; exact IsNilpotent.zero)

private instance : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))

variable [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]

private theorem qcont_iff {X : Type} [TopologicalSpace X] (f : X → E) : QCont l f ↔ Continuous f := by
  unfold QCont
  rw [← eq_moduleTopology ℚ_[l] E]

private theorem qcont_dual {X : Type} [TopologicalSpace X] (f : X → DualNumber E) :
    QCont l f ↔ Continuous (fun g => (f g).fst) ∧ Continuous fun g => (f g).snd := by
  have h : QCont l f ↔ @Continuous X (E × E) _ (moduleTopology ℚ_[l] (E × E)) f := Iff.rfl
  rw [h, ← eq_moduleTopology ℚ_[l] (E × E)]
  exact continuous_prodMk

include hx in
private theorem rz_cont : Continuous fun g => (D.rz E g).mat := by
  rw [← push_base D U E x hx]
  exact continuous_matrix fun a b => (qcont_iff E _).1 (push_cont D U _ a b)

include hx in
private theorem rz_inv_cont :
    Continuous fun g => (((D.rz E g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) := by
  have h : ∀ g, (D.rz E g).left⁻¹ = (D.rz E g⁻¹).left := fun g => by
    show (Matrix.GeneralLinearGroup.map (algebraMap O E) (tor O (D.Ψ g)))⁻¹ =
      Matrix.GeneralLinearGroup.map (algebraMap O E) (tor O (D.Ψ g⁻¹))
    simp only [map_inv]
  simp only [h]
  exact (rz_cont D U E x hx).comp continuous_inv

include hx hPC hCP in
private theorem tangent (T : Submodule E (U.R →ₗ[O] E))
    (hT : ∀ δ, δ ∈ T ↔ (∀ a b, δ (a * b) = algebraMap O E (x a) * δ b + algebraMap O E (x b) * δ a) ∧
      ∀ a ∈ GlobalTheory.OrdLoc.IY D U, δ a = 0) (hle : GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker x) :
    finrank E ↥T = finrank E ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E))) := by
  have hm : HasMult D.η (D.rz E) := fun _ => rfl
  have hinj : Function.Injective ((cochain D U E).domRestrict T) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨δ, hδ⟩ h0
    have h1 : ∀ g, (U.r.hom g).mat.map δ = 0 := fun g => by
      rw [← cochain_mul, show cochain D U E δ = 0 from h0, Pi.zero_apply, Matrix.zero_mul]
    have h2 := push_inj D U E x hx (TrivSqZeroExt.fstHom E E E) (nil_fst E)
      (dualPt x (0 : U.R →ₗ[O] E) (by simp)) (dualPt x δ ((hT δ).1 hδ).1) (fun _ => rfl) (by
        refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
        ext a b
        · rfl
        · exact congrFun (congrFun (h1 g) a) b)
    exact Subtype.ext (LinearMap.ext fun a => congrArg TrivSqZeroExt.snd (DFunLike.congr_fun h2 a))
  rw [← LinearMap.finrank_range_of_inj hinj, LinearMap.range_domRestrict]
  refine congrArg (fun S : Submodule E (GQ l → Matrix (Fin 3) (Fin 3) E) => finrank E ↥S) ?_
  refine le_antisymm ?_ fun γ hγ => ?_
  · rintro _ ⟨δ, hδ, rfl⟩
    obtain ⟨h1, h2⟩ := (hT δ).1 hδ
    have hF := inDcr_push D U E x hx hPC (TrivSqZeroExt.fstHom E E E) (dualPt x δ h1) (fun _ => rfl)
      (fun a ha => TrivSqZeroExt.ext (by
        show algebraMap O E (x a) = 0
        rw [show x a = 0 from hle ha, map_zero]) (h2 a ha))
    obtain ⟨γ, hγ, hd⟩ := dualCoc _ _ hF.red
    have e : cochain D U E δ = γ := cochain_eq D U E δ γ fun g => by
      ext a b
      exact (congrArg TrivSqZeroExt.snd ((hd g).2 a b)).symm
    have hc : Continuous (cochain D U E δ) := continuous_pi_iff.2 <| continuous_pi_iff.1 <|
      (continuous_matrix fun a b => ((qcont_dual E _).1 (hF.cont a b)).2).matrix_mul (rz_inv_cont D U E x hx)
    rw [e] at hc ⊢
    exact ((dualCr D E _ hm (rz_cont D U E x hx) γ ⟨hc, hγ⟩ _ hd).1 hF.cr).2
  · obtain ⟨r', hd⟩ := dualEx (D.rz E) γ hγ.1.2
    have hr' : D.InDcr (TrivSqZeroExt.fstHom E E E : DualNumber E →+* E) r' :=
      { mult := fun g => (hd g).1
        red := by
          refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) (hd g).1
          ext a b
          exact congrArg TrivSqZeroExt.fst ((hd g).2 a b)
        cont := fun a b => by
          rw [qcont_dual]
          simp only [fun g => (hd g).2 a b]
          exact ⟨(rz_cont D U E x hx).matrix_elem a b, (hγ.1.1.matrix_mul (rz_cont D U E x hx)).matrix_elem a b⟩
        cr := (dualCr D E _ hm (rz_cont D U E x hx) γ hγ.1 _ hd).2 ⟨(isType_and_isLocallyCrystalline_rz D E).2, hγ⟩ }
    obtain ⟨F, hF, hFI, hFx⟩ := exists_push D U E x hx hCP (TrivSqZeroExt.fstHom E E E) (nil_fst E) r' hr'
    refine ⟨(TrivSqZeroExt.sndHom E E).restrictScalars O ∘ₗ F.toLinearMap, (hT _).2 ⟨fun a b => ?_, fun a ha => ?_⟩,
      cochain_eq D U E _ γ fun g => ?_⟩
    · show (F (a * b)).snd = _ * (F b).snd + _ * (F a).snd
      rw [← hFx, ← hFx, map_mul]
      simp [mul_comm]
    · show (F a).snd = 0
      rw [show F a = 0 from hFI ha]
      rfl
    · ext a b
      subst hF
      exact (congrArg TrivSqZeroExt.snd ((hd g).2 a b)).symm

end Main

end GlobalTheory.OrdLoc.TangentDual

theorem GlobalTheory.OrdLoc.tangent_finrank_eq_twelve :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (x : U.R →ₐ[O] O), IsBase D.η D.Ψ U.r.hom x → ∀ T : Submodule E (U.R →ₗ[O] E), (∀ δ, δ ∈ T ↔ (∀ a b, δ (a * b) = algebraMap O E (x a) * δ b + algebraMap O E (x b) * δ a) ∧ ∀ a ∈ GlobalTheory.OrdLoc.IY D U, δ a = 0) → finrank E ↥T = 12 := by
  intro hL l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ _ x hx T hT
  obtain ⟨hPC, hCP⟩ := GlobalTheory.T.saturatedOrdinaryIdeal_cuts_out_crystalline_locus hL D U
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  rw [GlobalTheory.OrdLoc.TangentDual.tangent D U E x hx hPC hCP T hT (GlobalTheory.OrdLoc.TangentDual.le_ker D U E x hx hCP),
    UpperTheory.finrank_local_cocycles_adjoint_unitaryThree_eq_twelve hL D E]
