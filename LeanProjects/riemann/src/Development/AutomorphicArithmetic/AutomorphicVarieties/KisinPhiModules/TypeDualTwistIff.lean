import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinCrystalline.TypeSt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc UpperTheory.V.Lit

section
open TensorProduct GlobalTheory.Pst Polynomial Matrix

private theorem zpow_fix {Q R : Type} [Field Q] [CommRing R] [Algebra Q R] (f : R →ₐ[Q] R) (T : Rˣ) (c : Qˣ)
    (h : f (T : R) = (c : Q) • T) (m : ℤ) :
    ((c ^ m : Qˣ) : Q) • f ((T ^ (-m) : Rˣ) : R) = ((T ^ (-m) : Rˣ) : R) := by
  have e : Units.map (f : R →* R) T = Units.map (algebraMap Q R : Q →* R) c * T := by
    ext; simpa [Algebra.smul_def] using h
  have e' : Units.map (algebraMap Q R : Q →* R) (c ^ m) * Units.map (f : R →* R) (T ^ (-m)) = T ^ (-m) := by
    rw [map_zpow, map_zpow, e, mul_zpow, ← mul_assoc, ← _root_.zpow_add]; simp
  rw [Algebra.smul_def]
  exact congrArg Units.val e'

private theorem exists_phi {Q B R : Type} [Field Q] [CommRing B] [Algebra Q B] [CommRing R] [Algebra Q R]
    (n : ℕ) (u : Rˣ) :
    ∃ Φ : (Fin n → B) ⊗[Q] R ≃ₗ[Q] ((Fin n → B) →ₗ[B] B ⊗[Q] R),
      ∀ v r w, Φ (v ⊗ₜ r) w = (v ⬝ᵥ w) ⊗ₜ ((u : R) * r) := by
  refine ⟨(LinearEquiv.lTensor (Fin n → B) (u.mulLeftLinearEquiv Q R)).trans
    ((TensorProduct.piLeft Q R (fun _ : Fin n => B)).trans ((Pi.basisFun B (Fin n)).constr Q)), fun v r w => ?_⟩
  simp [Module.Basis.constr_apply_fintype, dotProduct, sum_tmul, smul_tmul', mul_comm, TensorProduct.piLeft]

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {B : Type} [CommRing B] [Algebra ℚ_[l] B]

private theorem transfer {V W : Type} [AddCommGroup V] [Module B V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] B V]
    [AddCommGroup W] [Module B W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] B W]
    (ρ : Representation B ↥(GK K) V) (σ : Representation B ↥(GK K) W)
    (Φ : V ⊗[ℚ_[l]] Bst (PP l) ≃+ (W →ₗ[B] B ⊗[ℚ_[l]] Bst (PP l)))
    (h1 : ∀ (g : ↥(GK K)) x, Φ (stRep (PP l) (resCoef ℚ_[l] ρ) g x) =
      (actBst (g : GQ l)).comp ((Φ x).comp (σ g⁻¹)))
    (h2 : ∀ c x, Φ (Thick.sm V (Bst (PP l)) c x) = (LinearMap.mulLeft B (toSt c)).comp (Φ x))
    (n : ℕ) (t : ↥(GK K) → B) : TypeSt K ρ n t ↔ TypeLit K σ n t := by
  have h3 : ∀ x, x ∈ Dpst (PP l) (resCoef ℚ_[l] ρ) ↔ Φ x ∈ DpstHom K σ := by
    intro x
    rw [mem_Dpst]
    refine exists_congr fun K' => forall_congr' fun g => imp_congr_right fun _ => ?_
    rw [← Φ.injective.eq_iff, h1]
    constructor
    · intro h v
      conv_lhs => rw [← h]
      simp
    · intro h
      ext1 v
      simp [← h]
  have h4 : ∀ (y : V ⊗[ℚ_[l]] Bst (PP l)) (c : Fin n → B ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) (x : Fin n → V ⊗[ℚ_[l]] Bst (PP l)),
      y = ∑ a, Thick.sm V (Bst (PP l)) (c a) (x a) ↔
        Φ y = ∑ a, (LinearMap.mulLeft B (toSt (c a))).comp (Φ (x a)) := by
    intro y c x
    rw [← Φ.injective.eq_iff, map_sum]
    simp only [h2]
  unfold TypeSt TypeLit
  refine (Equiv.piCongrRight fun _ : Fin n => Φ.toEquiv).exists_congr fun x => ?_
  refine and_congr (forall_congr' fun a => h3 _) (and_congr ?_ ?_)
  · refine Φ.toEquiv.forall_congr fun y => imp_congr (h3 _) (existsUnique_congr fun c => h4 _ _ _)
  · refine forall_congr' fun γ => imp_congr_right fun _ => forall_congr' fun M => imp_congr_left
      (forall_congr' fun b => ?_)
    rw [h4 _ (fun a => M a b), h1]
    rfl

end

open TensorProduct GlobalTheory.Pst Polynomial Matrix in
theorem UpperTheory.type_dual_twist_iff :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] (n : ℕ) (ρ : ↥(GK K) →* GL (Fin n) B) (a : ℤ) (t : ↥(GK K) → B), TypeSt K (colRep ρ) n t ↔ TypeLit K (colRep (dualTw (((cycA l l B).comp (GK K).subtype) ^ (-a)) ρ)) n t := by
  intro l _ K B _ _ _ _ n ρ a t
  let T : (Bst (PP l))ˣ := Units.map (C : (PP l).R.B →+* Bst (PP l)) (isUnit_tB (PP l)).unit
  have hT : (T : Bst (PP l)) = C (PP l).tB := rfl
  have hu : ∀ g : GQ l, (((PP l).χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) • actSt (PP l) g ((T ^ (-a) : (Bst (PP l))ˣ) : Bst (PP l)) =
      ((T ^ (-a) : (Bst (PP l))ˣ) : Bst (PP l)) :=
    fun g => zpow_fix (actSt (PP l) g) T ((PP l).χQ g) (by rw [hT, actSt_C, smul_C, localPrime_galoisAction_periodT]) a
  have hχ : ∀ g : GQ l, cycA l l B g = Units.map (algebraMap ℚ_[l] B : ℚ_[l] →* B) ((PP l).χQ g) := by
    intro g
    ext
    simp only [cycA, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, (cycFacts l l).2.2 g]
    exact IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B _
  have hχ' : ∀ g : ↥(GK K), (((((cycA l l B).comp (GK K).subtype) ^ (-a)) g⁻¹ : Bˣ) : B) =
      algebraMap ℚ_[l] B (((PP l).χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) := by
    intro g
    rw [map_inv, MonoidHom.zpow_apply, _root_.zpow_neg, inv_inv, MonoidHom.comp_apply, hχ, ← map_zpow]
    rfl
  generalize T ^ (-a) = u at hu
  generalize ((cycA l l B).comp (GK K).subtype) ^ (-a) = χ at hχ'
  obtain ⟨Φ, hΦ⟩ := exists_phi (Q := ℚ_[l]) (B := B) n u
  refine transfer _ _ Φ.toAddEquiv (fun g x => ?_) (fun c x => ?_) n t
  · change Φ _ = (actBst (g : GQ l)).comp ((Φ x).comp _)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp, LinearMap.comp_add]
    | tmul v b =>
      refine LinearMap.ext fun w => ?_
      have e : colRep (dualTw χ ρ) g⁻¹ w = (χ g⁻¹ : B) • ((ρ g : Matrix (Fin n) (Fin n) B)ᵀ *ᵥ w) := by
        simp [colRep, dualTw, Matrix.smul_mulVec]
      have e' : resCoef ℚ_[l] (colRep ρ) g v = (ρ g : Matrix (Fin n) (Fin n) B) *ᵥ v := rfl
      rw [stRep_tmul, hΦ, LinearMap.comp_apply, LinearMap.comp_apply, hΦ, e, e', hχ', actBst,
        AlgebraTensorModule.map_tmul, dotProduct_smul, algebraMap_smul, LinearMap.id_apply, smul_tmul,
        LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, map_mul, ← smul_mul_assoc, hu,
        dotProduct_mulVec, vecMul_transpose]
  · change Φ _ = (LinearMap.mulLeft B (toSt c)).comp (Φ x)
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, LinearMap.add_apply, map_add, hx, hy, map_add]
      refine LinearMap.ext fun w => ?_
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, add_mul]
    | tmul p k =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, LinearMap.comp_add]
    | tmul v b =>
      refine LinearMap.ext fun w => ?_
      rw [Thick.sm_tmul, hΦ, LinearMap.comp_apply, hΦ, LinearMap.mulLeft_apply, toSt,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, smul_dotProduct,
        Algebra.smul_def k, mul_left_comm]
      rfl
