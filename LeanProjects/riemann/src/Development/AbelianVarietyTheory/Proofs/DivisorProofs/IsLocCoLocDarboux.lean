import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.LocCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_mul (v : Pl F) (a : Fv F v) (b : AF F) :
    GlobalTheory.LatVac.liftV v a * b = GlobalTheory.LatVac.liftV v (a * evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v a * b.2 = GlobalTheory.AdelicU.singleFin v (a * evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem liftV_smul_liftE (v : Pl F) (a : Fv F v) (z : Fv F v ⊗[F] E) :
    GlobalTheory.LatVac.liftV v a • liftE (E := E) v z = liftE v (a • z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, smul_add, hx, hy, smul_add, map_add]
  | tmul b e =>
    rw [TensorProduct.smul_tmul', liftE, TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, liftV_mul, GlobalTheory.LatVac.evFin_liftV]

theorem compFin_liftE (v : Pl F) (z : Fv F v ⊗[F] E) : compFin F E v (liftE v z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b e =>
    rw [liftE, TensorProduct.map_tmul]
    change evFin F v (GlobalTheory.LatVac.liftV v b) ⊗ₜ[F] e = b ⊗ₜ[F] e
    rw [GlobalTheory.LatVac.evFin_liftV]

theorem liftV_one_smul (v : Pl F) (z : AE F E) :
    GlobalTheory.LatVac.liftV v 1 • z = liftE v (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]
  | tmul b e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_mul, one_mul]
    change _ = liftE v (evFin F v b ⊗ₜ[F] e)
    rw [liftE, TensorProduct.map_tmul]
    rfl

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl F) (z : AE F E) :
    compFin F E v (cA σ z) = cv σ v (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul b e => rfl

theorem trace_tmul (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem evFin_trace (v : Pl F) (z : AE F E) :
    evFin F v (Algebra.trace (AF F) (AE F E) z) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul b e =>
    change _ = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (evFin F v b ⊗ₜ[F] e)
    rw [trace_tmul, trace_tmul, map_mul, AlgHom.commutes]

end GlobalTheory.HoweLocal.LocCoords

namespace GlobalTheory.HoweLocal.LocCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symp_lift (σ : E →ₐ[F] E) (v : Pl F) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x x' : Matrix (Fin n) (Fin d) (Fv F v ⊗[F] E)) :
    symp (R := Fv F v) (cv σ v) (-1) (Jv v JX) (Jv v JW) x x' =
      evFin F v (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) (x.map (liftE v)) (x'.map (liftE v))) := by
  unfold symp hTens
  rw [evFin_trace]
  congr 1
  simp only [map_mul, map_neg, map_one, map_sum, Matrix.map_apply, compFin_cA, compFin_liftE]
  rfl

def locE (σ : E →ₐ[F] E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F) :
    Matrix (Fin n) (Fin d) (Fv F v ⊗[F] E) ≃ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) where
  toFun x := GlobalTheory.LatVac.locCo M.co v (x.map (liftE v))
  map_add' x y := by rw [Matrix.map_add _ (map_add _), map_add]
  map_smul' a x := by
    have h : (a • x).map (liftE v) = GlobalTheory.LatVac.liftV v a • x.map (liftE v) := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, liftV_smul_liftE]
    simp only [RingHom.id_apply, h, GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
    ext k
    · simp [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, liftV_mul, GlobalTheory.LatVac.evFin_liftV]
    · simp [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, liftV_mul, GlobalTheory.LatVac.evFin_liftV]
  invFun p := (M.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k))).map
    (compFin F E v)
  left_inv x := by
    have h1 : GlobalTheory.LatVac.liftV v 1 • x.map (liftE v) = x.map (liftE v) := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, liftV_smul_liftE, one_smul]
    have h2 : ((fun k => GlobalTheory.LatVac.liftV v ((GlobalTheory.LatVac.locCo M.co v (x.map (liftE v))).1 k),
        fun k => GlobalTheory.LatVac.liftV v ((GlobalTheory.LatVac.locCo M.co v (x.map (liftE v))).2 k)) :
          (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) = M.co.e (x.map (liftE v)) := by
      conv_rhs => rw [← h1, map_smul]
      ext k
      · simp [GlobalTheory.LatVac.locCo, liftV_mul]
      · simp [GlobalTheory.LatVac.locCo, liftV_mul]
    simp only
    rw [h2, LinearEquiv.symm_apply_apply]
    ext i j; simp [compFin_liftE]
  right_inv p := by
    set y := M.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)) with hy
    have h1 : (y.map (compFin F E v)).map (liftE v) = GlobalTheory.LatVac.liftV v 1 • y := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, liftV_one_smul]
    simp only
    rw [h1]
    show (fun k => evFin F v ((M.co.e (GlobalTheory.LatVac.liftV v 1 • y)).1 k),
      fun k => evFin F v ((M.co.e (GlobalTheory.LatVac.liftV v 1 • y)).2 k)) = p
    rw [map_smul, hy, LinearEquiv.apply_symm_apply]
    ext k <;> simp [liftV_mul, GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.HoweLocal.LocCoords

namespace GlobalTheory.HoweLocal.LocCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def locDarboux (σ : E →ₐ[F] E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F) :
    Darboux (symp (R := Fv F v) (cv σ v) (-1) (Jv v X.J) (Jv v W.J)) (Fin n × Fin d) where
  e := locE σ M v
  form x x' := by
    rw [symp_lift, M.co.form]
    simp only [locE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, dotProduct, map_sub, map_sum, map_mul]

theorem isLocCo_locDarboux (σ : E →ₐ[F] E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F) :
    IsLocCo σ M v (locDarboux σ M v) := fun _ => rfl

end GlobalTheory.HoweLocal.LocCoords

theorem GlobalTheory.HoweLocal.exists_isLocCo : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (v : Pl F),
      ∃ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J))
        (Fin n × Fin d), GlobalTheory.HoweLocal.IsLocCo σ M v co :=
  fun _ _ _ _ _ _ _ σ _ _ _ _ _ M v => ⟨_, GlobalTheory.HoweLocal.LocCoords.isLocCo_locDarboux σ M v⟩
