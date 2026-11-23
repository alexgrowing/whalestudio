import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.CompIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_cA {R : Type} [CommRing R] [Algebra F R] (f : AF F →ₐ[F] R) (σ : E →ₐ[F] E) (y : AE F E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (cA σ y) =
      Algebra.TensorProduct.map (AlgHom.id R R) σ (Algebra.TensorProduct.map f (AlgHom.id F E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_unit {A B : Type} [CommRing A] [CommRing B] {m : ℕ} (ρ : A →+* B) (c : A → A) (c' : B → B)
    (hc : ∀ y, ρ (c y) = c' (ρ y)) (M J : Matrix (Fin m) (Fin m) A) :
    (Mᵀ * J * M.map c).map ρ = (M.map ρ)ᵀ * J.map ρ * (M.map ρ).map c' := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map]
  congr 2
  funext y
  exact hc y

theorem mapNU_mul {A B : Type} [CommRing A] [CommRing B] {m : ℕ} (S : A →ₙ+* B) (X Y : Matrix (Fin m) (Fin m) A) :
    (X * Y).map S = X.map S * Y.map S := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

def liftMat (v : Pl F) (m : ℕ) : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E) →* Matrix (Fin m) (Fin m) (AE F E) where
  toFun h := 1 + (h - 1).map (Supp.singleTens E v)
  map_one' := by simp
  map_mul' a b := by
    have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    rw [e, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), mapNU_mul]
    noncomm_ring

theorem liftMat_apply (v : Pl F) {m : ℕ} (h : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :
    liftMat v m h = 1 + (h - 1).map (Supp.singleTens E v) := rfl

theorem liftMat_map_zero {B : Type} [CommRing B] (v : Pl F) {m : ℕ} (ρ : AE F E →+* B)
    (hρ : ∀ y, ρ (Supp.singleTens E v y) = 0) (h : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :
    (liftMat v m h).map ρ = 1 := by
  rw [liftMat_apply, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_map]
  have : (ρ ∘ Supp.singleTens E v) = fun _ => 0 := funext hρ
  rw [this]
  ext i j
  simp

theorem liftMat_map_self (v : Pl F) {m : ℕ} (h : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :
    (liftMat v m h).map (compFin F E v) = h := by
  rw [liftMat_apply, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_map]
  have : (compFin F E v ∘ Supp.singleTens E v) = id := funext (Supp.compFin_singleTens_self v)
  rw [this, Matrix.map_id]
  abel

theorem incM_map (v : Pl F) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) :
    (incM F J).map (compFin F E v) = Jv v J := by
  ext i j
  exact Supp.compFin_one_tmul v (J i j)

variable (σ : E →ₐ[F] E) {m : ℕ} (Y : Spc F E m) (v : Pl F)

variable (m) in

def fwdGL : GL (Fin m) (AE F E) →* GL (Fin m) (Fv F v ⊗[F] E) :=
  Units.map (compFin F E v).mapMatrix.toMonoidHom

theorem fwd_mem (g : UA σ Y.J) : fwdGL m v g.1 ∈ UG (cv σ v) (Jv v Y.J) := by
  have hg : (g.1 : Matrix (Fin m) (Fin m) (AE F E))ᵀ * incM F Y.J * (g.1 : Matrix (Fin m) (Fin m) (AE F E)).map (cA σ) =
      incM F Y.J := g.2
  show ((g.1 : Matrix (Fin m) (Fin m) (AE F E)).map (compFin F E v))ᵀ * Jv v Y.J *
      ((g.1 : Matrix (Fin m) (Fin m) (AE F E)).map (compFin F E v)).map (cv σ v) = Jv v Y.J
  rw [← incM_map v Y.J, ← map_unit (compFin F E v) (cA σ) (cv σ v) (fun y => map_cA (evFin F v) σ y), hg]

def fwd : UAtGrp σ Y (evFin F v) →* UG (cv σ v) (Jv v Y.J) :=
  ((fwdGL m v).comp ((UG (cA σ) (incM F Y.J)).subtype.comp (UAtGrp σ Y (evFin F v)).subtype)).codRestrict _
    (fun g => fwd_mem σ Y v g.1)

variable (m) in

def bwdGL : GL (Fin m) (Fv F v ⊗[F] E) →* GL (Fin m) (AE F E) := Units.map (liftMat v m)

theorem bwd_mem (h : UG (cv σ v) (Jv v Y.J)) : bwdGL m v h.1 ∈ UG (cA σ) (incM F Y.J) := by
  have hh : (h.1 : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E))ᵀ * Jv v Y.J *
      (h.1 : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)).map (cv σ v) = Jv v Y.J := h.2
  show (liftMat v m h.1.1)ᵀ * incM F Y.J * (liftMat v m h.1.1).map (cA σ) = incM F Y.J
  ext i j
  apply Supp.adTens_ext
  · intro w
    have e := congrArg (fun M => M i j) (map_unit (compInf F E w) (cA σ)
      (Algebra.TensorProduct.map (AlgHom.id w.Completion w.Completion) σ) (fun y => map_cA (evInf F w) σ y)
      (liftMat v m h.1.1) (incM F Y.J))
    rw [Matrix.map_apply] at e
    rw [e, liftMat_map_zero v _ (fun y => Supp.compInf_singleTens w v y), Matrix.transpose_one, Matrix.one_mul,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    rfl
  · intro u
    have e := congrArg (fun M => M i j) (map_unit (compFin F E u) (cA σ) (cv σ u) (fun y => map_cA (evFin F u) σ y)
      (liftMat v m h.1.1) (incM F Y.J))
    rw [Matrix.map_apply] at e
    rw [e]
    rcases eq_or_ne u v with rfl | hu
    · rw [liftMat_map_self, incM_map, hh]
      exact (congrArg (fun M => M i j) (incM_map u Y.J)).symm
    · rw [liftMat_map_zero v _ (fun y => Supp.compFin_singleTens_ne hu y), Matrix.transpose_one, Matrix.one_mul,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      rfl

theorem liftMat_at (h : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) : At (evFin F v) (liftMat v m h - 1) := by
  intro u hu
  rw [liftMat_apply, add_sub_cancel_left]
  ext i j
  rw [Matrix.smul_apply, Matrix.map_apply, Algebra.smul_def, mul_comm, Supp.singleTens_mul]
  have e : compFin F E v (algebraMap (AF F) (AE F E) u) = 0 := by
    show evFin F v u ⊗ₜ[F] (1 : E) = 0
    rw [hu, TensorProduct.zero_tmul]
  rw [e, mul_zero, map_zero]
  rfl

def bwdU : UG (cv σ v) (Jv v Y.J) →* UA σ Y.J :=
  ((bwdGL m v).comp (UG (cv σ v) (Jv v Y.J)).subtype).codRestrict _ (fun h => bwd_mem σ Y v h)

def bwd : UG (cv σ v) (Jv v Y.J) →* UAtGrp σ Y (evFin F v) :=
  (bwdU σ Y v).codRestrict _ (fun h => liftMat_at v h.1.1)

theorem lift_comp (z : AE F E) (hz : At (evFin F v) z) : Supp.singleTens E v (compFin F E v z) = z := by
  have h1 := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero, Algebra.smul_def] at h1
  conv_rhs => rw [h1]
  rw [show algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) = Supp.singleTens E v 1 from rfl, Supp.singleTens_mul,
    one_mul]

theorem bwd_fwd (g : UAtGrp σ Y (evFin F v)) : bwd σ Y v (fwd σ Y v g) = g := by
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  show liftMat v m ((g.1.1 : Matrix (Fin m) (Fin m) (AE F E)).map (compFin F E v)) = g.1.1
  have hg : At (evFin F v) (mat g.1 - 1) := g.2
  have e : (g.1.1 : Matrix (Fin m) (Fin m) (AE F E)).map (compFin F E v) - 1 =
      ((g.1.1 : Matrix (Fin m) (Fin m) (AE F E)) - 1).map (compFin F E v) := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [liftMat_apply, e, Matrix.map_map]
  ext i j
  have hz : At (evFin F v) (((g.1.1 : Matrix (Fin m) (Fin m) (AE F E)) - 1) i j) := fun u hu => by
    have := congrArg (fun M => M i j) (hg u hu)
    simp only [Matrix.smul_apply, Matrix.zero_apply] at this
    exact this
  rw [Matrix.add_apply, Matrix.map_apply, Function.comp_apply, lift_comp v _ hz, Matrix.sub_apply]
  abel

theorem fwd_bwd (h : UG (cv σ v) (Jv v Y.J)) : fwd σ Y v (bwd σ Y v h) = h := by
  apply Subtype.ext; apply Units.ext
  exact liftMat_map_self v _

end GlobalTheory.HoweLocal.CompIso

namespace GlobalTheory.HoweLocal

open CompIso in

theorem compIso_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (m : ℕ) (Y : Spc F E m) (v : Pl F), ∃ e : UAtGrp σ Y (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v Y.J),
      GlobalTheory.HoweLocal.IsCompIso σ Y v e := by
  intro F E _ _ _ _ _ σ _ m Y v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have hcf : Continuous (compFin F E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
      ((RestrictedProduct.continuous_eval v).comp continuous_snd)
  have hst : Continuous (Supp.singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ (Continuous.prodMk continuous_const (continuous_singleFin v))
  refine ⟨MonoidHom.toMulEquiv (fwd σ Y v) (bwd σ Y v) (MonoidHom.ext (bwd_fwd σ Y v)) (MonoidHom.ext (fwd_bwd σ Y v)),
    fun g => rfl, ?_, ?_⟩
  · show Continuous (fwd σ Y v)
    refine Continuous.subtype_mk ?_ _
    exact (Continuous.units_map _ (continuous_id.matrix_map hcf)).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  · show Continuous (bwd σ Y v)
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (Continuous.units_map _ (continuous_const.add ((continuous_id.sub continuous_const).matrix_map hst))).comp
      continuous_subtype_val

end GlobalTheory.HoweLocal
