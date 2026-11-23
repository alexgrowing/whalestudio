import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceComponent

section General

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']

theorem tens_comp (φ : R'' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (k : R' →ₗ[F] R'')
    (hk : ∀ a b, k (a * b) = k a * k b) (h : ∀ a, k (j (φ a)) = k (j 1) * a) (z : R'' ⊗[F] E) :
    tensNU k hk (tensNU j hj (Algebra.TensorProduct.map φ (AlgHom.id F E) z)) = (k (j 1) ⊗ₜ[F] (1 : E)) * z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [h]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

theorem mat_ext_ext_map (φ : R'' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (k : R' →ₗ[F] R'')
    (hk : ∀ a b, k (a * b) = k a * k b) (h : ∀ a, k (j (φ a)) = k (j 1) * a) (g : HA R'' σ J) :
    (HA.mat R'' σ J (extH σ J k hk (extH σ J j hj (mapH σ J φ g)))).1 =
      (k (j 1) ⊗ₜ[F] (1 : E)) • (HA.mat R'' σ J g).1 +
        (1 - k (j 1) ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin M) (Fin M) (R'' ⊗[F] E)) := by
  refine Matrix.ext fun r s => ?_
  have e1 : tensNU (E := E) k hk (tensNU (E := E) j hj 1) = k (j 1) ⊗ₜ[F] (1 : E) := by
    rw [Algebra.TensorProduct.one_def, tensNU_tmul, tensNU_tmul]
  rw [mat_extH, mat_extH, mat_mapH, map_add, tens_comp φ j hj k hk h, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases e : r = s
  · subst e
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one, mul_one, mul_one, map_sub, e1]
    ring
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, mul_zero, mul_zero, mul_zero, map_zero, zero_add, zero_add,
      add_zero]

theorem mix_mul {A l m n : Type} [CommRing A] [Fintype m] {b : A} (hb : b * b = b) (X X' : Matrix l m A)
    (Y Y' : Matrix m n A) :
    (b • X + (1 - b) • X') * (b • Y + (1 - b) • Y') = b • (X * Y) + (1 - b) • (X' * Y') := by
  have h1 : b * (1 - b) = 0 := by linear_combination -hb
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, hb, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem mix_act {A m n : Type} [CommRing A] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {b : A}
    (hb : b * b = b) (X : Matrix m m A) (w : Matrix m n A) (Y : Matrix n n A) :
    (b • X + (1 - b) • (1 : Matrix m m A)) * w * (b • Y + (1 - b) • (1 : Matrix n n A)) =
      b • (X * w * Y) + (1 - b) • w := by
  have e : w = b • w + (1 - b) • w := by rw [← add_smul, add_sub_cancel, one_smul]
  conv_lhs => rw [e]
  rw [mix_mul hb, mix_mul hb, Matrix.one_mul, Matrix.mul_one]

theorem mix_act_smul {A m n : Type} [CommRing A] [Fintype m] [Fintype n] {b : A}
    (hb : b * b = b) (X : Matrix m m A) (w : Matrix m n A) (Y : Matrix n n A) :
    b • (X * w * Y) = b • (X * (b • w) * Y) + (1 - b) • b • w := by
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul, hb, h2, zero_smul, add_zero]

end General

variable {D : D7}

theorem mt_gAt (V : HSp D) (p : Place D) (g : GA D V) :
    Formalism.L2.Theta.mt V (gAt V p g) =
      idem D p • Formalism.L2.Theta.mt V g + (1 - idem D p) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  classical
  cases p with
  | inl v =>
    refine mat_ext_ext_map (R'' := AF D.host.F) D.sp.cm.sig V.gram (GlobalTheory.AdelicU.evFin D.host.F v)
      (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v)
      (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (fun _ _ => Prod.ext (mul_zero _).symm rfl) (fun a => ?_) g
    refine Prod.ext (zero_mul _).symm (GlobalTheory.AdelicU.af_ext fun u => ?_)
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ u (GlobalTheory.AdelicU.singleFin v _) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ u (GlobalTheory.AdelicU.singleFin v 1 * a.2)
    rw [map_mul]
    by_cases e : u = v
    · subst e
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, GlobalTheory.AdelicU.evalV_singleFin_ne e, zero_mul]
  | inr τ =>
    refine mat_ext_ext_map (R'' := AF D.host.F) D.sp.cm.sig V.gram (GlobalTheory.AdelicU.evInf D.host.F (plTau D τ))
      (GlobalTheory.AutFunCompare.sgW (plTau D τ)) (GlobalTheory.AutFunCompare.sgW_mul _)
      (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm) (fun a => ?_) g
    refine Prod.ext (funext fun u => ?_) (zero_mul _).symm
    change (Pi.single (M := fun w : InfinitePlace D.host.F => w.Completion) (plTau D τ) (a.1 (plTau D τ))) u =
      (Pi.single (M := fun w : InfinitePlace D.host.F => w.Completion) (plTau D τ) 1) u * a.1 u
    by_cases e : u = plTau D τ
    · subst e
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne e, Pi.single_eq_of_ne e, zero_mul]

theorem idem_mul_self (p : Place D) : idem D p * idem D p = idem D p := by
  cases p with
  | inl v =>
    change algebraMap (AF D.host.F) (AE D) _ * algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [← map_mul]
    refine congrArg _ (Prod.ext (mul_zero _) ?_)
    exact (GlobalTheory.AdelicU.singleFin_mul v 1 1).symm.trans (by rw [mul_one]; rfl)
  | inr τ =>
    change algebraMap (AF D.host.F) (AE D) _ * algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [← map_mul]
    refine congrArg _ (Prod.ext ?_ (mul_zero _))
    exact (GlobalTheory.AutFunCompare.sgW_mul (plTau D τ) 1 1).symm.trans (by rw [mul_one]; rfl)

theorem gAt_gAt_self (V : HSp D) (p : Place D) (g : GA D V) : gAt V p (gAt V p g) = gAt V p g := by
  cases p <;> simp [gAt]

theorem gAt_gAt_ne (V : HSp D) (p : Place D) (g : GA D V) (q : Place D) (h : q ≠ p) : gAt V q (gAt V p g) = 1 := by
  cases p with
  | inl v =>
    cases q with
    | inl u =>
      have e : u ≠ v := fun e => h (congrArg _ e)
      simp only [gAt]
      rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e, map_one]
    | inr ρ => simp [gAt]
  | inr τ =>
    cases q with
    | inl u => simp [gAt]
    | inr ρ =>
      have e : plTau D ρ ≠ plTau D τ := fun e => h (congrArg _ ((GlobalTheory.AdelicU.placeOf_bijective D).1 e))
      simp only [gAt]
      rw [GlobalTheory.AdelicU.projArch_embArch_ne _ _ e, map_one]

theorem actO_gAt (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T) :
    actO S T (gAt S p g) (gAt T p h) w = idem D p • actO S T g h w + (1 - idem D p) • w := by
  unfold actO
  rw [← gAt_inv, mt_gAt, mt_gAt]
  exact mix_act (idem_mul_self p) _ _ _

theorem wAt_actO (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T) :
    wAt p (actO S T g h w) = actO S T (gAt S p g) (gAt T p h) (wAt p w) := by
  rw [actO_gAt]
  exact mix_act_smul (idem_mul_self p) _ _ _

theorem gAt_laws : ∀ (D : D7), (∀ (V : HSp D) (p : Place D) (g : GA D V), Formalism.L2.Theta.mt V (gAt V p g) = idem D p • Formalism.L2.Theta.mt V g + (1 - idem D p) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ gAt V p (gAt V p g) = gAt V p g ∧ ∀ q, q ≠ p → gAt V q (gAt V p g) = 1) ∧ ∀ (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T), actO S T (gAt S p g) (gAt T p h) w = idem D p • actO S T g h w + (1 - idem D p) • w ∧ wAt p (actO S T g h w) = actO S T (gAt S p g) (gAt T p h) (wAt p w) :=
  fun _ => ⟨fun V p g => ⟨mt_gAt V p g, gAt_gAt_self V p g, gAt_gAt_ne V p g⟩,
    fun S T p g h w => ⟨actO_gAt S T p g h w, wAt_actO S T p g h w⟩⟩

end GlobalTheory.PlaceComponent

end
