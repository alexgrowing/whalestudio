import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.OneFormCoh

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def extForm (hp : Par F) (l : Glob1 F →ₗ[R] R) (T : C) : Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T :=
  (hp T).lift ((Algebra.linearMap R (F.obj T)) ∘ₗ l)

theorem extForm_ev (hp : Par F) (l : Glob1 F →ₗ[R] R) (T : C) (v : Glob1 F) :
    extForm F hp l T (v.1 T) = algebraMap R (F.obj T) (l v) :=
  (hp T).lift_eq _ v

theorem extended_form_naturality (hp : Par F) (l : Glob1 F →ₗ[R] R) {T T' : C} (φ : T ⟶ T') (α : Ω[F.obj T⁄R]) :
    extForm F hp l T' (p1 F φ α) = mp F φ (extForm F hp l T α) := by
  refine (hp T).inductionOn α (fun α => GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T' (GlobalTheory.CechDR.p1 F φ α) =
    GlobalTheory.CatCoh.mp F φ (GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T α)) ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · intro v
    change GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T' (GlobalTheory.CechDR.p1 F φ (v.1 T)) =
      GlobalTheory.CatCoh.mp F φ (GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T (v.1 T))
    have hv : GlobalTheory.CechDR.p1 F φ (v.1 T) = v.1 T' := by
      first
        | exact v.2 φ
        | exact v.2 T T' φ
        | exact (v.2 φ).symm
        | exact (v.2 T T' φ).symm
    rw [hv, GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, AlgHom.commutes]
  · intro s n hn
    rw [GlobalTheory.CechDR.oneFormsMapOfFunctorMorphism_smul, map_smul, map_smul, hn, smul_eq_mul, smul_eq_mul, map_mul]
  · intro n₁ n₂ h₁ h₂
    rw [map_add, map_add, h₁, h₂, map_add, map_add]

theorem extForm_sum (hp : Par F) {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Glob1 F →ₗ[R] R)
    (hw : ∀ v, ∑ i, l i v • w i = v) (T : C) (α : Ω[F.obj T⁄R]) :
    ∑ i, extForm F hp (l i) T α • (w i).1 T = α := by
  refine (hp T).inductionOn α (fun α => ∑ i, GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp (l i) T α • (w i).1 T = α) ?_ ?_ ?_ ?_
  · simp only [map_zero, zero_smul, Finset.sum_const_zero]
  · intro v
    change ∑ i, GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp (l i) T (v.1 T) • (w i).1 T = v.1 T
    simp only [GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, algebraMap_smul]
    have h := congrArg (MainStatements.Hodge.evForm F T) (hw v)
    rw [map_sum] at h
    simp only [map_smul] at h
    exact h
  · intro s m hm
    conv_rhs => rw [← hm]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_smul]
  · intro m₁ m₂ h₁ h₂
    conv_rhs => rw [← h₁, ← h₂]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, add_smul]

def muMap : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F :=
  TensorProduct.lift (LinearMap.mk₂ R (fun (f : Z1 F) (v : Glob1 F) T T' φ ↦ f.1 T T' φ • v.1 T')
    (fun f f' v ↦ by funext T T' φ; simp [add_smul])
    (fun r f v ↦ by funext T T' φ; simp)
    (fun f v v' ↦ by funext T T' φ; simp)
    (fun r f v ↦ by funext T T' φ; simp [smul_comm r]))

theorem muMap_tmul (f : Z1 F) (v : Glob1 F) {T T' : C} (φ : T ⟶ T') :
    muMap F (f ⊗ₜ v) T T' φ = f.1 T T' φ • v.1 T' := rfl

def contr (l : Glob1 F →ₗ[R] R) : Z1 F ⊗[R] Glob1 F →ₗ[R] Z1 F :=
  (TensorProduct.rid R (Z1 F)).toLinearMap ∘ₗ LinearMap.lTensor (Z1 F) l

theorem contr_tmul (l : Glob1 F →ₗ[R] R) (f : Z1 F) (v : Glob1 F) :
    contr F l (f ⊗ₜ v) = l v • f := by
  simp [contr]

theorem extForm_muMap (hp : Par F) (l : Glob1 F →ₗ[R] R) (t : Z1 F ⊗[R] Glob1 F) {T T' : C}
    (φ : T ⟶ T') : extForm F hp l T' (muMap F t T T' φ) = (contr F l t).1 T T' φ := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact map_zero _
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, Submodule.coe_add, hx, hy]
  | tmul f v =>
    simp only [GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul, GlobalTheory.CompanionTheory.OneFormCoh.contr_tmul, map_smul, GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
    ring

theorem sum_contr {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Glob1 F →ₗ[R] R)
    (hw : ∀ v, ∑ i, l i v • w i = v) (t : Z1 F ⊗[R] Glob1 F) :
    ∑ i, contr F (l i) t ⊗ₜ[R] w i = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]
  | tmul f v =>
    simp_rw [GlobalTheory.CompanionTheory.OneFormCoh.contr_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, hw]

def pushZ (hp : Par F) (l : Glob1 F →ₗ[R] R) (a : A1 F)
    (ha : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) : Z1 F :=
  ⟨fun T T' φ ↦ extForm F hp l T' (a T T' φ), fun T T' T'' φ ψ ↦ by
    change extForm F hp l T'' (a T T'' (φ ≫ ψ)) =
      mp F ψ (extForm F hp l T' (a T T' φ)) + extForm F hp l T'' (a T' T'' ψ)
    rw [ha, map_add, extended_form_naturality]⟩

theorem main (hF : Framed F) :
    ∃ mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F, (∀ f ω T T' φ, mu (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T') ∧
      (∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
        a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, mu t = a) ∧
      ∀ (t : Z1 F ⊗[R] Glob1 F) (β : A0 F), (∀ T T' φ, mu t T T' φ = β T' - p1 F φ (β T)) →
        (H1.mk F).rTensor (Glob1 F) t = 0 := by
  obtain ⟨-, hp, hfin, hproj⟩ := hF
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R (GlobalTheory.CechDR.Glob1 F)
  obtain ⟨w, l, hw⟩ : ∃ (w : Fin n → GlobalTheory.CechDR.Glob1 F) (l : Fin n → GlobalTheory.CechDR.Glob1 F →ₗ[R] R),
      ∀ v, ∑ i, l i v • w i = v := by
    refine ⟨fun i => f (Pi.single i 1), fun i => LinearMap.proj i ∘ₗ g, fun v => ?_⟩
    have hsum : ∑ i, g v i • (Pi.single i 1 : Fin n → R) = g v := by
      ext j
      simp [Pi.single_apply]
    calc ∑ i, (LinearMap.proj i ∘ₗ g) v • f (Pi.single i 1)
        = f (∑ i, g v i • (Pi.single i 1 : Fin n → R)) := by
          rw [map_sum]
          simp only [map_smul, LinearMap.comp_apply, LinearMap.proj_apply]
      _ = v := by
          rw [hsum]
          exact LinearMap.congr_fun hfg v
  refine ⟨GlobalTheory.CompanionTheory.OneFormCoh.muMap F, fun x ω T T' φ => GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul F x ω φ, ?_, ?_⟩
  · intro a ha
    refine ⟨∑ i, GlobalTheory.CompanionTheory.OneFormCoh.pushZ F hp (l i) a ha ⊗ₜ w i, ?_⟩
    funext T T' φ
    rw [map_sum]
    simp only [Finset.sum_apply, GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul]
    exact GlobalTheory.CompanionTheory.OneFormCoh.extForm_sum F hp w l hw T' (a T T' φ)
  · intro t β hβ
    have hzero : ∀ i, GlobalTheory.CatCoh.H1.mk F
        (GlobalTheory.CompanionTheory.OneFormCoh.contr F (l i) t) = 0 := by
      intro i
      rw [GlobalTheory.CatCoh.H1.mk_eq_zero]
      refine ⟨fun T => GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp (l i) T (β T), ?_⟩
      funext T T' φ
      rw [GlobalTheory.CatCoh.amitsur_d0_apply, ← GlobalTheory.CompanionTheory.OneFormCoh.extForm_muMap F hp, hβ, map_sub,
        GlobalTheory.CompanionTheory.OneFormCoh.extended_form_naturality]
    rw [← GlobalTheory.CompanionTheory.OneFormCoh.sum_contr F w l hw t, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.rTensor_tmul, hzero, TensorProduct.zero_tmul]

theorem oneFormCohSt : OneFormCohSt := by
  unfold MainStatements.Hodge.OneFormCohSt MainStatements.Hodge.AllF
  intro R _ C _ F hF
  exact GlobalTheory.CompanionTheory.OneFormCoh.main F hF

end GlobalTheory.CompanionTheory.OneFormCoh
