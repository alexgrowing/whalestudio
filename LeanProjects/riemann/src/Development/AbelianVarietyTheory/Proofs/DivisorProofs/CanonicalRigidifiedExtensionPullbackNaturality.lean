import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueBaseChangeNaturaStatement

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExtNat

variable {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R')

abbrev via (D : Type) [CommRing D] [Algebra R' D] : Algebra R D := ((algebraMap R' D).comp σ).toAlgebra

def down {D D' : Type} [CommRing D] [Algebra R' D] [CommRing D'] [Algebra R' D'] (ψ : D →ₐ[R'] D') :
    letI := via σ D; letI := via σ D'; D →ₐ[R] D' :=
  letI := via σ D; letI := via σ D'
  { (ψ : D →+* D') with commutes' := fun r ↦ ψ.commutes (σ r) }

@[simp] theorem down_apply {D D' : Type} [CommRing D] [Algebra R' D] [CommRing D'] [Algebra R' D'] (ψ : D →ₐ[R'] D') (a : D) :
    down σ ψ a = ψ a := rfl

variable {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
  (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ)

theorem ptsDown_comp {D D' : Type} [CommRing D] [Algebra R' D] [CommRing D'] [Algebra R' D'] (ψ : D →ₐ[R'] D') (x : Pt A' D) :
    letI := via σ D; letI := via σ D'
    ptsDown m D' (fun _ ↦ rfl) (spOver ψ ≫ x) = spOver (down σ ψ) ≫ ptsDown m D (fun _ ↦ rfl) x := by
  apply Over.OverMorphism.ext
  rfl

theorem fv_pull (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) {D D' : Type} [CommRing D] [Algebra R' D] [CommRing D'] [Algebra R' D'] (ψ : D →ₐ[R'] D') (x : Pt A' D) :
    letI := via σ D; letI := via σ D'
    fv (m.isMor.coef.pullbackOneCocycle f) D D' ψ x = fv f D D' (down σ ψ) (ptsDown m D (fun _ ↦ rfl) x) := by
  letI := via σ D; letI := via σ D'
  exact ((GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq R A f).2 D D' (ptsDown m D (fun _ ↦ rfl) x) (ptsDown m D' (fun _ ↦ rfl) (spOver ψ ≫ x))
    (down σ ψ) (m.isMor.functor.map (trivMap ψ x)) (fun _ ↦ rfl)).2

end GlobalTheory.PtExtNat

namespace GlobalTheory.PtExtNat

variable {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R')
variable {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
  (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ)
variable {p : ℕ} {G : PDivGroup p R} {G' : PDivGroup p R'} (t : G.TorsionTower A) (t' : G'.TorsionTower A')

def sR (n : ℕ) : letI := via σ (G'.A n); G.A n →ₐ[R] G'.A n :=
  letI := via σ (G'.A n)
  { ((t'.semiHom t m).app n).toRingHom with commutes' := ((t'.semiHom t m).app n).map_algebraMap }

@[simp] theorem sR_apply (n : ℕ) (a : G.A n) : sR σ m t t' n a = (t'.semiHom t m).app n a := rfl

theorem ptsDown_y (n : ℕ) :
    letI := via σ (G'.A n)
    ptsDown m (G'.A n) (fun _ ↦ rfl) (t'.y n) = spOver (sR σ m t t' n) ≫ t.y n := by
  apply Over.OverMorphism.ext
  exact (PDivGroup.TorsionTower.semiOf_y (t := t) (t' := t') m n).symm

def corr (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (n : ℕ) : G'.A n :=
  letI := via σ (G'.A n)
  fv f (G.A n) (G'.A n) (sR σ m t t' n) (t.y n)

variable {σ m t t'}

def natDat {c : primDR A} (d : Dat t c) : Dat t' (m.pull c) where
  f := m.isMor.coef.pullbackOneCocycle d.f
  cl := by rw [GrpMor.coe_pull, ← d.cl]; rfl
  g := fun D _ _ x y ↦ letI := via σ D; d.g D (ptsDown m D (fun _ ↦ rfl) x) (ptsDown m D (fun _ ↦ rfl) y)
  add := by
    intro D _ _ D' _ _ ψ x y
    letI := via σ D; letI := via σ D'
    rw [fv_pull σ m, fv_pull σ m, fv_pull σ m]
    have h := d.add D D' (down σ ψ) (ptsDown m D (fun _ ↦ rfl) x) (ptsDown m D (fun _ ↦ rfl) y)
    rw [← ptsDown_comp σ m, ← ptsDown_comp σ m, ← map_mul] at h
    exact h
  h := fun n ↦ (t'.semiHom t m).app n (d.h n) + corr σ m t t' d.f n
  res := by
    intro n
    letI := via σ (G'.A n); letI := via σ (G'.A (n + 1))
    rw [fv_pull σ m, ptsDown_y σ m t t']
    have coc := (GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq R A d.f).1
    have h1 := coc (G.A (n + 1)) (G'.A (n + 1)) (G'.A n) (sR σ m t t' (n + 1)) (down σ (G'.res n : G'.A (n + 1) →ₐ[R'] G'.A n)) (t.y (n + 1)) (sm_whole _)
    have e : (down σ (G'.res n : G'.A (n + 1) →ₐ[R'] G'.A n)).comp (sR σ m t t' (n + 1)) = (sR σ m t t' n).comp (G.res n : G.A (n + 1) →ₐ[R] G.A n) :=
      AlgHom.ext fun a ↦ (t'.semiHom t m).res_app n a
    have h2 := coc (G.A (n + 1)) (G.A n) (G'.A n) (G.res n : G.A (n + 1) →ₐ[R] G.A n) (sR σ m t t' n) (t.y (n + 1)) (sm_whole _)
    rw [e] at h1
    rw [t.res n, d.res n] at h2
    have h3 := (t'.semiHom t m).res_app n (d.h (n + 1))
    simp only [corr, down_apply, sR_apply, map_add, map_sub] at h1 h2 ⊢
    have h4 : ∀ a, (G'.res n : G'.A (n + 1) →ₐ[R'] G'.A n) a = G'.res n a := fun _ ↦ rfl
    simp only [h4] at h1 ⊢
    linear_combination -(h2.symm.trans h1) + h3

end GlobalTheory.PtExtNat

namespace GlobalTheory.PtExtNat

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
variable {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
  {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ}
variable {p : ℕ} {G : PDivGroup p R} {G' : PDivGroup p R'} {t : G.TorsionTower A} {t' : G'.TorsionTower A'}

variable (σ m t t') in

def sL (n : ℕ) : letI := via σ (G'.A n ⊗[R'] G'.A n); G.A n →ₐ[R] G'.A n ⊗[R'] G'.A n :=
  letI := via σ (G'.A n ⊗[R'] G'.A n)
  { (Algebra.TensorProduct.includeLeftRingHom).comp ((t'.semiHom t m).app n).toRingHom with
    commutes' := fun r ↦ by
      change ((t'.semiHom t m).app n) (algebraMap R _ r) ⊗ₜ[R'] (1 : G'.A n) = _
      rw [SemiBialgHom.map_algebraMap]; rfl }

variable (σ m t t') in

def sRt (n : ℕ) : letI := via σ (G'.A n ⊗[R'] G'.A n); G.A n →ₐ[R] G'.A n ⊗[R'] G'.A n :=
  letI := via σ (G'.A n ⊗[R'] G'.A n)
  { (Algebra.TensorProduct.includeRight.toRingHom).comp ((t'.semiHom t m).app n).toRingHom with
    commutes' := fun r ↦ by
      change (1 : G'.A n) ⊗ₜ[R'] ((t'.semiHom t m).app n) (algebraMap R _ r) = _
      rw [SemiBialgHom.map_algebraMap]
      exact (Algebra.TensorProduct.algebraMap_apply' _).symm }

theorem lift_eq_two (n : ℕ) (c : G.A n ⊗[R] G.A n) :
    letI := via σ (G'.A n ⊗[R'] G'.A n)
    Algebra.TensorProduct.lift (sL σ m t t' n) (sRt σ m t t' n) (fun _ _ ↦ Commute.all _ _) c =
      ((t'.semiHom t m).app n).two c := by
  letI := via σ (G'.A n ⊗[R'] G'.A n)
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.lift_tmul]
    change ((t'.semiHom t m).app n a ⊗ₜ[R'] (1 : G'.A n)) * ((1 : G'.A n) ⊗ₜ[R'] (t'.semiHom t m).app n b) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem coc_naturality (n : ℕ) :
    letI := via σ (G'.A n); letI := via σ (G'.A n ⊗[R'] G'.A n)
    (down σ (toConv (Algebra.TensorProduct.includeLeft : G'.A n →ₐ[R'] G'.A n ⊗[R'] G'.A n) *
        toConv (Algebra.TensorProduct.includeRight : G'.A n →ₐ[R'] G'.A n ⊗[R'] G'.A n)).ofConv).comp
        (sR σ m t t' n) =
      (toConv (sL σ m t t' n) * toConv (sRt σ m t t' n)).ofConv := by
  letI := via σ (G'.A n); letI := via σ (G'.A n ⊗[R'] G'.A n)
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, down_apply, sR_apply, AlgHom.convMul_apply, AlgHom.convMul_apply,
    ← SemiBialgHom.two_comul]
  generalize Coalgebra.comul (R := R) a = c
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => rfl

private theorem coc_naturality_of_dat_algHom {c : primDR A} (d : Dat t c) (n : ℕ) {T : Type} [CommRing T] [Algebra R' T]
    (ψ : G'.A n →ₐ[R'] T) :
    letI := via σ (G'.A n); letI := via σ T
    fv (natDat (m := m) (t' := t') d).f (G'.A n) T ψ (t'.y n) + ψ ((natDat (m := m) (t' := t') d).h n) =
      fv d.f (G.A n) T ((down σ ψ).comp (sR σ m t t' n)) (t.y n) + ((down σ ψ).comp (sR σ m t t' n)) (d.h n) := by
  letI := via σ T
  letI := via σ (G'.A n)
  have hc := (GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq R A d.f).1 (G.A n) (G'.A n) T (sR σ m t t' n) (down σ ψ) (t.y n) (sm_whole _)
  have hp := fv_pull σ m d.f ψ (t'.y n)
  rw [ptsDown_y σ m t t'] at hp
  change fv (m.isMor.coef.pullbackOneCocycle d.f) (G'.A n) T ψ (t'.y n) +
    ψ ((t'.semiHom t m).app n (d.h n) + corr σ m t t' d.f n) = _
  rw [hp, hc, map_add]
  simp only [AlgHom.comp_apply, down_apply, sR_apply, corr]
  abel

private theorem coc_naturality_algHom {T : Type} [CommRing T] [Algebra R' T] (n : ℕ) (ψ : G'.A n →ₐ[R'] T) :
    letI := via σ (G'.A n); letI := via σ T
    ptsDown m T (fun _ ↦ rfl) (spOver ψ ≫ t'.y n) = spOver ((down σ ψ).comp (sR σ m t t' n)) ≫ t.y n := by
  letI := via σ T
  letI := via σ (G'.A n)
  rw [ptsDown_comp σ m ψ (t'.y n), ptsDown_y σ m t t', ← Category.assoc, ← spOver_comp]

private theorem tensorProduct_lift_includeLeft_includeRight_apply (n : ℕ) (c : G'.A n ⊗[R'] G'.A n) :
    Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : G'.A n →ₐ[R'] G'.A n ⊗[R'] G'.A n)
      (Algebra.TensorProduct.includeRight : G'.A n →ₐ[R'] G'.A n ⊗[R'] G'.A n) (fun _ _ ↦ Commute.all _ _) c = c := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem coc_naturality_tensor (n : ℕ) :
    letI := via σ (G'.A n); letI := via σ (G'.A n ⊗[R'] G'.A n)
    (down σ (Algebra.TensorProduct.includeLeft : G'.A n →ₐ[R'] G'.A n ⊗[R'] G'.A n)).comp (sR σ m t t' n) =
      sL σ m t t' n := by
  letI := via σ (G'.A n); letI := via σ (G'.A n ⊗[R'] G'.A n)
  exact AlgHom.ext fun _ ↦ rfl

private theorem coc_naturality_tensor_swap (n : ℕ) :
    letI := via σ (G'.A n); letI := via σ (G'.A n ⊗[R'] G'.A n)
    (down σ (Algebra.TensorProduct.includeRight : G'.A n →ₐ[R'] G'.A n ⊗[R'] G'.A n)).comp (sR σ m t t' n) =
      sRt σ m t t' n := by
  letI := via σ (G'.A n); letI := via σ (G'.A n ⊗[R'] G'.A n)
  exact AlgHom.ext fun _ ↦ rfl

private theorem coc_naturality_of_dat_pt {c : primDR A} (d : Dat t c) {T : Type} [CommRing T] [Algebra R' T] (x y : Pt A' T) :
    letI := via σ T
    (natDat (m := m) (t' := t') d).g T x y = d.g T (ptsDown m T (fun _ ↦ rfl) x) (ptsDown m T (fun _ ↦ rfl) y) := rfl

end GlobalTheory.PtExtNat

namespace GlobalTheory.PtExtNat

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
variable {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
  {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ}
variable {p : ℕ} {G : PDivGroup p R} {G' : PDivGroup p R'} {t : G.TorsionTower A} {t' : G'.TorsionTower A'}

theorem coc_nat {c : primDR A} (d : Dat t c) (n : ℕ) :
    ((t'.semiHom t m).app n).two (d.coc n) = (natDat (m := m) (t' := t') d).coc n := by
  letI := via σ (G'.A n); letI := via σ (G'.A n ⊗[R'] G'.A n)
  have hL := GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue R A p G t c d n (G'.A n ⊗[R'] G'.A n) (sL σ m t t' n) (sRt σ m t t' n)
  have hR := GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue R' A' p G' t' (m.pull c) (natDat (m := m) (t' := t') d) n (G'.A n ⊗[R'] G'.A n)
    Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight
  rw [lift_eq_two] at hL
  rw [tensorProduct_lift_includeLeft_includeRight_apply] at hR
  rw [hL, hR, coc_naturality_of_dat_pt, coc_naturality_algHom, coc_naturality_algHom, coc_naturality_of_dat_algHom d n, coc_naturality_of_dat_algHom d n, coc_naturality_of_dat_algHom d n,
    coc_naturality, coc_naturality_tensor, coc_naturality_tensor_swap]

end GlobalTheory.PtExtNat

namespace GlobalTheory.PtExtNat

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
variable {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
  {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ}
variable {p : ℕ} {G : PDivGroup p R} {G' : PDivGroup p R'} {t : G.TorsionTower A} {t' : G'.TorsionTower A'}

theorem om_nat {c : primDR A} (d : Dat t c) (n : ℕ) :
    ((t'.semiHom t m).app n).cot (d.om n) = (natDat (m := m) (t' := t') d).om n := by
  letI := via σ (G'.A n)
  let a : trivAt (t.y n) ⟶ m.isMor.obj (trivAt (t'.y n)) :=
    Thick.trivHom (sR σ m t t' n) (PDivGroup.TorsionTower.semiOf_y (t := t) (t' := t') m n)
  have e1 := GlobalTheory.T.crystallineCocycleCotangentValue_baseChange_natural R R' σ A A' φ m.isMor (G.A n) (G'.A n) ((t'.semiHom t m).app n) (t.y n) (t'.y n) a d.f
    (fun _ ↦ rfl)
  have e2 : ev d.f a = fv d.f (G.A n) (G'.A n) (sR σ m t t' n) (t.y n) :=
    ((GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq R A d.f).2 (G.A n) (G'.A n) (t.y n) (ptsDown m (G'.A n) (fun _ ↦ rfl) (t'.y n))
      (sR σ m t t' n) a (fun _ ↦ rfl)).2
  simp only [Dat.om, natDat, corr]
  rw [e1, e2, map_sub, SemiBialgHom.cot_d]
  simp only [dUnit, map_add]
  abel

theorem isCan_pull : ∀ (p : ℕ) (R R' : Type) [CommRing R] [CommRing R'] (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (G : PDivGroup p R) (G' : PDivGroup p R') (t : G.TorsionTower A) (t' : G'.TorsionTower A') (σ : R →+* R') (φ : A'.left ⟶ A.left) (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) (c : primDR A) (x : G.RigExt), IsCan t c x → IsCan t' (m.pull c) ((t'.semiHom t m).rig x) := by
  intro p R R' _ _ A _ A' _ G G' t t' σ φ m c x hx
  obtain ⟨d, z, w, hz, hw, rfl⟩ := hx
  refine ⟨natDat (m := m) (t' := t') d, ((t'.semiHom t m).pair (z, w)).1, ((t'.semiHom t m).pair (z, w)).2,
    fun n ↦ ?_, fun n ↦ ?_, ?_⟩
  · rw [← coc_nat, ← hz n]
    rfl
  · rw [← om_nat, ← hw n]
    rfl
  · rfl

end GlobalTheory.PtExtNat
