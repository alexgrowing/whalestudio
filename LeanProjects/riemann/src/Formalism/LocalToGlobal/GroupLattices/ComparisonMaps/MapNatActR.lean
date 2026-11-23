import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.GrowthBounds.DataG

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms MvPolynomial Matrix

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

abbrev Var : Type := Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))

abbrev XR (R : Type) [CommRing R] : Type := MvPolynomial (Var P) R

def eAt (v : Fin P.nV) (s : Fin (P.n' v)) : ℤ := lamAt (P.lam0 v) s (Fin.last P.m)

def substR (R : Type) [CommRing R] (G : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R) :
    XR P R →ₐ[R] XR P R :=
  aeval fun x => ∑ b : Fin (P.m + 1), C (G x.1 x.2.1 x.2.2.1 b) * X ⟨x.1, (x.2.1, (b, x.2.2.2))⟩

def natActR (R : Type) [Field R] (g : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) R) : XR P R →ₗ[R] XR P R :=
  (∏ v, ∏ s : Fin (P.n' v), (g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R).det ^ (-(eAt P v s))) •
    (substR P R fun v s => ((g v s)⁻¹ : GL (Fin (P.m + 1)) R)).toLinearMap

def gPosGL (v : Fin P.nV) (s : Fin (P.n' v)) : GL (Fin (P.m + 1)) (P.Qq v) →* GL (Fin (P.m + 1)) Kf :=
  Matrix.GeneralLinearGroup.map ((P.ι v).comp ((P.σ v ^ s.val : P.Qq v ≃+* P.Qq v) : P.Qq v →+* P.Qq v))

theorem natAct_eq (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) :
    P.natAct A = natActR P Kf (fun v s => gPosGL P v s (A v)) := by
  rfl

section Map

variable {R S : Type}

theorem map_substR [CommRing R] [CommRing S] (f : R →+* S)
    (G : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R) (Q : XR P R) :
    MvPolynomial.map f (substR P R G Q) = substR P S (fun v s => (G v s).map f) (MvPolynomial.map f Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [substR]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [substR, map_sum, Matrix.map_apply]

theorem map_natActR [Field R] [Field S] (f : R →+* S) (g : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) R) (Q : XR P R) :
    MvPolynomial.map f (natActR P R g Q) =
      natActR P S (fun v s => Matrix.GeneralLinearGroup.map f (g v s)) (MvPolynomial.map f Q) := by
  simp only [natActR, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_substR]
  congr 2
  · simp only [map_prod, map_zpow₀, RingHom.map_det]
    rfl

end Map

variable {Tau : Type} [Fintype Tau] {n : ℕ}

def reM (h : P.m + 1 = n) (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ :=
  A.submatrix (finCongr h) (finCongr h)

theorem reM_mul (h : P.m + 1 = n) (A B : Matrix (Fin n) (Fin n) ℂ) : reM P h (A * B) = reM P h A * reM P h B := by
  unfold reM
  exact (Matrix.submatrix_mul_equiv A B (finCongr h) (finCongr h) (finCongr h)).symm

theorem reM_one (h : P.m + 1 = n) : reM P h (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold reM
  exact Matrix.submatrix_one_equiv _

def reG (h : P.m + 1 = n) : GL (Fin n) ℂ →* GL (Fin (P.m + 1)) ℂ :=
  Units.map
    { toFun := reM P h
      map_one' := reM_one P h
      map_mul' := reM_mul P h }

def zAt (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (M y : Tau → Matrix (Fin n) (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ :=
  if Even s.val then reM P h (M (pos ⟨v, s⟩) * y (pos ⟨v, s⟩))
  else ((reM P h (M (pos ⟨v, s⟩) * y (pos ⟨v, s⟩)))⁻¹)ᵀ.submatrix id Fin.rev

def evC (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) : XR P ℂ →ₗ[ℂ] (Frames G → ℂ) where
  toFun Q := fun y => (∏ v, ∏ s : Fin (P.n' v), (zAt P h pos M y.1 v s).det ^ (eAt P v s)) *
    MvPolynomial.eval (fun x : Var P => zAt P h pos M y.1 x.1 x.2.1 x.2.2.1 x.2.2.2) Q
  map_add' Q Q' := by funext y; simp [mul_add]
  map_smul' c Q := by funext y; simp [MvPolynomial.smul_eval]; ring

def invT {k : Type} [Fintype k] [DecidableEq k] (X : GL k ℂ) : GL k ℂ :=
  ⟨((X⁻¹ : GL k ℂ) : Matrix k k ℂ)ᵀ, (X : Matrix k k ℂ)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel]; simp,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]; simp⟩

def hAt (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (M g : Tau → GL (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) : GL (Fin (P.m + 1)) ℂ :=
  if Even s.val then reG P h (M (pos ⟨v, s⟩) * g (pos ⟨v, s⟩) * (M (pos ⟨v, s⟩))⁻¹)
  else invT (reG P h (M (pos ⟨v, s⟩) * g (pos ⟨v, s⟩) * (M (pos ⟨v, s⟩))⁻¹))

theorem zAt_tr (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (M g : Tau → GL (Fin n) ℂ)
    (y y' : Tau → Matrix (Fin n) (Fin n) ℂ) (hy : ∀ τ, y' τ = (g τ : Matrix (Fin n) (Fin n) ℂ) * y τ)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    zAt P h pos (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) y' v s =
      (hAt P h pos M g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) *
        zAt P h pos (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) y v s := by
  have key : reM P h ((M (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ) * y' (pos ⟨v, s⟩)) =
      (reG P h (M (pos ⟨v, s⟩) * g (pos ⟨v, s⟩) * (M (pos ⟨v, s⟩))⁻¹) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) *
        reM P h ((M (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ) * y (pos ⟨v, s⟩)) := by
    show _ = reM P h _ * _
    rw [← reM_mul, hy]
    congr 1
    simp [Matrix.mul_assoc]
  unfold zAt hAt
  split_ifs with hs
  · exact key
  · rw [key]
    show _ = (((reG P h (M (pos ⟨v, s⟩) * g (pos ⟨v, s⟩) * (M (pos ⟨v, s⟩))⁻¹))⁻¹ : GL (Fin (P.m + 1)) ℂ) :
      Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)ᵀ * _
    rw [Matrix.coe_units_inv, Matrix.mul_inv_rev, Matrix.transpose_mul]
    ext i j
    simp [Matrix.mul_apply]

theorem evC_natAct (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M g : Tau → GL (Fin n) ℂ) (y y' : Frames G) (hy : IsTr (fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ)) y y') (Q : XR P ℂ) :
    evC P h pos G (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) (natActR P ℂ (hAt P h pos M g) Q) y' =
      evC P h pos G (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) Q y := by
  have hz' : ∀ v s, zAt P h pos (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) y'.1 v s = (hAt P h pos M g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) * zAt P h pos (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) y.1 v s :=
    fun v s => zAt_tr P h pos M g y.1 y'.1 hy v s
  have hz : ∀ v s, ((((hAt P h pos M g v s)⁻¹ : GL (Fin (P.m + 1)) ℂ)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) * zAt P h pos (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) y'.1 v s = zAt P h pos (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) y.1 v s := by
    intro v s
    rw [hz', ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hev : ∀ Q : XR P ℂ,
      MvPolynomial.eval (fun x : Var P => zAt P h pos (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) y'.1 x.1 x.2.1 x.2.2.1 x.2.2.2)
        (substR P ℂ (fun v s => ((((hAt P h pos M g v s)⁻¹ : GL (Fin (P.m + 1)) ℂ)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) Q) =
      MvPolynomial.eval (fun x : Var P => zAt P h pos (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) y.1 x.1 x.2.1 x.2.2.1 x.2.2.2) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a => simp [substR]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p x hp =>
      rw [map_mul, map_mul, map_mul, hp]
      congr 1
      simp only [substR, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [← hz x.1 x.2.1, Matrix.mul_apply]
  have hdet : ∀ v s, (hAt P h pos M g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det ≠ 0 := fun v s =>
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
  have hc : (∏ v, ∏ s : Fin (P.n' v), (hAt P h pos M g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det ^ (-(eAt P v s))) *
      (∏ v, ∏ s : Fin (P.n' v), (hAt P h pos M g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det ^ (eAt P v s)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun s _ => ?_
    rw [_root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hdet v s))]
  have hnat : natActR P ℂ (hAt P h pos M g) Q = (∏ v, ∏ s : Fin (P.n' v), (hAt P h pos M g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det ^ (-(eAt P v s))) •
      substR P ℂ (fun v s => ((((hAt P h pos M g v s)⁻¹ : GL (Fin (P.m + 1)) ℂ)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) Q := rfl
  rw [hnat, map_smul, Pi.smul_apply, smul_eq_mul]
  simp only [evC, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hev]
  simp only [hz', Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  rw [← mul_assoc, ← mul_assoc, hc, one_mul]

def VtupR (R : Type) [Field R] : Submodule R (XR P R) :=
  Submodule.span R {Z | ∃ F : ∀ v, MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) R,
    (∀ v, F v ∈ Vsp R (P.lam0 v)) ∧ Z = ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (F v)}

theorem VtupR_Kf : VtupR P Kf = P.Vtup := rfl

def WtTie (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (lam : Tau → Formalism.BasicNotions.DomWeight n) : Prop :=
  ∀ v (s : Fin (P.n' v)) (i : Fin (P.m + 1)), P.lam0 v s i = (lam (pos ⟨v, s⟩)).w (finCongr h i)

def EvValC (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → GL (Fin n) ℂ) (lam : Tau → Formalism.BasicNotions.DomWeight n) : Prop :=
  WtTie P h pos lam → (VtupR P ℂ).map (evC P h pos G (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ))) = ValC G lam

end Formalism.L2.G.Cmp

end
