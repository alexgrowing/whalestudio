import Mathlib

noncomputable section

open MvPolynomial NumberField
open scoped Matrix

namespace UpperTheory.V.Z.Sym.Wt

def hq {R : Type} [CommRing R] (t n : R) : ℕ → R
  | 0 => 1
  | 1 => t
  | j + 2 => t * hq t n (j + 1) - n * hq t n j

def invT (R : Type) [CommRing R] (d : ℕ) : GL (Fin d) R →* GL (Fin d) R where
  toFun g := ⟨((g⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R)ᵀ, (g : Matrix (Fin d) (Fin d) R)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp only [Units.val_mul, mul_inv_rev, Matrix.transpose_mul])

theorem invT_val {R : Type} [CommRing R] {d : ℕ} (g : GL (Fin d) R) :
    (invT R d g : Matrix (Fin d) (Fin d) R) = ((g⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R)ᵀ := rfl

theorem invT_invT {R : Type} [CommRing R] {d : ℕ} (g : GL (Fin d) R) : invT R d (invT R d g) = g :=
  Units.ext (Matrix.transpose_transpose _)

section Blocks

variable {K : Type} {d : ℕ}

def act (g : K → GL (Fin d) ℂ) (x : K × Fin d → ℂ) : K × Fin d → ℂ :=
  fun p => ∑ j, x (p.1, j) * (g p.1 : Matrix (Fin d) (Fin d) ℂ) j p.2

def sbs (g : K → GL (Fin d) ℂ) : MvPolynomial (K × Fin d) ℂ →ₐ[ℂ] MvPolynomial (K × Fin d) ℂ :=
  aeval fun p => ∑ j, X (p.1, j) * C ((g p.1 : Matrix (Fin d) (Fin d) ℂ) j p.2)

theorem eval_sbs (g : K → GL (Fin d) ℂ) (x : K × Fin d → ℂ) (P : MvPolynomial (K × Fin d) ℂ) :
    eval x (sbs g P) = eval (act g x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sbs]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [sbs, act]

theorem act_one (x : K × Fin d → ℂ) : act 1 x = x := by
  funext p; obtain ⟨v, i⟩ := p; simp [act, Matrix.one_apply]

theorem act_mul (g h : K → GL (Fin d) ℂ) (x : K × Fin d → ℂ) : act (g * h) x = act h (act g x) := by
  funext p
  simp only [act, Pi.mul_apply, Units.val_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

variable [Fintype K]

variable (d) in

def MH (n : K → ℕ) : Submodule ℂ (MvPolynomial (K × Fin d) ℂ) where
  carrier := {P | ∀ (s : K → ℂ) (x : K × Fin d → ℂ), eval (fun p => s p.1 * x p) P = (∏ v, s v ^ n v) * eval x P}
  add_mem' h h' s x := by rw [map_add, map_add, h, h', mul_add]
  zero_mem' s x := by simp
  smul_mem' c P h s x := by rw [smul_eval, smul_eval, h]; ring

theorem sbs_mem {n : K → ℕ} (g : K → GL (Fin d) ℂ) {P : MvPolynomial (K × Fin d) ℂ} (h : P ∈ MH d n) : sbs g P ∈ MH d n := by
  intro s x
  rw [eval_sbs, eval_sbs, ← h]
  congr 2
  funext p
  simp [act, Finset.mul_sum, mul_assoc]

variable (d) in

def mRep (n : K → ℕ) : Representation ℂ (K → GL (Fin d) ℂ) (MH d n) where
  toFun g := (sbs g).toLinearMap.restrict fun _ h => sbs_mem g h
  map_one' := by
    refine LinearMap.ext fun P => Subtype.ext (MvPolynomial.funext fun x => ?_)
    change eval x (sbs 1 P.1) = eval x P.1
    rw [eval_sbs, act_one]
  map_mul' g h := by
    refine LinearMap.ext fun P => Subtype.ext (MvPolynomial.funext fun x => ?_)
    change eval x (sbs (g * h) P.1) = eval x (sbs g (sbs h P.1))
    rw [eval_sbs, eval_sbs, eval_sbs, act_mul]

theorem eval_mRep (n : K → ℕ) (g : K → GL (Fin d) ℂ) (P : MH d n) (x : K × Fin d → ℂ) :
    eval x (mRep d n g P).1 = eval (act g x) P.1 := eval_sbs g x P.1

end Blocks

section Bi

variable {I : Type} {d : ℕ}

variable (d) in

def dbl : (I → GL (Fin d) ℂ) →* (I × Bool → GL (Fin d) ℂ) where
  toFun g k := if k.2 then invT ℂ d (g k.1) else g k.1
  map_one' := by funext k; by_cases h : k.2 <;> simp [h]
  map_mul' g h := by funext k; by_cases hk : k.2 <;> simp [hk]

variable (I d) in

def flip (p : (I × Bool) × Fin d) : (I × Bool) × Fin d := ((p.1.1, !p.1.2), p.2)

variable [Fintype I]

variable (d) in

abbrev Bi (n : I → ℕ) : Submodule ℂ (MvPolynomial ((I × Bool) × Fin d) ℂ) := MH d fun k : I × Bool => n k.1

variable (d) in

def biRep (n : I → ℕ) : Representation ℂ (I → GL (Fin d) ℂ) (Bi d n) := (mRep d _).comp (dbl d)

theorem flip_mem {n : I → ℕ} {P : MvPolynomial ((I × Bool) × Fin d) ℂ} (h : P ∈ Bi d n) : rename (flip I d) P ∈ Bi d n := by
  intro s x
  rw [eval_rename, eval_rename]
  have := h (fun k => s (k.1, !k.2)) (x ∘ flip I d)
  refine this.trans ?_
  congr 1
  simp [Fintype.prod_prod_type, mul_comm]

variable (d) in

def swp (n : I → ℕ) : Module.End ℂ (Bi d n) := (rename (flip I d)).toLinearMap.restrict fun _ h => flip_mem h

def dg (j : ℕ) (S : I → Bool) (v : I) : ℕ := if S v then j - 1 else j

def sg (S : I → Bool) : ℂ := ∏ v, if S v then -1 else 1

variable (I) in

abbrev VG (j : ℕ) : Type := ∀ S : I → Bool, Bi 3 (dg j S)

variable (I) in

def repG (j : ℕ) : Representation ℂ (I → GL (Fin 3) ℂ) (VG I j) where
  toFun g := LinearMap.pi fun S => (biRep 3 (dg j S) g).comp (LinearMap.proj S)
  map_one' := by refine LinearMap.ext fun P => funext fun S => ?_; simp
  map_mul' g h := by refine LinearMap.ext fun P => funext fun S => ?_; simp

variable (I) in

def thG (j : ℕ) : Module.End ℂ (VG I j) := LinearMap.pi fun S => (sg S • swp 3 (dg j S)).comp (LinearMap.proj S)

theorem repG_apply (j : ℕ) (g : I → GL (Fin 3) ℂ) (P : VG I j) (S : I → Bool) : repG I j g P S = biRep 3 (dg j S) g (P S) := rfl

theorem thG_apply (j : ℕ) (P : VG I j) (S : I → Bool) : thG I j P S = sg S • swp 3 (dg j S) (P S) := rfl

end Bi

def infG {R I : Type} [CommRing R] (em : I → R →+* ℂ) (n : ℕ) : GL (Fin n) R →* (I → GL (Fin n) ℂ) :=
  Pi.monoidHom fun w => Matrix.GeneralLinearGroup.map (em w)

def WG {R I : Type} [CommRing R] [Fintype I] (em : I → R →+* ℂ) (j : ℕ) : Representation ℂ (GL (Fin 3) R) (VG I j) :=
  (repG I j).comp (infG em 3)

def detE {I : Type} [Fintype I] (d : ℕ) (e : ℤ) : (I → GL (Fin d) ℂ) →* ℂˣ where
  toFun g := ∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e
  map_one' := by simp
  map_mul' g h := by simp [mul_zpow, Finset.prod_mul_distrib]

abbrev VD (I : Type) [Fintype I] (n : ℕ) : Submodule ℂ (MvPolynomial (I × Fin 2) ℂ) := MH 2 fun _ : I => n

def repD (I : Type) [Fintype I] (n : ℕ) (e : ℤ) : Representation ℂ (I → GL (Fin 2) ℂ) (VD I n) where
  toFun g := (detE 2 e g : ℂ) • mRep 2 _ g
  map_one' := by simp
  map_mul' g h := by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

theorem repD_apply (I : Type) [Fintype I] (n : ℕ) (e : ℤ) (g : I → GL (Fin 2) ℂ) :
    repD I n e g = (detE 2 e g : ℂ) • mRep 2 _ g := rfl

def WD {R I : Type} [CommRing R] [Fintype I] (em : I → R →+* ℂ) (n : ℕ) (e : ℤ) : Representation ℂ (GL (Fin 2) R) (VD I n) :=
  (repD I n e).comp (infG em 2)

def chi {R I : Type} [CommRing R] [Fintype I] (em : I → R →+* ℂ) (j : ℕ) (τ : R) : ℂ := ∏ w, hq (em w τ) 1 j

example : (1 : MvPolynomial (Unit × Fin 2) ℂ) ∈ MH 2 (fun _ : Unit => 0) := fun s x => by simp

end UpperTheory.V.Z.Sym.Wt

end
