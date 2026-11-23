import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix NNReal

namespace UpperTheory.V.Sd.Wc

def nu {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) : Valuation ℂ ℝ≥0 :=
  (NormedField.valuation (K := Qbar l)).comap ι.symm.toRingHom

theorem nu_apply {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (x : ℂ) : nu ι x = ‖ι.symm x‖₊ := rfl

def IsPos {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, B y x = starRingEnd ℂ (B x y)) ∧ ∀ x, x ≠ 0 → 0 < (B x x).re

section Weight

open MvPolynomial

variable {I : Type} [Fintype I]

def act (g : I → GL (Fin 2) ℂ) (x : I × Fin 2 → ℂ) : I × Fin 2 → ℂ :=
  fun p => ∑ j, x (p.1, j) * (g p.1 : Matrix (Fin 2) (Fin 2) ℂ) j p.2

def sbs (g : I → GL (Fin 2) ℂ) : MvPolynomial (I × Fin 2) ℂ →ₐ[ℂ] MvPolynomial (I × Fin 2) ℂ :=
  aeval fun p => ∑ j, X (p.1, j) * C ((g p.1 : Matrix (Fin 2) (Fin 2) ℂ) j p.2)

omit [Fintype I] in
theorem eval_sbs (g : I → GL (Fin 2) ℂ) (x : I × Fin 2 → ℂ) (P : MvPolynomial (I × Fin 2) ℂ) :
    eval x (sbs g P) = eval (act g x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sbs]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [sbs, act]

omit [Fintype I] in
theorem act_one (x : I × Fin 2 → ℂ) : act 1 x = x := by
  funext p; obtain ⟨v, i⟩ := p; fin_cases i <;> simp [act]

omit [Fintype I] in
theorem act_mul (g h : I → GL (Fin 2) ℂ) (x : I × Fin 2 → ℂ) : act (g * h) x = act h (act g x) := by
  funext p; simp [act, Matrix.mul_apply, Fin.sum_univ_two]; ring

def Wt (n : I → ℕ) : Submodule ℂ (MvPolynomial (I × Fin 2) ℂ) where
  carrier := {P | ∀ (s : I → ℂ) (x : I × Fin 2 → ℂ), eval (fun p => s p.1 * x p) P = (∏ v, s v ^ n v) * eval x P}
  add_mem' h h' s x := by rw [map_add, map_add, h, h', mul_add]
  zero_mem' s x := by simp
  smul_mem' c P h s x := by rw [smul_eval, smul_eval, h]; ring

def detE (e : I → ℤ) : (I → GL (Fin 2) ℂ) →* ℂˣ where
  toFun g := ∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e v
  map_one' := by simp
  map_mul' g h := by simp [mul_zpow, Finset.prod_mul_distrib]

theorem sbs_mem {n : I → ℕ} (g : I → GL (Fin 2) ℂ) {P : MvPolynomial (I × Fin 2) ℂ} (h : P ∈ Wt n) : sbs g P ∈ Wt n := by
  intro s x
  rw [eval_sbs, eval_sbs, ← h]
  congr 2
  funext p
  simp [act, mul_add, mul_assoc]

def wRep (n : I → ℕ) (e : I → ℤ) : Representation ℂ (I → GL (Fin 2) ℂ) (Wt n) where
  toFun g := (detE e g : ℂ) • (sbs g).toLinearMap.restrict fun _ h => sbs_mem g h
  map_one' := by
    refine LinearMap.ext fun P => Subtype.ext (MvPolynomial.funext fun x => ?_)
    change eval x ((detE e 1 : ℂ) • sbs 1 P.1) = eval x P.1
    rw [smul_eval, eval_sbs, act_one, map_one, Units.val_one, one_mul]
  map_mul' g h := by
    refine LinearMap.ext fun P => Subtype.ext (MvPolynomial.funext fun x => ?_)
    change eval x ((detE e (g * h) : ℂ) • sbs (g * h) P.1) = eval x ((detE e g : ℂ) • sbs g ((detE e h : ℂ) • sbs h P.1))
    rw [smul_eval, smul_eval, eval_sbs, eval_sbs, smul_eval, eval_sbs, act_mul, map_mul, Units.val_mul, mul_assoc]

theorem eval_wRep (n : I → ℕ) (e : I → ℤ) (g : I → GL (Fin 2) ℂ) (P : Wt n) (x : I × Fin 2 → ℂ) :
    eval x (wRep n e g P).1 = (detE e g : ℂ) * eval (act g x) P.1 := by
  change eval x ((detE e g : ℂ) • sbs g P.1) = _
  rw [smul_eval, eval_sbs]

def rowE (I : Type) : I × Fin 2 → ℂ := fun p => ![0, 1] p.2

def tc (n : I → ℕ) : Wt n →ₗ[ℂ] ℂ := (aeval (rowE I)).toLinearMap.comp (Wt n).subtype

theorem tc_apply (n : I → ℕ) (P : Wt n) : tc n P = eval (rowE I) P.1 := rfl

def eY (n : I → ℕ) : Wt n := ⟨∏ v, X (v, 1) ^ n v, fun s x => by simp [mul_pow, Finset.prod_mul_distrib]⟩

end Weight

section Abs

variable {Γ G W : Type} [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W]

def AF (j : Γ →* G) (R : Representation ℂ G W) : Submodule ℂ (G → W) where
  carrier := {f | ∀ γ g, f (j γ * g) = R (j γ) (f g)}
  add_mem' h h' γ g := by simp [h γ g, h' γ g]
  zero_mem' γ g := by simp
  smul_mem' c f h γ g := by simp [h γ g]

def psi (R : Representation ℂ G W) (t : W →ₗ[ℂ] ℂ) : (G → W) →ₗ[ℂ] (G → ℂ) where
  toFun f g := t (R g⁻¹ (f g))
  map_add' f f' := by funext g; simp
  map_smul' c f := by funext g; simp

theorem psi_apply (R : Representation ℂ G W) (t : W →ₗ[ℂ] ℂ) (f : G → W) (g : G) : psi R t f g = t (R g⁻¹ (f g)) := rfl

def stab (j : Γ →* G) (H : Subgroup G) (g : G) : Subgroup Γ := H.comap ((MulAut.conj g⁻¹).toMonoidHom.comp j)

theorem mem_stab {j : Γ →* G} {H : Subgroup G} {g : G} {γ : Γ} : γ ∈ stab j H g ↔ g⁻¹ * j γ * g ∈ H := by
  simp [stab]

end Abs

variable (F : Type) [Field F] [NumberField F]

abbrev GF : Type := GL (Fin 2) (Af F)

def zc : (Af F)ˣ →* GF F := Matrix.GeneralLinearGroup.scalar (Fin 2)

def ratU : Fˣ →* (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom

variable {F}

def Kc (c : Pl F → ℕ) : Subgroup (GF F) := ⨅ w, (K1 w (c w)).comap (Matrix.GeneralLinearGroup.map (pLoc F w))

def Hc (c : Pl F → ℕ) : Subgroup (GF F) := Kc c ⊔ (zc F).range

section Sp

variable {W : Type} [AddCommGroup W] [Module ℂ W]

variable (W) in

def Cen (ω : (Af F)ˣ →* ℂˣ) : Submodule ℂ (GF F → W) where
  carrier := {f | ∀ z g, f (g * zc F z) = (ω z : ℂ) • f g}
  add_mem' h h' z g := by simp [h z g, h' z g]
  zero_mem' z g := by simp
  smul_mem' c f h z g := by simp only [Pi.smul_apply, h z g]; exact smul_comm _ _ _

def Sp (Q : DefQuat F) (R : Representation ℂ (GF F) W) (c : Pl F → ℕ) (ω : (Af F)ˣ →* ℂˣ) : Submodule ℂ (GF F → W) :=
  AF Q.toFin R ⊓ Hi.fixd (Hi.rtr ℂ (GF F) W) (Kc c) ⊓ Cen W ω

variable (W) in

def Hk (w : Pl F) (c : ℕ) : Module.End ℂ (GF F → W) := Uop w ((Hi.rtr ℂ (GF F) W).comp (locGL F 2 w)) c

end Sp

structure CC (c : Pl F → ℕ) (ω : (Af F)ˣ →* ℂˣ) (k : ℤ) : Prop where
  lev : ∀ z, zc F z ∈ Kc c → ω z = 1
  rat : ∀ x : Fˣ, (ω (ratU F x) : ℂ) = ∏ v : InfinitePlace F, v.embedding (x : F) ^ k

variable (F) in

structure LDat {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) where

  pl : InfinitePlace F → Pl F

  em : ∀ v, (pl v).adicCompletion F →+* ℂ
  em_alg : ∀ v (x : F), em v (algebraMap F _ x) = v.embedding x
  le : ∀ v x, nu ι (em v x) ≤ 1 ↔ Valued.v x ≤ 1
  lt : ∀ v x, nu ι (em v x) < 1 ↔ Valued.v x < 1
  res : ∀ v x, Valued.v x = 1 → nu ι (em v x ^ (l - 1) - 1) < 1
  mem : ∀ v, ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal
  inj : Function.Injective pl
  surj : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ v, pl v = w
  norm : ∀ v, normV (pl v) = l
  unif : ∀ v, Valued.v ((l : ℕ) : (pl v).adicCompletion F) = WithZero.exp (-1 : ℤ)
  embAt : ∀ (τ : F →+* Qbar l) (w : Pl F), EmbAt w τ ↔ pl (InfinitePlace.mk (ι.toRingHom.comp τ)) = w

namespace LDat

variable {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι)

def ea (v : InfinitePlace F) : Af F →+* ℂ := (D.em v).comp (pLoc F (D.pl v))

def gl : GF F →* (InfinitePlace F → GL (Fin 2) ℂ) := Pi.monoidHom fun v => Matrix.GeneralLinearGroup.map (D.ea v)

def R (n : InfinitePlace F → ℕ) (e : InfinitePlace F → ℤ) : Representation ℂ (GF F) (Wt n) := (wRep n e).comp D.gl

def Cmp (Q : DefQuat F) : Prop := ∀ v y, Q.jc v y = (Q.jf y).map (D.ea v)

open Classical in

def nz (e : InfinitePlace F → ℤ) (w : Pl F) : ℂ := ∏ v, if D.pl v = w then (l : ℂ) ^ (-e v) else 1

open Classical in

def uf (e : InfinitePlace F → ℤ) (w : Pl F) : ℂ :=
  ∏ v, if D.pl v = w then (v.embedding (Formalism.L2.Host.unif w : Fˣ) / (l : ℂ)) ^ e v else 1

def resplit (Q : DefQuat F) : DefQuat F :=
  { Q with
    jc := fun v => (D.ea v).mapMatrix.comp Q.jf.toRingHom
    jc_alg := fun v x => by
      have h : D.ea v (algebraMap F (Af F) x) = v.embedding x := D.em_alg v x
      ext i j
      simp [Matrix.algebraMap_matrix_apply, apply_ite (D.ea v), h] }

theorem cmp_resplit (Q : DefQuat F) : D.Cmp (D.resplit Q) := fun _ _ => rfl

theorem Cmp.toInf {D : LDat F ι} {Q : DefQuat F} (h : D.Cmp Q) (γ : Q.Dˣ) : Q.toInf γ = D.gl (Q.toFin γ) :=
  funext fun v => Units.ext (h v γ)

end LDat

end UpperTheory.V.Sd.Wc
