import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.InfCharG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.QuasiDeterminantConjInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.AdjointEquivalence
import Formalism.FormalDegreeBessel.FinalIO

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.CapCoef

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

theorem jm_sq : Jm ε * Jm ε = 1 := by
  unfold Jm; rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one; split_ifs <;> simp

section Transp

variable {P Q : Matrix (Fin n) (Fin n) ℂ}

theorem hinv (hQP : Q * P = 1) (hPQ : P * Q = 1) : (Pᴴ * Jm ε * P)⁻¹ = Q * Jm ε * Qᴴ := by
  apply Matrix.inv_eq_left_inv
  have h1 : Qᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
  calc Q * Jm ε * Qᴴ * (Pᴴ * Jm ε * P) = Q * (Jm ε * ((Qᴴ * Pᴴ) * (Jm ε * P))) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.one_mul, ← Matrix.mul_assoc (Jm ε), jm_sq, Matrix.one_mul, hQP]

theorem conj_star (hQP : Q * P = 1) (hPQ : P * Q = 1) (Z : Matrix (Fin n) (Fin n) ℂ) :
    P * ((Pᴴ * Jm ε * P)⁻¹ * Zᴴ * (Pᴴ * Jm ε * P)) * Q = Jm ε * (P * Z * Q)ᴴ * Jm ε := by
  rw [hinv hQP hPQ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P Q, hPQ, Matrix.one_mul]
  simp only [hPQ, Matrix.mul_one]

theorem conj_hpart1 (hQP : Q * P = 1) (hPQ : P * Q = 1) (Z : Matrix (Fin n) (Fin n) ℂ) :
    P * Formalism.QuantumDeterminants.hpart1 (Pᴴ * Jm ε * P) Z * Q = S7.cpart1 ε (P * Z * Q) := by
  unfold Formalism.QuantumDeterminants.hpart1 S7.cpart1
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, conj_star hQP hPQ]

theorem conj_hpart2 (hQP : Q * P = 1) (hPQ : P * Q = 1) (Z : Matrix (Fin n) (Fin n) ℂ) :
    P * Formalism.QuantumDeterminants.hpart2 (Pᴴ * Jm ε * P) Z * Q = S7.cpart2 ε (P * Z * Q) := by
  unfold Formalism.QuantumDeterminants.hpart2 S7.cpart2
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, conj_star hQP hPQ]

theorem conj_UJ (hQP : Q * P = 1) (hPQ : P * Q = 1) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ * (Pᴴ * Jm ε * P) * g = Pᴴ * Jm ε * P) : inUJ ε (P * g * Q) := by
  show (P * g * Q)ᴴ * Jm ε * (P * g * Q) = Jm ε
  have h1 : Qᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
  calc (P * g * Q)ᴴ * Jm ε * (P * g * Q) = Qᴴ * ((gᴴ * (Pᴴ * Jm ε * P) * g) * Q) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Qᴴ * Pᴴ) * Jm ε * (P * Q) := by rw [hg]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, hPQ, Matrix.one_mul, Matrix.mul_one]

theorem unconj_UH (hQP : Q * P = 1) (hPQ : P * Q = 1) {M : Matrix (Fin n) (Fin n) ℂ} (hM : inUJ ε M) :
    (Q * M * P)ᴴ * (Pᴴ * Jm ε * P) * (Q * M * P) = Pᴴ * Jm ε * P := by
  have hM' : Mᴴ * Jm ε * M = Jm ε := hM
  have h1 : Qᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
  calc (Q * M * P)ᴴ * (Pᴴ * Jm ε * P) * (Q * M * P)
      = Pᴴ * (Mᴴ * ((Qᴴ * Pᴴ) * (Jm ε * ((P * Q) * (M * P))))) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * ((Mᴴ * Jm ε * M) * P) := by rw [h1, hPQ]; simp only [Matrix.one_mul, Matrix.mul_assoc]
    _ = Pᴴ * Jm ε * P := by rw [hM', Matrix.mul_assoc]

theorem exp_conj' (hQP : Q * P = 1) (hPQ : P * Q = 1) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    P * NormedSpace.exp ((t : ℂ) • X) * Q = NormedSpace.exp ((t : ℂ) • (P * X * Q)) := by
  have hinvP : P⁻¹ = Q := Matrix.inv_eq_right_inv hPQ
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr (Matrix.isUnit_det_of_right_inverse hPQ)
  have h := Matrix.exp_conj P ((t : ℂ) • X) hu
  rw [hinvP] at h
  rw [show (t : ℂ) • (P * X * Q) = P * ((t : ℂ) • X) * Q by rw [Matrix.mul_smul, Matrix.smul_mul], h]

end Transp

section Coef

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {P Q : Matrix (Fin n) (Fin n) ℂ}

theorem exp_eq_unconj (hQP : Q * P = 1) (hPQ : P * Q = 1) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) = Q * NormedSpace.exp ((t : ℂ) • (P * X * Q)) * P := by
  rw [← exp_conj' hQP hPQ X t]
  simp only [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  rw [Matrix.mul_assoc, hQP, Matrix.mul_one]

theorem exp_mem_Hm (hQP : Q * P = 1) (hPQ : P * Q = 1) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε (P * X * Q))
    (t : ℝ) : (NormedSpace.exp ((t : ℂ) • X))ᴴ * (Pᴴ * Jm ε * P) * NormedSpace.exp ((t : ℂ) • X) =
      Pᴴ * Jm ε * P := by
  rw [exp_eq_unconj hQP hPQ X t]
  exact unconj_UH hQP hPQ (PI.UnitaryGroupMassFormula.DSIC.exp_mem_UJ hX t)

theorem mul_mem_Hm {g h : Matrix (Fin n) (Fin n) ℂ} {Hm : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * Hm * g = Hm)
    (hh : hᴴ * Hm * h = Hm) : (g * h)ᴴ * Hm * (g * h) = Hm := by
  calc (g * h)ᴴ * Hm * (g * h) = hᴴ * (gᴴ * Hm * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hm := by rw [hg, hh]

theorem rdv_cf (hσ : IsURepOn (UJset ε) σ) (hQP : Q * P = 1) (hPQ : P * Q = 1) (a : H) (T : E)
    (x : smD ε σ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : ∀ h, hᴴ * (Pᴴ * Jm ε * P) * h = Pᴴ * Jm ε * P → f h = (inner ℂ a (σ (P * h * Q) x)) • T)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε (P * X * Q)) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ * (Pᴴ * Jm ε * P) * g = Pᴴ * Jm ε * P) :
    Formalism.REAL.RdV X f g = (inner ℂ a (σ (P * g * Q) ((actM (smE ε σ) (P * X * Q) x : smD ε σ) : H))) • T := by
  unfold Formalism.REAL.RdV
  have hpath : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) = fun t : ℝ =>
      (inner ℂ a (σ (P * g * Q) (σ (NormedSpace.exp ((t : ℂ) • (P * X * Q))) (x : H)))) • T := by
    funext t
    rw [hf _ (mul_mem_Hm hg (exp_mem_Hm hQP hPQ hX t))]
    congr 2
    have e : P * (g * NormedSpace.exp ((t : ℂ) • X)) * Q = (P * g * Q) * (P * NormedSpace.exp ((t : ℂ) • X) * Q) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
    rw [e, exp_conj' hQP hPQ X t, hσ.1.2 _ (conj_UJ hQP hPQ hg) _ (PI.UnitaryGroupMassFormula.DSIC.exp_mem_UJ hX t)]
    rfl
  rw [hpath]
  have hd := (isDerivedOn_smE hσ).deriv _ hX x
  have hd1 : HasDerivAt (fun t : ℝ => inner ℂ a (σ (P * g * Q) (σ (NormedSpace.exp ((t : ℂ) • (P * X * Q))) (x : H))))
      (inner ℂ a (σ (P * g * Q) ((actM (smE ε σ) (P * X * Q) x : smD ε σ) : H))) 0 := by
    have := (((innerSL ℂ a).comp (σ (P * g * Q))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    convert this using 1 <;> first | (ext t; simp) | simp
  exact (hd1.smul_const T).deriv

theorem eabH_cf (hσ : IsURepOn (UJset ε) σ) (hQP : Q * P = 1) (hPQ : P * Q = 1) (a : H) (T : E)
    (x : smD ε σ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : ∀ h, hᴴ * (Pᴴ * Jm ε * P) * h = Pᴴ * Jm ε * P → f h = (inner ℂ a (σ (P * h * Q) x)) • T)
    (c d : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * (Pᴴ * Jm ε * P) * g = Pᴴ * Jm ε * P) :
    Formalism.QuantumDeterminants.EabH (Pᴴ * Jm ε * P) c d f g =
      (inner ℂ a (σ (P * g * Q) ((actM (smE ε σ) (P * Matrix.single c d 1 * Q) x : smD ε σ) : H))) • T := by
  unfold Formalism.QuantumDeterminants.EabH
  have h1 : inG ε (P * Formalism.QuantumDeterminants.hpart1 (Pᴴ * Jm ε * P) (Matrix.single c d 1) * Q) := by
    rw [conj_hpart1 hQP hPQ]; exact SmDerA.inG_cpart1 ε _
  have h2 : inG ε (P * Formalism.QuantumDeterminants.hpart2 (Pᴴ * Jm ε * P) (Matrix.single c d 1) * Q) := by
    rw [conj_hpart2 hQP hPQ]; exact SmDerA.inG_cpart2 ε _
  rw [rdv_cf hσ hQP hPQ a T x f hf h1 hg, rdv_cf hσ hQP hPQ a T x f hf h2 hg, conj_hpart1 hQP hPQ,
    conj_hpart2 hQP hPQ]
  have hY : actM (smE ε σ) (P * Matrix.single c d 1 * Q) =
      actM (smE ε σ) (S7.cpart1 ε (P * Matrix.single c d 1 * Q)) +
        Complex.I • actM (smE ε σ) (S7.cpart2 ε (P * Matrix.single c d 1 * Q)) := by
    conv_lhs => rw [SmDerA.cpart_decomp ε (P * Matrix.single c d 1 * Q)]
    rw [SmDerA.actM_add, SmDerA.actM_smul]
  rw [hY, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul,
    inner_add_right, inner_smul_right, add_smul, smul_smul]

end Coef

section Capelli

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {P Q : Matrix (Fin n) (Fin n) ℂ}

def Ec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P Q : Matrix (Fin n) (Fin n) ℂ) :
    Fin n → Fin n → Module.End ℂ (smD ε σ) :=
  fun c d => actM (smE ε σ) (P * Matrix.single c d 1 * Q)

theorem Ec_eq (c d : Fin n) :
    Ec ε σ P Q c d = ∑ a, ∑ b, (P a c * Q d b) • smE ε σ a b := by
  unfold Ec actM
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

theorem top_cf (hσ : IsURepOn (UJset ε) σ) (hQP : Q * P = 1) (hPQ : P * Q = 1) (a : H) (T : E)
    (x : smD ε σ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : ∀ h, hᴴ * (Pᴴ * Jm ε * P) * h = Pᴴ * Jm ε * P → f h = (inner ℂ a (σ (P * h * Q) x)) • T)
    (u : ℂ) (c d : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * (Pᴴ * Jm ε * P) * g = Pᴴ * Jm ε * P) :
    Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH (Pᴴ * Jm ε * P)) u c d f g =
      (inner ℂ a (σ (P * g * Q) ((Formalism.REAL.Tm (Ec ε σ P Q) u c d x : smD ε σ) : H))) • T := by
  unfold Formalism.QuantumDeterminants.Top Formalism.REAL.Tm
  rw [eabH_cf hσ hQP hPQ a T x f hf c d hg, hf g hg]
  by_cases hcd : c = d
  · rw [if_pos hcd, if_pos hcd, LinearMap.add_apply, Submodule.coe_add, map_add, inner_add_right, add_smul,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul, map_smul,
      inner_smul_right, smul_smul]
    rfl
  · rw [if_neg hcd, if_neg hcd, zero_add, zero_add]
    rfl

theorem foldr_cf (hσ : IsURepOn (UJset ε) σ) (hQP : Q * P = 1) (hPQ : P * Q = 1) (a : H) (T : E) :
    ∀ (L : List (ℂ × Fin n × Fin n)) (x : smD ε σ) (f : Matrix (Fin n) (Fin n) ℂ → E),
    (∀ h, hᴴ * (Pᴴ * Jm ε * P) * h = Pᴴ * Jm ε * P → f h = (inner ℂ a (σ (P * h * Q) x)) • T) →
    ∀ g, gᴴ * (Pᴴ * Jm ε * P) * g = Pᴴ * Jm ε * P →
      (L.map fun t => Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH (Pᴴ * Jm ε * P)) t.1 t.2.1 t.2.2).foldr (fun T' h => T' h) f g =
        (inner ℂ a (σ (P * g * Q) (((L.map fun t => Formalism.REAL.Tm (Ec ε σ P Q) t.1 t.2.1 t.2.2).prod x :
          smD ε σ) : H))) • T
  | [], x, f, hf, g, hg => by simp only [List.map_nil, List.foldr_nil, List.prod_nil, Module.End.one_apply]; exact hf g hg
  | t :: L, x, f, hf, g, hg => by
    simp only [List.map_cons, List.foldr_cons, List.prod_cons, Module.End.mul_apply]
    exact top_cf hσ hQP hPQ a T _ _ (fun h hh => foldr_cf hσ hQP hPQ a T L x f hf h hh) t.1 t.2.1 t.2.2 hg

end Capelli

section Capelli2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {P Q : Matrix (Fin n) (Fin n) ℂ}

theorem qminorOp_cf (hσ : IsURepOn (UJset ε) σ) (hQP : Q * P = 1) (hPQ : P * Q = 1) (a : H) (T : E)
    (x : smD ε σ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : ∀ h, hᴴ * (Pᴴ * Jm ε * P) * h = Pᴴ * Jm ε * P → f h = (inner ℂ a (σ (P * h * Q) x)) • T)
    {t : ℕ} (ra cb : Fin t → Fin n) (u : ℂ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ * (Pᴴ * Jm ε * P) * g = Pᴴ * Jm ε * P) :
    Formalism.QuantumDeterminants.qminorOp (Formalism.QuantumDeterminants.EabH (Pᴴ * Jm ε * P)) ra cb u f g =
      (inner ℂ a (σ (P * g * Q) ((Formalism.REAL.qminor (Ec ε σ P Q) ra cb u x : smD ε σ) : H))) • T := by
  unfold Formalism.QuantumDeterminants.qminorOp Formalism.REAL.qminor
  rw [Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum, map_sum, inner_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hL1 : (List.ofFn fun k : Fin t => Formalism.QuantumDeterminants.Top (E := E) (Formalism.QuantumDeterminants.EabH (Pᴴ * Jm ε * P)) (u - ((k : ℕ) : ℂ))
      (ra (s k)) (cb k)) = (List.ofFn fun k : Fin t => ((u - ((k : ℕ) : ℂ)), ra (s k), cb k)).map
        fun t => Formalism.QuantumDeterminants.Top (E := E) (Formalism.QuantumDeterminants.EabH (Pᴴ * Jm ε * P)) t.1 t.2.1 t.2.2 := by
    rw [List.map_ofFn]; rfl
  have hL2 : (List.ofFn fun k : Fin t => Formalism.REAL.Tm (Ec ε σ P Q) (u - (k : ℂ)) (ra (s k)) (cb k)) =
      (List.ofFn fun k : Fin t => ((u - ((k : ℕ) : ℂ)), ra (s k), cb k)).map
        fun t => Formalism.REAL.Tm (Ec ε σ P Q) t.1 t.2.1 t.2.2 := by
    rw [List.map_ofFn]; rfl
  rw [Pi.smul_apply, hL1, foldr_cf hσ hQP hPQ a T _ x f hf g hg, hL2]
  rw [show ((Equiv.Perm.sign s : ℤ) : Module.End ℂ (smD ε σ)) = ((Equiv.Perm.sign s : ℤ) : ℂ) • 1 by
    rw [Int.cast_smul_eq_zsmul ℂ, zsmul_eq_mul, mul_one]]
  rw [smul_mul_assoc, one_mul, LinearMap.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right, smul_smul]

theorem capelliH_cf (hσ : IsURepOn (UJset ε) σ) (hQP : Q * P = 1) (hPQ : P * Q = 1) (a : H) (T : E)
    (x : smD ε σ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : ∀ h, hᴴ * (Pᴴ * Jm ε * P) * h = Pᴴ * Jm ε * P → f h = (inner ℂ a (σ (P * h * Q) x)) • T)
    (u : ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * (Pᴴ * Jm ε * P) * g = Pᴴ * Jm ε * P) :
    Formalism.QuantumDeterminants.capelliH (Pᴴ * Jm ε * P) u f g =
      (inner ℂ a (σ (P * g * Q) ((Formalism.REAL.qdet (smE ε σ) u x : smD ε σ) : H))) • T := by
  unfold Formalism.QuantumDeterminants.capelliH Formalism.QuantumDeterminants.qdetOp
  rw [qminorOp_cf hσ hQP hPQ a T x f hf id id u hg]
  have hP : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr (Matrix.isUnit_det_of_right_inverse hPQ)
  have hPi : P⁻¹ = Q := Matrix.inv_eq_right_inv hPQ
  have hq := PI.UnitaryGroupMassFormula.DSIC.quasi_determinant_conj_inv (Module.End ℂ (smD ε σ)) n (smE ε σ) (isDerivedOn_smE hσ).glRep P hP u
  rw [hPi] at hq
  have hE : Ec ε σ P Q = fun a b => ∑ c, ∑ d, (P c a * Q b d) • smE ε σ c d := by
    funext c d; exact Ec_eq c d
  have hq' : Formalism.REAL.qminor (Ec ε σ P Q) id id u = Formalism.REAL.qminor (smE ε σ) id id u := by
    rw [hE]; exact hq
  show _ = (inner ℂ a (σ (P * g * Q) ((Formalism.REAL.qminor (smE ε σ) id id u x : smD ε σ) : H))) • T
  rw [hq']

end Capelli2

section Rect

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem capelliH_cf_rect {N m : ℕ} {ε : Fin N → Bool} {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {P : Matrix (Fin N) (Fin m) ℂ} {Q : Matrix (Fin m) (Fin N) ℂ} (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (a : H) (T : E) (x : smD ε σ) (f : Matrix (Fin m) (Fin m) ℂ → E)
    (hf : ∀ h, hᴴ * (Pᴴ * Jm ε * P) * h = Pᴴ * Jm ε * P → f h = (inner ℂ a (σ (P * h * Q) x)) • T)
    (u : ℂ) {g : Matrix (Fin m) (Fin m) ℂ} (hg : gᴴ * (Pᴴ * Jm ε * P) * g = Pᴴ * Jm ε * P) :
    Formalism.QuantumDeterminants.capelliH (Pᴴ * Jm ε * P) u f g =
      (inner ℂ a (σ (P * g * Q) ((Formalism.REAL.qdet (smE ε σ) u x : smD ε σ) : H))) • T := by
  have hNm : N = m := by
    have h1 := Matrix.rank_mul_le_left Q P
    have h2 := Matrix.rank_mul_le_left P Q
    rw [hQP, Matrix.rank_one] at h1
    rw [hPQ, Matrix.rank_one] at h2
    have h3 := Matrix.rank_le_width Q
    have h4 := Matrix.rank_le_width P
    simp at h1 h2 h3 h4
    omega
  subst hNm
  exact capelliH_cf hσ hQP hPQ a T x f hf u hg

end Rect

end Formalism.L2.SG.Pf.CapCoef
