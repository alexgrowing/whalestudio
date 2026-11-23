import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FockRSmulLeft
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.CoefProd

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.MainNotions.G

def evX {K : Type} [CommRing K] {n : ℕ} (x : ℕ × Fin n → K) : GenR K n →+* MvPolynomial (Fin n × Fin n) K :=
  eval₂Hom (RingHom.id _) fun s => C (x s)

section FinalTheorems

variable {O K Kc : Type} [CommRing O] [Field K] [Algebra O K] [Infinite K] [Field Kc] [Algebra K Kc]
  {B τ τx : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (xm : B → ℕ × Fin n → τx) (hxm : Function.Injective fun x : B × (ℕ × Fin n) => xm x.1 x.2)
  (ν : B → Fin n → ℕ)
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc) (hM : ∀ (o : O), ∀ a ∈ M, algebraMap K Kc (algebraMap O K o) * a ∈ M)
  (Hg : B → GenR K n)
  (hQ : ∀ b, (weyl O n n le_rfl (ν b)).map (toK O K) ≤ Submodule.span O (Set.range fun m => coeff m (Hg b)))
  (Φ : MvPolynomial τ K →ₗ[K] Kc) (A : MvPolynomial τx Kc) (hA : ∀ m, coeff m A ∈ M)
  (hnum : ∀ x : τx → K, Φ (∏ b, rename (em b) (rowAct K (hi b) (evX (fun s => x (xm b s)) (Hg b)))) =
    eval (fun t => algebraMap K Kc (x t)) A)

include hxm hh hM hQ hA hnum in

theorem src_abs (hI : Interp) (hCP : CoefProd) (F : B → MvPolynomial (Fin n × Fin n) K)
    (hF : ∀ b, F b ∈ deltaL O K n (ν b) (h b)) : Φ (∏ b, rename (em b) (F b)) ∈ M := by
  classical
  have hh' : ∀ b, h b * hi b = 1 := fun b => mul_eq_one_comm.1 (hh b)
  let ψ : ∀ b, MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial τ K := fun b => (rename (em b)).comp (rowAct K (hi b))
  let HH : MvPolynomial τx (MvPolynomial τ K) := ∏ b, rename (xm b) (map (ψ b : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial τ K) (Hg b))
  have hcoef : ∀ p : B → (ℕ × Fin n →₀ ℕ), coeff (∑ b, (p b).mapDomain (xm b)) HH = ∏ b, ψ b (coeff (p b) (Hg b)) := by
    intro p
    rw [hCP (MvPolynomial τ K) B (ℕ × Fin n) τx xm hxm]
    exact Finset.prod_congr rfl fun b _ => coeff_map _ _ _
  have hev : ∀ x : τx → K, eval₂ (RingHom.id (MvPolynomial τ K)) (fun t => C (x t)) HH =
      ∏ b, rename (em b) (rowAct K (hi b) (evX (fun s => x (xm b s)) (Hg b))) := by
    intro x
    show eval₂Hom (RingHom.id (MvPolynomial τ K)) (fun t => C (x t)) HH = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [coe_eval₂Hom, eval₂_rename, eval₂_map]
    show _ = ψ b (eval₂ (RingHom.id _) (fun s => C (x (xm b s))) (Hg b))
    rw [← AlgHom.coe_toRingHom, eval₂_comp_left]
    congr 1
    funext s
    show C (x (xm b s)) = ψ b (C (x (xm b s)))
    exact ((ψ b).commutes (x (xm b s))).symm
  have hw : ∀ m, Φ (coeff m HH) = coeff m A := by
    intro m
    by_cases hm : m ∈ HH.support ∪ A.support
    · have := hI K τx Kc (HH.support ∪ A.support) (fun m => Φ (coeff m HH) - coeff m A) ?_ m hm
      · exact sub_eq_zero.1 this
      · intro x
        simp only [smul_sub]
        rw [Finset.sum_sub_distrib, sub_eq_zero]
        have e1 : ∑ m ∈ HH.support ∪ A.support, (m.prod fun t k => x t ^ k) • Φ (coeff m HH) =
            Φ (eval₂ (RingHom.id (MvPolynomial τ K)) (fun t => C (x t)) HH) := by
          rw [eval₂_eq, map_sum, ← Finset.sum_subset Finset.subset_union_left]
          · refine Finset.sum_congr rfl fun d _ => ?_
            rw [← map_smul]
            congr 1
            rw [RingHom.id_apply, smul_eq_C_mul, mul_comm, Finsupp.prod, map_prod]
            simp only [map_pow]
          · intro d _ hd
            rw [notMem_support_iff.1 hd, map_zero, smul_zero]
        have e2 : ∑ m ∈ HH.support ∪ A.support, (m.prod fun t k => x t ^ k) • coeff m A =
            eval (fun t => algebraMap K Kc (x t)) A := by
          rw [eval_eq, ← Finset.sum_subset Finset.subset_union_right]
          · refine Finset.sum_congr rfl fun d _ => ?_
            rw [Algebra.smul_def, mul_comm, Finsupp.prod, map_prod]
            simp only [map_pow]
          · intro d _ hd
            rw [notMem_support_iff.1 hd, smul_zero]
        rw [e1, e2, hev, hnum]
    · rw [Finset.mem_union, not_or] at hm
      rw [notMem_support_iff.1 hm.1, notMem_support_iff.1 hm.2, map_zero]
  let T : Submodule O (MvPolynomial τ K) :=
    { carrier := {G | Φ G ∈ M}
      add_mem' := fun {a b} ha hb => by
        show Φ (a + b) ∈ M
        rw [map_add]; exact M.add_mem ha hb
      zero_mem' := by show Φ 0 ∈ M; rw [map_zero]; exact M.zero_mem
      smul_mem' := fun o G hG => by
        show Φ (o • G) ∈ M
        rw [← algebraMap_smul K o G, map_smul, Algebra.smul_def]
        exact hM o _ hG }
  refine prod_span (R := O) (fun b => Set.range fun m => ψ b (coeff m (Hg b))) T ?_ _ ?_
  · intro f hf
    choose p hp using hf
    show Φ _ ∈ M
    rw [← Finset.prod_congr rfl fun b _ => hp b, ← hcoef, hw]
    exact hA _
  · intro b
    have h2 : rowAct K (h b) (F b) ∈ Submodule.span O (Set.range fun m => coeff m (Hg b)) := hQ b (hF b)
    have h3 : rename (em b) (F b) = ψ b (rowAct K (h b) (F b)) := by
      show _ = rename (em b) (rowAct K (hi b) (rowAct K (h b) (F b)))
      rw [rowAct_rowAct, hh' b, rowAct_one]
    rw [h3]
    have h4 := Submodule.mem_map_of_mem (f := (ψ b).toLinearMap.restrictScalars O) h2
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact h4

end FinalTheorems

end Formalism.L2.PairingIndexBounds.Ent
