import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.EopUEq
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.SumFib

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 4000000 in

theorem du_formula_of_fibre_count (T : Forms0 D u) (hF : DUFib0F T) : DUFormulaLevelZero D u := by
  intro v φ hφ
  obtain ⟨G, hG, hGφ⟩ := S0.forms_from_adelic_function T 0 (Nat.zero_le _) rfl φ hφ
  have hGA := (Submodule.mem_inf.1 hG).1
  choose k hk δ hδ using fun a => S0.diamond_elements_exist_all T 0 (Nat.zero_le _) rfl v a
  funext c
  have : Finite ((D.fm u).lk 0 v c) := Module.finite_of_finite ((D.mem u).A.Fv v)
  letI : Fintype ((D.fm u).lk 0 v c) := Fintype.ofFinite _
  have hdia : ∀ a, dia D u 0 v a φ c = fun s => G (T.cls0.y c * δ a) (T.val0.eY s) := by
    intro a
    show (D.fm u).dilT 0 v a c (φ ((D.fm u).dil 0 v a c)) = _
    rw [hGφ]
    exact T.val0.dilT v a (k a) (hk a) c (δ a) (hδ a) G hGA
  obtain ⟨γ, η, κ, Mu, hmv, hMu, πD, πE, τ, hcE, hcD, hval⟩ := hF v c
  obtain ⟨hself, hDE, hEE, hline⟩ := hval G hGA
  funext s
  rw [norm_eq_sum_diamond]
  simp only [Formalism.MainNotions.product_first_zeroth_parts.trp, LinearMap.smul_apply, LinearMap.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_apply]
  rw [dopU_eq T v φ hGA hGφ c γ η κ Mu hmv hMu, eopU_eq T v φ hGA hGφ c γ η κ Mu hmv hMu]
  simp only [hdia]
  exact comb_du ((D.fm u).te 0 v c) ((D.fm u).te_ne 0 v c) (D.mem u).A.T (D.R.N 0 - 1) (D.R.N 0 - 2)
    (D.mem u).A.T_prime.ne_zero πD πE _ _ (φ c s) (fun a => G (T.cls0.y c * δ a) (T.val0.eY s)) τ
    hcE hcD
    (fun p hp => by rw [hGφ c]; exact congrFun (hself p hp) _) (fun p q h => congrFun (hDE p q h) _)
    (fun p q h => congrFun (hEE p q h) _)
    (fun a q hq => congrFun (hline a q hq (k (τ a)) (hk (τ a)) (δ (τ a)) (hδ (τ a))) _)

theorem dUAll_of (h : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), DUFib0F T) : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.DUAll :=
  fun D u T => du_formula_of_fibre_count T (h D u T)

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
