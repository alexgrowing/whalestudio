import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem coeff_goodAt_eq (D : D7) (X : HidaSetting D) (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ b, a * b = b * a)
    (x : X.B.I.Gf) (γ γ' : G0g D.nd) (h : GoodAt X x γ) (h' : GoodAt X x γ') : a.coeff γ' = a.coeff γ := by
  have hP : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      γ' kv = P⁻¹ * γ kv * P := by
    intro kv
    exact Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy X.B.I (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw kv.1 kv.2))
      (D.host.g kv.1) (D.host.g_prime kv.1)
      (by rw [Formalism.L2.SG.Pf.RowDictPf.card_wB, Formalism.L2.SG.Pf.RowDictPf.card_res_host]) D.R.r X.n_eq.symm x (γ kv) (γ' kv)
      ((Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ x _).1 (h kv))
      ((Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ x _).1 (h' kv))
  choose P hP using hP
  have e : γ' = (P : G0g D.nd)⁻¹ * γ * P := funext fun kv => hP kv
  rw [e]
  exact Formalism.L2.SG.Pf.RowDictPf.coeff_conj_of_central ha γ P

theorem coeff_chosenRed_eq_redHom : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd), IsRedHom X red →
    ∀ a : MonoidAlgebra ℂ (G0g D.nd), (∀ b, a * b = b * a) → ∀ x : X.B.I.Gf,
    (if h : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ then
      a.coeff (Classical.choose h.2) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0) =
    if x ∈ X.B.I.Kset then a.coeff (red x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0 := by
  intro D X red hred a ha x
  by_cases hx : x ∈ X.B.I.Kset
  · have hc : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ := ⟨hx, red x, hred.1 x hx⟩
    rw [dif_pos hc, if_pos hx,
      coeff_goodAt_eq D X a ha x (red x) (Classical.choose hc.2) (hred.1 x hx) (Classical.choose_spec hc.2)]
  · rw [dif_neg (fun h => hx h.1), if_neg hx]

end GlobalTheory
