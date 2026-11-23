import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain

theorem exists_intertwiner_of_index_eq {D : D7} (hP : ItPair D) (k : Fin D.R.m) (hk : ChainPar D k)
    (V W : HSp D) (a b : ℕ) (ha : a = k) (hb : b = k + 1)
    (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (hθ : IsInfFam θ) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      ∀ ω f, IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  subst ha hb
  obtain ⟨It, -, hIt⟩ := hP k V W M M' θ ψ hθ hk
  exact ⟨It, hIt⟩

theorem innerIntertwiners_of_pair (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (hP : ItPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : StepsOK R) :
    ItYSt R := by
  intro k hk
  have hk0 : k < D.R.m := Nat.lt_of_succ_lt hk
  obtain ⟨It, hIt⟩ := exists_intertwiner_of_index_eq hP ⟨k, hk0⟩ (hC _) (Yc D k) (Yc D (k + 1))
    (min k D.R.m) (min (k + 1) D.R.m) (Nat.min_eq_left hk0.le) (Nat.min_eq_left hk.le)
    (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ
  refine ⟨It, fun t => ?_⟩
  obtain ⟨hω, hv⟩ := hS.1 t ⟨k, hk0⟩ hk
  exact hIt _ _ hω hv

end GlobalTheory.Chain
