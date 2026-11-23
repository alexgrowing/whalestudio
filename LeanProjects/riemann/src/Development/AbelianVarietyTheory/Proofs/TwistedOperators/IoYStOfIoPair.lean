import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain

theorem IoPair.of_index_eq {D : D7} (hP : IoPair D) (k : Fin D.R.m) (a b : ℕ) (ha : a = k) (hb : b = k + 1)
    (V W : HSp D) (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (hθ : IsInfFam θ) (hC : ChainPar D k)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
    (hW : IsStepWeil k ψ V W ω) (hV : IsVacVec ψ θ M M' f)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hI : IsItW θ M M' ω (ptOf ψ θ M M' f) It)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (hJ : ∀ κ ∈ J, κ ∈ GfC V ∧ ω (κ, 1) f = χ κ • f)
    (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (hν : ν.IsHaarMeasure)
    (h𝓕 : MeasureTheory.IsFundamentalDomain (GQ W) 𝓕 ν)
    (J' : Set (GA D W)) (χ' : GA D W → ℂ) (C : Submodule ℂ (SmT M' →ₗ[ℂ] (GA D W → ℂ)))
    (hle : C ≤ MultT θ M' J' χ') :
    Lift.IoExists ν 𝓕 (thetaKO ω) (ptOf ψ θ M M' f) It C (MultT θ M J χ) := by
  subst ha hb
  exact hP k V W M M' θ ψ hθ hC ω f hW hV It hI J χ hJ ν 𝓕 hν h𝓕 J' χ' C hle

theorem ioYSt_of_ioPair (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : StepsOK R) (hL : LawsOK R)
    (hν : R.models_νY) (hν' : R.models_νY') (hI : R.chain_ItY) : IoYSt R := by
  intro t k hk
  have hkm : k < D.R.m := Nat.lt_of_succ_lt hk
  have hIt := hI
  have hInner := hν
  have hLast := hν'
  unfold RealDat.chain_ItY at hIt
  unfold RealDat.models_νY at hInner
  unfold RealDat.models_νY' at hLast

  have hmeas : (R.νY t (k + 1)).IsHaarMeasure ∧
      MeasureTheory.IsFundamentalDomain (GQ (Yc D (k + 1))) (R.fdY t (k + 1)) (R.νY t (k + 1)) := by
    by_cases h2 : k + 1 + 1 < D.R.m
    · exact ⟨(hInner t (k + 1) h2).1.1, (hInner t (k + 1) h2).2⟩
    · have atLast : ∀ j, j = D.R.m - 1 → (R.νY t j).IsHaarMeasure ∧
          MeasureTheory.IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
        rintro j rfl
        exact ⟨(hLast t).1.1, (hLast t).2⟩
      exact atLast (k + 1) (by omega)
  obtain ⟨hW, hV⟩ := hS.1 t ⟨k, hkm⟩ hk
  exact IoPair.of_index_eq hP ⟨k, hkm⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left hkm.le)
    (min_eq_left hk.le) (Yc D k) (Yc D (k + 1)) (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY t k)
    (R.vY t k) hW hV (R.ItY k) (hIt t k hk) _ _ (hL.1 t k hk) (R.νY t (k + 1)) (R.fdY t (k + 1))
    hmeas.1 hmeas.2 _ _ (R.CC t (k + 1)) le_rfl

end GlobalTheory.Chain
