import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharacterTrivialOnPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationPrincipalLevelEqCoreLevelOpenStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.PrincLevChar

theorem castDict_apply {D : D7} {Y : Type} {V W : HSp D} (hV : V = W) (μ : GA D V → Y) (k : GA D W) :
    castDict hV μ k = μ (cast (congrArg (GA D) hV.symm) k) := by
  subst hV
  rfl

set_option maxHeartbeats 1000000 in

theorem char_eq_one : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) k = 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hpb i σ hσ hV k hk
  rw [castDict_apply]
  exact GlobalTheory.T.dictionary_character_trivial_on_principal_level T R κ v₀ hL ht hpb i (res T σ) hσ hV _
    (((GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM ht hpb i σ hσ hV).1 k).1 hk)

end GlobalTheory.HolDict.PrincLevChar
