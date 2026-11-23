import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PcRes

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (pc P h hN hF hS).Dpcris ρ = Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ∧ ((pc P h hN hF hS).IsPotCrys ρ ↔ IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) := by
  intro l _ P K K' LL h hN hF hS V _ _ _ _ ρ
  have key : (pc P h hN hF hS).Dpcris ρ =
      Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
    unfold PotCrysData.Dpcris Dcris
    exact (GKinEquiv h).surjective.iInf_congr (GKinEquiv h) (fun x => rfl)
  refine ⟨key, ?_⟩
  unfold PotCrysData.IsPotCrys IsCrys
  have key' : Dcris (pc P h hN hF hS).PD' ((pc P h hN hF hS).resH ρ) =
      Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := key
  rw [key']

end GlobalTheory.PcRes
