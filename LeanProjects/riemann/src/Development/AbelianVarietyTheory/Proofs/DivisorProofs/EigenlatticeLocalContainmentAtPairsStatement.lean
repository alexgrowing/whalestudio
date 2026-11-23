import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeLocalContainmentAtPairs
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenlattice_local_containment_at_pairs : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (c : OnConst) (O : OnObj S P c), LeafSpan O → LeafData O → LeafProj O → (∀ j (g : P), O.e j ∘ₗ O.ρ j g = O.ρ j g ∘ₗ O.e j) → (AtPair S fun v => ∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) → RankAtPlaces O := by
  first | exact @GlobalTheory.OnRankAlg.rankAtPlaces_alg | exact GlobalTheory.OnRankAlg.rankAtPlaces_alg | (intros; apply GlobalTheory.OnRankAlg.rankAtPlaces_alg <;> assumption)
