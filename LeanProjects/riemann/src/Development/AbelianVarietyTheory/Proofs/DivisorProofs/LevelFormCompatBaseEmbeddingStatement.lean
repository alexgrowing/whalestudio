import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_form_compat_base_embedding : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.toCore.σ₀ → ∀ k : (T.U ((i : ℕ) + 1) σ).Comp, IsMod (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) ∧ IsONFr ((T.U ((i : ℕ) + 1) σ).X k) (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) ∧ IsInvOf (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) (cart (R.MW i (sg0 D A))) ∧ ((T.U ((i : ℕ) + 1) σ).X k).p0 = (T.Q.Dw ((i : ℕ) + 1)).q ∧ D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q ∧ (T.Q.Dw ((i : ℕ) + 1)).p ≠ (T.Q.Dw ((i : ℕ) + 1)).q ∧ 1 ≤ D.R.r ∧ (T.Q.H.rt : D.host.E) = D.host.sqrtMinusD ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ ((T.U ((i : ℕ) + 1) σ).X k).Ψ ↔ τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0) ∧ (∀ hq : ((T.U ((i : ℕ) + 1) σ).X k).p0 + (T.Q.Dw ((i : ℕ) + 1)).p = D.R.r, IsBasOf (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) hq (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) (onb (R.MW i (sg0 D A)))) ∧ Dom (wtA (κ i)) (Vc D i).rank ∧ (κ i).n = (Vc D i).rank ∧ LastPos (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) := by
  first | exact @GlobalTheory.AdTh.models_at_record | exact GlobalTheory.AdTh.models_at_record | (intros; apply GlobalTheory.AdTh.models_at_record <;> assumption)
