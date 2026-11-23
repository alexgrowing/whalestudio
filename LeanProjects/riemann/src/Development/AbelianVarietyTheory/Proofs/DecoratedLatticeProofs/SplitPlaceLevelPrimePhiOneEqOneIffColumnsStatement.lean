import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLevelPrimePhiOneEqOneIffColumns
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maps_rd_iff_colCond_toHom : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P →
    ∀ {S T : HSp D} {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (α : Frame p S (Fin S.rank)) (β : Frame p T (Fin T.rank))
    (Q : Pair k (Fin S.rank)) (Q' : Pair k (Fin T.rank)) (LS : Lat S) (LT : Lat T) (t : 𝓞 D.host.E),
    (∀ z, z ∈ LS ↔ z ∈ intVec D _) → (∀ z, z ∈ LT ↔ z ∈ intVec D _) → α.IsLat LS Q.lat → β.IsLat LT Q'.lat →
    (∀ w ∈ LS, ∀ r : Fin S.rank, r.1 + 1 = S.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q.HasVal (α.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    (∀ w ∈ LT, ∀ r : Fin T.rank, r.1 + 1 = T.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q'.HasVal (β.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (Maps Q Q' (GlobalTheory.FinPl.rd α β (z.map (incA D))) ↔ ColCond P t (toHom S T hS hT z)) := by
  first | exact @GlobalTheory.PhiOneVal.maps_rd_iff_colCond | exact GlobalTheory.PhiOneVal.maps_rd_iff_colCond | (intros; apply GlobalTheory.PhiOneVal.maps_rd_iff_colCond <;> assumption)
