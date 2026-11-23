import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JEvExistsAndJEvBar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjReading

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

private theorem tieIn_of_fwTie' (fw : FWTie T R κ v₀) : TieIn T R κ v₀ where
  laws := fw.laws
  alg := fw.alg_eq
  kap := fw.kap
  hv₀ := fw.hv₀
  chiR := fw.chiR
  x0 i σ hσ := fw.x0 i σ hσ

private theorem pb_eq_of_omPins (hL : R.toLevCh.Is A.μ0) (fw : FWTie T R κ v₀) (i : Fin D.R.m)
    (hOi : OMPins T R κ v₀ O i) : T.pb = R.C.P.pb :=
  GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R fw.laws.toLawsM hL (hOi.2.tuple ()).half

private theorem jEvExists_and_jEvBar_of_isEmpty (hm : IsEmpty (Fin D.R.m)) : JEvExists T R κ v₀ ∧ JEvBar T R κ := by
  constructor
  · intro i
    exact hm.elim i
  · intro i
    exact hm.elim i

theorem jEvExists_and_jEvBar (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (fw : FWTie T R κ v₀)
    (hO : ∀ i, OMPins T R κ v₀ O i) : JEvExists T R κ v₀ ∧ JEvBar T R κ := by
  rcases isEmpty_or_nonempty (Fin D.R.m) with hm | hne
  · exact jEvExists_and_jEvBar_of_isEmpty T R κ v₀ hm
  · obtain ⟨i⟩ := hne
    have htie := tieIn_of_fwTie' T R κ v₀ fw
    have hpb := pb_eq_of_omPins T R κ v₀ O hL fw i (hO i)
    exact GlobalTheory.CuspValues.jEvExists_and_jEvBar _ _ _ _ _ T R κ v₀ hL hM htie hpb

theorem jEvExists (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (fw : FWTie T R κ v₀)
    (hO : ∀ i, OMPins T R κ v₀ O i) : JEvExists T R κ v₀ := by
  obtain ⟨hJ, -⟩ := jEvExists_and_jEvBar T R κ v₀ O hL hM fw hO
  exact hJ

theorem jEvBar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → R.IsModels → FWTie T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → JEvBar T R κ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hL hM fw hO
  obtain ⟨-, hB⟩ := jEvExists_and_jEvBar T R κ v₀ O hL hM fw hO
  exact hB

end GlobalTheory.ConjReading
