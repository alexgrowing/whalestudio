import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreTiesOfHyp
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Plug.coreTies_of_tied : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (L : SizeData₂ D) (EX : ErrX D) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A J.Q.c.F) (μ0 : T0), Tied EX J R.C → R.toLevCh.Is μ0 → FieldSmall D L → GlobalTheory.BigOn.CoreTies L EX J R := by
  intro D G _ _ Pl0 T0 A L EX J _ R μ0 hT hL hs
  have hH : HalfEX J.toCore EX := fun i => by
    show barE D (EX.piG i) ∈ (J.pb i).asIdeal.map _
    rw [hT.core.pb]
    exact hT.half i
  exact GlobalTheory.BigOn.coreTies_of_is hL hT.core.pb hT.core.laws hT.core.canon hT.core.rank hH hT.field.one hT.field.two hs
    hT.field.del hT.field.del'
