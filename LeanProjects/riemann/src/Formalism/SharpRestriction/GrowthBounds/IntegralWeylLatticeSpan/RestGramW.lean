import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.IntSpanGSmul

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

def RestLatW (T : ∀ u : D.what₂.Word, Forms0 D u) (I : CmpIn D X) : Prop :=
  ∀ u w hg (i : (D.gat u w hg).comp) (L : (D.gat u w hg).P.Tup) (c : (D.mem u).C.cls 0)
    (g : ∀ v, GL (Fin ((D.gat u w hg).P.m + 1)) ((D.gat u w hg).P.Qq v)) (γ : GL (Fin (D.R.N 0)) D.host.E)
    (κ : ((T u).cls0).lev.U),
    (∀ v, L v = colSpan ((D.gat u w hg).P.W v) (g v : Matrix (Fin ((D.gat u w hg).P.m + 1)) (Fin ((D.gat u w hg).P.m + 1)) ((D.gat u w hg).P.Qq v))) →
    γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) →
    (locAt X u w hg I.B).IsPt i g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ *
      (((T u).cls0).y c).1 * κ.1) →
    ∀ B' : GL (Fin (D.R.N 0)) D.host.E, Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B' →
    ∀ v, L v = colSpan ((D.gat u w hg).P.W v)
      (((castGL (locAt X u w hg I.B).rk ((D.gat u w hg).P.Qq v)).symm
        (bc ((locAt X u w hg I.B).iw v) ((locAt X u w hg I.B).B⁻¹ * γ * B')) :
          GL (Fin ((D.gat u w hg).P.m + 1)) ((D.gat u w hg).P.Qq v)) :
        Matrix (Fin ((D.gat u w hg).P.m + 1)) (Fin ((D.gat u w hg).P.m + 1)) ((D.gat u w hg).P.Qq v))

def RestGramW (I : CmpIn D X) : Prop :=
  ∀ u w hg (c : (D.mem u).C.cls 0) (B' : GL (Fin (D.R.N 0)) D.host.E), Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B' →
    ∀ v a b,
      (locAt X u w hg I.B).iw v ((cT (sigD D : D.host.E →+* D.host.E) B'.1 * gramN D 0 (Nat.zero_le _) * B'.1) a b) ∈
        Set.range (algebraMap ((D.gat u w hg).P.W v) ((D.gat u w hg).P.Qq v)) ∧
      (locAt X u w hg I.B).iw v ((cT (sigD D : D.host.E →+* D.host.E) B'.1 * gramN D 0 (Nat.zero_le _) * B'.1)⁻¹ a b) ∈
        Set.range (algebraMap ((D.gat u w hg).P.W v) ((D.gat u w hg).P.Qq v))

end Formalism.L2.G.RelativeIndexFlags
