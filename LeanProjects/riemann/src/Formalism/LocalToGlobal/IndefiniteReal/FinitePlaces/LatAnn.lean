import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PairingRankOneMemInverseDifferent

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

set_option maxHeartbeats 800000 in

theorem lat_ann (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {x : WO S T}
    (hx : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True))
    {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    ψ (symplO S T x u) = 1 := by
  have inner : ∀ {α : Af D.host.F} {c : D.host.E} {s : Fin S.rank → D.host.E} {t : Fin T.rank → D.host.E},
      α ∈ intAf D.host.F → c ∈ D.host.AA → s ∈ ΛS → t ∈ ΛT →
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ψ (symplO S T (pairA D.host.F 0 α • ratW T S (rk1 S T c s t)) u) = 1 := by
    intro α c s t hα hc hs ht u hu
    induction hu using AddSubgroup.closure_induction with
    | mem u' hu' =>
      obtain ⟨α', hα', -, c', hc', s', hs', t', ht', rfl⟩ := hu'
      rw [gen_eq]
      exact psi_gen hψ S T hS hT hα hα' hc hc' hs hs' ht ht'
    | zero => rw [symplO_zero_right, AddChar.map_zero_eq_one]
    | add u1 u2 _ _ h1 h2 => rw [symplO_add_right, AddChar.map_add_eq_mul, h1, h2, one_mul]
    | neg u' _ h => rw [symplO_neg_right, AddChar.map_neg_eq_inv, h, inv_one]
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩ := hx'
    rw [gen_eq]
    exact inner hα hc hs ht u hu
  | zero => rw [symplO_zero_left, AddChar.map_zero_eq_one]
  | add x1 x2 _ _ h1 h2 => rw [symplO_add_left, AddChar.map_add_eq_mul, h1, h2, one_mul]
  | neg x' _ h => rw [symplO_neg_left, AddChar.map_neg_eq_inv, h, inv_one]

end Formalism.IndefR.Fin

end
