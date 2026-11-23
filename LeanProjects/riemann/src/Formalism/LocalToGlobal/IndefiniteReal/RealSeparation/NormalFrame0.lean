import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormFr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def frame0 (i : ℕ) : Fin (D.sp.Y 0).rank → D.host.E :=
  if h : i < D.R.rS then (D.sp.Y 0).frame.repr (D.sp.hypE ⟨i, h⟩)
  else if i = D.R.rS then (D.sp.Y 0).frame.repr D.sp.zm
  else if h' : 2 * D.R.rS - i < D.R.rS then
    (D.sp.Y 0).frame.repr ((-(D.sp.T : D.host.E)) • D.sp.hypF ⟨2 * D.R.rS - i, h'⟩)
  else 0

open Classical in

def NormalFrame0 (βY0 : GL (Fin (D.sp.Y 0).rank) (EAf D)) (S Pg : Finset (Pl D.host.E)) : Prop :=
  ∀ PP ∈ S, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
    (∀ i < D.R.m - 1, ∀ col : Fin (D.sp.Y 0).rank, col.val = D.R.N 0 + i →
      ColAt 0 βY0.val ei col fun r =>
        (if PP ∈ Pg then ((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) else 1) * frame0 i r) ∧
    (∀ col : Fin (D.sp.Y 0).rank, col.val < D.R.N 0 → XSpanAt 0 βY0.val ei col)

def VertexAt (j : ℕ) (βY0 : GL (Fin (D.sp.Y 0).rank) (EAf D)) (βW : GL (Fin (D.sp.W j).rank) (EAf D))
    (e : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W j).rank)
    (ι : GL (Fin (D.sp.W j).rank) (EAf D)) (Pg : Finset (Pl D.host.E)) : Prop :=
  (∀ k, (e k).val = k.val) ∧
  Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) ι.val *
            (((D.sp.Y 0).gram.reindex e e).map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F))) *
            ι.val =
    (D.sp.W j).gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) ∧
  ∀ PP ∈ Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
    IsIntM (toEAf D ei • ((βY0⁻¹ : GL (Fin (D.sp.Y 0).rank) (EAf D)).val.reindex e e * ι.val * βW.val)) ∧
      redM PP (toEAf D ei • ((βY0⁻¹ : GL (Fin (D.sp.Y 0).rank) (EAf D)).val.reindex e e * ι.val * βW.val)) = 1

end Formalism.IndefR.Mi

end
