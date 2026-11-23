import Formalism.LocalToGlobal.HermitianForms.TiedBrCo
import Formalism.LocalToGlobal.HermitianForms.TiedBrRep

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

variable {D : D7} {u : D.what₂.Word}

structure PendClauses (Tf : FormsTied D u)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  coM_mem : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMT Tf B w c (φ ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan ((D.fm u).lam D.R.m)
  coM_inj : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMT Tf B w c (φ ((D.fm u).til c)) = 0 → φ ((D.fm u).til c) = 0
  coP_mem : ∀ w, ∀ z ∈ (D.fm u).ptC, ∀ c, coPT Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg
  coP_inj : ∀ w, ∀ z ∈ (D.fm u).ptC, coPT Tf B w z = 0 → z = 0
  exP : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPT Tf B w z c = Formalism.L2.Ker.brTen D u (coMT Tf B w c (φ ((D.fm u).til c)))
  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coMT Tf B w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔
    ∀ c, coPT Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg
  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMT Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMT Tf B w c (φ ((D.fm u).til c))))).re
  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPT Tf B w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPT Tf B w z c))).re

def pendOf (Tf : FormsTied D u) (hL : LowerLevelCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendClauses Tf B gP) : Pend D u where
  br τ := Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)
  coM := coMT Tf B
  coP := coPT Tf B
  coM_mem := h.coM_mem
  coM_inj := h.coM_inj
  coP_mem := h.coP_mem
  coP_inj := h.coP_inj
  Pt_eq := by
    intro w φ hφ c
    obtain ⟨P, hP, hv, hz⟩ := h.exP w φ hφ c
    exact hz _ (hL.map.pt_eq (bZ_isUnit Tf) φ c P hP hv)
  lat_co := h.lat_co
  pt_co := h.pt_co
  gP := gP
  ipV_co := h.ipV_co
  re_petersson_self_eq_sum_coord := h.re_petersson_self_eq_sum_coord
  beOn_eq := hL.beOn
  interlace := sg_interlace Tf.valP

theorem brExists_of_tied (Tf : FormsTied D u) (hL : LowerLevelCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendClauses Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  ⟨pendOf Tf hL B gP h, archimedeanSignatureMatching_of_trivial_branching Tf _ fun _ => rfl⟩

end Formalism.L2.Forms
