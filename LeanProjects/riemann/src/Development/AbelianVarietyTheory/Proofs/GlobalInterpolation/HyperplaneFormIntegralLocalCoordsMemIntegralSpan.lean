import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalBasisRepLatticeIntegralCoordsSpecStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWDelAtrIffStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanMapNabKDelK
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PtIntCoord

theorem natW_shW {n : ℕ} (l : DomWeight n) (c : ℤ) : (GlobalTheory.Mem.Col2.shW l c).natW = l.natW := by
  have e : GlobalTheory.Mem.Col2.shW l c = Formalism.MainNotions.product_first_zeroth_parts.wSh l (-c) := by
    unfold GlobalTheory.Mem.Col2.shW Formalism.MainNotions.product_first_zeroth_parts.wSh
    congr 1
    funext i
    ring
  rw [e, Formalism.MainNotions.product_first_zeroth_parts.natW_wSh]

theorem coP_mem_intSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ z ∈ ((I.tw l l0 Z).fm u a).ptC, (∃ y ∈ ((I.tw l l0 Z).fm u a).SP w, ((I.tw l l0 Z).fm u a).ptEmb y = z) → ∀ c, GlobalTheory.PerQ.Co.coP I u a w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w ((I.rec7 l Z).fm u).sg := by
  intro B X I hI l Z l0 u a w z _hz hyz c
  obtain ⟨y, hy, rfl⟩ := hyz
  clear _hz
  have hQ : (I.perIn u a).Ok := l.per u a
  have hA : y.1 c ∈ locW B.places w (delAtr B.fields.emb (I.perIn u a).sgT
      ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c))) := by
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hx c)
    | zero => exact Submodule.zero_mem _
    | add x x' _ _ hx hx' => exact Submodule.add_mem _ hx hx'
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  have hB := (GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c).1
  have key := (GlobalTheory.T.mem_locW_delAtr_iff' B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq
    (I.perIn u a).sgT (I.perIn u a).sg (fun τ => natW_shW _ _) _ (hQ.step.lsh_lat c.1 _) w _ hB (y.1 c)).1 hA
  have e : GlobalTheory.PerQ.Co.coP I u a w (((I.tw l l0 Z).fm u a).ptEmb y) c =
      MvPolynomial.map B.embLL (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹ (y.1 c)).1 := by
    show actP _ _ (polOf _ _ _ (evV B.fields.emb 1 (I.perIn u a).sgT B.embLL (y.1 c))) = _
    rw [GlobalTheory.LvT.BuiltChain.polOf_evV]
    show _ = MvPolynomial.map B.embLL (actP (I.perIn u a).sgT
      (invTrK (Formalism.L2.DIV.embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹)) (y.1 c).1)
    rw [GlobalTheory.ValCmp.use₂]
    congr 2
  rw [e]
  exact key

end GlobalTheory.PtIntCoord
