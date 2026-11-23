import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ExportPin.Model

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem theta_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL μ j) :
    D.what₂.thetaP ν j (D.what₂.jMt ν j (h ▸ x)) = D.what₂.thetaP μ j (D.what₂.jMt μ j x) := by
  subst h; rfl

set_option synthInstance.maxHeartbeats 400000 in

theorem pin_of_export (p : PtAt ex Csz) (hE : p.ExportRow)
    (hD : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I) :
    ClassSumPin p := by
  intro w i h1 h2 t ht hw c x hx hxT y hy n a f hsum
  obtain ⟨jD, hjD, ⟨N⟩⟩ := hE
  have e1 := hjD i (p.P.JM.eW i (((p.P.A3.indefDown p.P.S0).θ i t).mulVec
        ((lPrj D p.P.A3.A p.P.P0 p.P.ψ0 (p.P.A3.fam3.toSub2 p.P.Zs) i t).mulVec c))) y
        (by rw [LinearEquiv.symm_apply_apply]; exact hy)
  have e2 := (p.nexp.fi i).e.injective (e1.trans hsum.symm)
  have e3 := N.eMj_sum w _ h1 h2 _ n a f e2
  refine Eq.trans ?_ e3
  symm
  apply N.eMj_th w _ hw h1 h2 x hxT
  rw [p.P.mjH.j_eq, ← hD.thTheta, hx]
  exact (theta_cast _ _ _ ht _).symm

theorem pin_of_rows (p : PtAt ex Csz) (h : p.Rows) : ClassSumPin p := pin_of_export p h.export_ h.divRows

theorem dim_eq (p : PtAt ex Csz) (i : Fin D.R.m) :
    (p.P.A3.indefDown p.P.S0).dW i = Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i) := by
  have hz := p.zs
  have hs := p.s0
  have key : ∀ (Z : DefSub p.P.A3.fam3.amb3) (S : IndefData (p.P.A3.side3 p.P.P0 p.P.ψ0 Z)), Z = p.P.Zs → HEq S p.P.S0 →
      p.P.S0.dW i = S.dW i := by
    intro Z S h1 h2
    subst h1
    rw [eq_of_heq h2]
  exact key _ _ hz hs

theorem exists_heq_fin {K : Type} {a b : ℕ} (h : a = b) (z : Fin a → K) : ∃ y : Fin b → K, HEq z y := by
  subst h; exact ⟨z, HEq.rfl⟩

theorem exists_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL ν j) :
    ∃ x' : D.what₂.MtL μ j, x = h ▸ x' := by
  subst h; exact ⟨x, rfl⟩

theorem exists_sum (p : PtAt ex Csz) (i : Fin D.R.m) (v : Fin (p.R.nW i) → D.what₂.LL) :
    ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK p.Sx ((i : ℕ) + 1)),
      (p.nexp.fi i).e (∑ k, a k • (show ↥(p.Sx.A ((i : ℕ) + 1)).WK from f k).1) = v := by
  obtain ⟨n, b, hb, -, -, -, hs⟩ := p.fw.ks i
  have hv : v ∈ Submodule.span D.what₂.LL (Set.range b) := by rw [hs]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  refine ⟨n, a, fun k => (⟨(p.nexp.fi i).e.symm (b k), ((p.nexp.fi i).wk _).2 (by
    rw [LinearEquiv.apply_symm_apply]; exact hb k)⟩ : ↥(p.Sx.A ((i : ℕ) + 1)).WK), ?_⟩
  rw [map_sum, ← ha]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  congr 1
  exact (p.nexp.fi i).e.apply_symm_apply _

theorem premises_met (p : PtAt ex Csz) (w : D.what₂.places.Pl) (i : Fin D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0)
    (x : D.what₂.MtL (D.what₂.muTw w) ((i : ℕ) + 1)) :
    ∃ (t : p.P.T) (ht : p.P.I.tup t = D.what₂.muTw w) (c : Fin (lDim D p.P.A3.A p.P.P0 p.P.ψ0 i t) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)) → D.what₂.LL)
      (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK p.Sx ((i : ℕ) + 1)),
      x = ht ▸ p.P.I.eMt i t c ∧
      HEq (((p.P.A3.indefDown p.P.S0).θ i t).mulVec
        ((lPrj D p.P.A3.A p.P.P0 p.P.ψ0 (p.P.A3.fam3.toSub2 p.P.Zs) i t).mulVec c)) y ∧
      (p.nexp.fi i).e (∑ k, a k • (show ↥(p.Sx.A ((i : ℕ) + 1)).WK from f k).1) = jDL p.R p.F.lv2 i y := by
  have h0 : D.what₂.muAt w = D.what₂.muTw w := (D.what₂.muAt_or w).resolve_left hw
  have ht : p.P.I.tup (p.tupT (D.what₂.muAt w)) = D.what₂.muTw w := (p.tupTie _ (Or.inr ⟨w, rfl⟩)).trans h0
  obtain ⟨x', hx'⟩ := exists_cast ((i : ℕ) + 1) _ _ ht x
  obtain ⟨c, rfl⟩ := (p.P.I.eMt i _).surjective x'
  obtain ⟨y, hy⟩ := exists_heq_fin (dim_eq p i) (((p.P.A3.indefDown p.P.S0).θ i _).mulVec
        ((lPrj D p.P.A3.A p.P.P0 p.P.ψ0 (p.P.A3.fam3.toSub2 p.P.Zs) i _).mulVec c))
  obtain ⟨n, a, f, hf⟩ := exists_sum p i (jDL p.R p.F.lv2 i y)
  exact ⟨_, ht, c, y, n, a, f, hx', hy, hf⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem classSum_of_pin (p : PtAt ex Csz) (hP : ClassSumPin p)
    (hD : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I)
    (w : D.what₂.places.Pl) (i : Fin D.R.m) (h1 : 1 ≤ (i : ℕ) + 1) (h2 : (i : ℕ) + 1 ≤ D.R.m)
    (hw : D.what₂.muAt w ≠ D.what₂.mu0)
    (jD : (Y.MjH ((i : ℕ) + 1)).V → p.Sx.WL ((i : ℕ) + 1))
    (hjD : ∀ (x : (Y.MjH ((i : ℕ) + 1)).V)
      (y : Fin (Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)) → D.what₂.LL),
      HEq ((p.P.JM.eW i).symm x) y → (p.nexp.fi i).e (jD x) = jDL p.R p.F.lv2 i y)
    (eMj : (Y.MjH ((i : ℕ) + 1)).V → FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)]
      D.nexp.Fm (ex.nch.twI w) ((i : ℕ) + 1) (ex.nch.sd w))
    (hsum : ∀ (x : (Y.MjH ((i : ℕ) + 1)).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK p.Sx ((i : ℕ) + 1)),
      jD x = ∑ k, a k • (show ↥(p.Sx.A ((i : ℕ) + 1)).WK from f k).1 →
      eMj x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
          (p.nexp.eF (ex.nch.twI w) ((i : ℕ) + 1) (ex.nch.sd w) h1 h2).symm
            ((1 : KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k))
    (x : D.what₂.MtL (D.what₂.muTw w) ((i : ℕ) + 1)) (hx : x ∈ Idx.TjV D (D.what₂.muTw w) ((i : ℕ) + 1))
    (z : (Y.MjH ((i : ℕ) + 1)).V)
    (hz : Y.jM _ z = D.what₂.thetaP (D.what₂.muTw w) _ (D.what₂.jMt (D.what₂.muTw w) _ x)) :
    eMj z = NChoice.thPe D ex.nch w ((i : ℕ) + 1) (ex.nch.eMt w ((i : ℕ) + 1) x) := by
  obtain ⟨t, ht, c, y, n, a, f, e1, e2, e3⟩ := premises_met p w i hw x
  rw [hP w i h1 h2 t ht hw c x e1 hx y e2 n a f e3]
  apply hsum
  apply (p.nexp.fi i).e.injective
  rw [e3]
  apply hjD
  have : z = p.P.JM.eW i (((p.P.A3.indefDown p.P.S0).θ i t).mulVec
        ((lPrj D p.P.A3.A p.P.P0 p.P.ψ0 (p.P.A3.fam3.toSub2 p.P.Zs) i t).mulVec c)) := by
    apply Idx.jM_inj Y
    rw [hz, p.P.mjH.j_eq, ← hD.thTheta, e1]
    exact theta_cast _ _ _ ht _
  rw [this, LinearEquiv.symm_apply_apply]
  exact e2

end GlobalTheory.ExportPin.Model
