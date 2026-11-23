import Mathlib
import Formalism.LocalToGlobal.Divisibility.EigenvalueSumLeClosedOf

noncomputable section

namespace Formalism.L2.DIV.Arith4S

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
open NumberField IsDedekindDomain

def c0F (Ch Cc CYL Ct : ℝ) : ℝ := max 28 (max (2 * (1 + |Cc|) + 1) (max 1 (Ch * (3 + 2 * CYL + (max Ct 5 + 3)))))

def ceF (C Ce cD C0 : ℝ) : ℝ := max C0 (C + 2 + C + (Ce + cD) + 1)

def x0F (eps Ct Cc CH ce : ℝ) : ℝ :=
  max (max 16 ((48 * (max Ct 5 + 3) / eps + 6 / eps + 2) ^ (6 / eps)))
    (max (3 + |Cc|) (max (max 9 (272 + 2 * ce))
      (max (⌈(9 * (max Ct 5 + 3) + 1 + 1) / eps⌉₊.factorial : ℝ) (⌈(max CH 0 + 1) / eps⌉₊.factorial : ℝ))))

variable {D : D7} (L : SizeData₂ D) (Del h0 : ℕ)

theorem arithClause_rec (hS : SizesAt L) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (P5 : ParameterChoice' D L) (hFD : L.FDef) (hK : DV.KapDef D)
    {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T D.R.m)
    (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* D.what₂.LLˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (cf : ConvFace A3.fam3.base3) (C CH Ch Ce cD : ℝ)
    (hTf : Finite T) (hDG : DGamSize A3.A P0 ψ0 (ofRecord D L Del h0) L.Nc hTf 1 cD)
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch)
    (hx : x0F L.sc.eps L.Ct L.Cc CH (ceF C Ce cD (c0F Ch L.Cc P5.CYL L.Ct)) ≤ L.sc.x) :
    ∀ Pk : IndefPkgR A3.fam3.amb3
        (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp (ZscFix3 A3 P0 ψ0 (ofRecord D L Del h0) (Equiv.refl _) L.Nc Ch)) cf C CH,
    ∃ (lam0 Sw C1 : ℝ) (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0
        (c0F Ch L.Cc P5.CYL L.Ct) (ceF C Ce cD (c0F Ch L.Cc P5.CYL L.Ct)) Ch Sw C1) (dg : ℕ),
      0 < dg ∧ (∀ j t, (A3.A.fam.L j t).DG (A3.A.fam.lvlA P0 ψ0) ∣ dg) ∧
      ∀ u, ArithAt A3 1 P0 ψ0 P1 ψ1 Dc Sp (ZscFix3 A3 P0 ψ0 (ofRecord D L Del h0) (Equiv.refl _) L.Nc Ch) cf C CH Pk
        (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0
          (c0F Ch L.Cc P5.CYL L.Ct) (ceF C Ce cD (c0F Ch L.Cc P5.CYL L.Ct)) Ch Sw C1 (H u))
        (fun _ => divSize L Ce) dg := by
  intro Pk
  set C0 := c0F Ch L.Cc P5.CYL L.Ct with hC0def
  set ce := ceF C Ce cD C0 with hcedef
  have h28 : 28 ≤ C0 := le_max_left _ _
  have hC1 : constantOneChoice L + 1 ≤ C0 := (le_max_left _ _).trans (le_max_right _ _)
  have hC0 : max 1 (Ch * (3 + 2 * P5.CYL + (max L.Ct 5 + 3))) ≤ C0 := (le_max_right _ _).trans (le_max_right _ _)
  have hce0 : C0 ≤ ce := le_max_left _ _
  have hce : C + 2 + C + (Ce + cD) + 1 ≤ ce := le_max_right _ _
  have hxB : max 16 ((48 * (max L.Ct 5 + 3) / L.sc.eps + 6 / L.sc.eps + 2) ^ (6 / L.sc.eps)) ≤ L.sc.x :=
    (le_max_left _ _).trans hx
  have hrest := (le_max_right _ _).trans hx
  have hx3 : 3 + |L.Cc| ≤ L.sc.x := (le_max_left _ _).trans hrest
  have hrest2 := (le_max_right _ _).trans hrest
  have hxq : max 9 (272 + 2 * ce) ≤ L.sc.x := (le_max_left _ _).trans hrest2
  have hrest3 := (le_max_right _ _).trans hrest2
  have hx1 : (⌈(9 * (max L.Ct 5 + 3) + 1 + 1) / L.sc.eps⌉₊.factorial : ℝ) ≤ L.sc.x := (le_max_left _ _).trans hrest3
  have hx2 : (⌈(max CH 0 + 1) / L.sc.eps⌉₊.factorial : ℝ) ≤ L.sc.x := (le_max_right _ _).trans hrest3
  have hB : BigX L := bigX_of L ((le_max_left _ _).trans hxB) ((le_max_right _ _).trans hxB)
  refine ⟨Real.log (Fintype.card G), swRec L, constantOneChoice L,
    fun u => numFacts_rec L Del h0 hS hB hDel hh0 P5 u hx3 ((le_max_left _ _).trans hxq) G hc C0 ce Ch hCh hC0 hC1 hce0,
    dgOf A3.A P0 ψ0 hTf, dgOf_pos A3.A P0 ψ0 hTf, dgOf_dvd A3.A P0 ψ0 hTf, fun u => ?_⟩
  exact arithAt_rec L Del h0 hS hB hDel hh0 P5 hFD hK u hx3 A3 hc P0 ψ0 P1 ψ1 Dc Sp (Equiv.refl _) cf C CH Ch C0 ce Ce Pk
    (dgOf A3.A P0 ψ0 hTf) cD hDG hC hCh h28 hC1 hC0 hce0 hce hxq hx1 hx2

end Formalism.L2.DIV.Arith4S

end
