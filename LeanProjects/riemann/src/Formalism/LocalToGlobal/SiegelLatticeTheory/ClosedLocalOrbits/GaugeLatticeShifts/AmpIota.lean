import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActRRep

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.AmpIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ratLink_unique {x y : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x γ)
    (hy : RatLink X y γ) : x = y := by
  obtain ⟨M, -, h1, h2, h3⟩ := hx
  obtain ⟨N, -, k1, k2, k3⟩ := hy
  have hMN : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = N := by
    ext i j
    obtain ⟨w, hw⟩ : ∃ w, X.crd w = Pi.single j 1 :=
      ⟨Formalism.L2.SG.Pf.LatDictK.vOf X (Pi.single j 1), Formalism.L2.SG.Pf.LatDictK.crd_vOf X _⟩
    have e := (h3 w).symm.trans (k3 w)
    rw [hw] at e
    have := congrFun e i
    simpa [Matrix.mulVec_single_one] using this
  have hMN' : M = N := Units.ext hMN
  subst hMN'
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((h1 v).trans (k1 v).symm))
  · exact Subtype.ext (Units.ext (h2.trans k2.symm))

variable {X} (TR : TypedRed X)

theorem levi_eq_one_of {a : X.B.I.Gf} (ga : Good X a)
    (hb : ∀ j, (X.B.I.fmat a - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0)) : levi TR a = 1 := by
  funext v
  apply Units.ext
  rw [levi_coe TR ga]
  ext i j
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  have hI := hA_int X.B.I (hbwd i) (K_mv X.B.I ga.1.1 (hbw j))
  have hZ1 : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) ((X.B.I.fmat a - 1) *ᵥ X.bw j)) :=
    Z_pair_Mo X (hbwd i) (by rintro _ ⟨b, rfl⟩; exact dual_beta_reference_congruence i b) _ (hb j)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right] at hZ1
  have hZ := Z_add X.B.I X.B.g hZ1 (X.bw_dual i j)
  rw [show hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j) - hA X.B.I (X.bwd i) (X.bw j) +
    (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) =
    hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j) - if i = j then X.ew else 0 by ring] at hZ
  show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j)) = _
  rw [resT_of_mem TR v hI, res_of_Z_delta TR v hI (i = j) hZ, Pi.one_apply, Units.val_one, Matrix.one_apply]

theorem rep_split {u u' : D.what₂.Word} (Y : Formalism.L2.SG.Full.Full X) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Λ ∈ Y.what₂ u) (hΛ' : Λ' ∈ Y.what₂ u') (p q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ')
    (hpq : GRel X u u' (X.Fu u) (X.Fu u') Λ Λ' p q) :
    ∃ (n n' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (xn xn' : X.B.I.GA),
      n ∈ NLam Λ (lf D (X.Fu u)) ∧ n' ∈ NLam Λ' (lf D (X.Fu u')) ∧ RatLink X xn n ∧ RatLink X xn' n' ∧
      q.1.2 = n * p.1.2 * n' ∧ q.1.1 = xn * p.1.1 * xn' := by
  obtain ⟨n, hn, n', hn', hq⟩ := hpq
  obtain ⟨xn, hxn⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hn.1.1
  obtain ⟨xn', hxn'⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n' hn'.1.1
  refine ⟨n, n', xn, xn', hn, hn', hxn, hxn', hq, ?_⟩
  have h1 : RatLink X q.1.1 q.1.2 := q.2.1
  have h2 : RatLink X (xn * p.1.1 * xn') (n * p.1.2 * n') := ratLink_mul X (ratLink_mul X hxn p.2.1) hxn'
  rw [← hq] at h2
  exact ratLink_unique X h1 h2

end Formalism.L2.SG.Pf.AmpIota

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.AmpIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iotaRepC_holds : Formalism.L2.SG.Pf.SatGramRep.IotaRepC := by
  intro D X Y u u' Λ Λ' hΛ hΛ' p q hpq
  obtain ⟨n, n', xn, xn', hn, hn', hxn, hxn', -, hq1⟩ := rep_split Y hΛ hΛ' p q hpq
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hbl' : (Y.cs u').lamOf ((Y.cs u').base Λ') = Λ' := (Y.cs u').base_lam Λ' hΛ'
  obtain ⟨ha1, -, -⟩ := nilradical_conj_level' D X Y u ((Y.cs u).base Λ) xn n (by rw [hbl]; exact hn) hxn
  obtain ⟨ha1', -, -⟩ := nilradical_conj_level' D X Y u' ((Y.cs u').base Λ') xn' n' (by rw [hbl']; exact hn') hxn'
  set hb : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf)
  set hb' : X.B.I.Gf := ((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf)
  set a := (hb * X.xu u)⁻¹ * xn.2 * (hb * X.xu u) with hadef
  set a' := (hb' * X.xu u')⁻¹ * xn'.2 * (hb' * X.xu u') with ha'def
  have ga : Good X a := good_of_ncong X ha1.1 ⟨ha1.2.1, ha1.2.2.1⟩
  have ga' : Good X a' := good_of_ncong X ha1'.1 ⟨ha1'.2.1, ha1'.2.2.1⟩
  have hκK := termK_car (Y.cs u) (Y.cs u') hΛ hΛ' p
  have gκ := good_of_ncong X hκK
    (adm_norm_of_carrier (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') (Formalism.L2.SG.Pf.modGAt X) hΛ hΛ' p hκK)
  have hk : kOf X u u' hb hb' q.1.1 = a * kOf X u u' hb hb' p.1.1 * a' := by
    rw [hq1, hadef, ha'def]; simp only [kOf, Prod.snd_mul]; group

  have hlev : ∀ (w : D.what₂.Word) (Lw : Submodule (𝓞 D.host.E) (VS D).V) (hh : Hfin X w) (m : X.B.I.GA)
      (nm : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X m nm → nm ∈ NLam Lw (lf D (X.Fu w)) →
      ((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset →
      Good X (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) →
      levi Y.TR (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) = 1 := by
    intro w Lw hh m nm hm hnm hK gA
    obtain ⟨C, hC⟩ := Formalism.L2.SG.Pf.exists_goodC X w
    have hN0 := Formalism.L2.SG.Pf.nLamNfin_holds D X w Lw m nm hm hnm
    have hN1 := (Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X w hh⁻¹ m.2 hN0).1
    simp only [Subgroup.coe_inv, inv_inv] at hN1
    have e : ((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w) =
        (X.xu w)⁻¹ * ((hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf)) * X.xu w := by group
    have hK1 : (hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf) ∈ X.B.I.Kset := by
      have e2 : (hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf) =
          X.xu w * (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) * (X.xu w)⁻¹ := by group
      rw [e2]
      exact K_mul X.B.I (K_mul X.B.I (X.xu_K w) hK) (K_inv X.B.I (X.xu_K w))
    refine levi_eq_one_of Y.TR gA (fun j => ?_)
    rw [e]
    exact Formalism.L2.SG.Pf.cong_b hC hN1 hK1 j
  have hla := hlev u Λ ((Y.cs u).h ((Y.cs u).base Λ)) xn n hxn hn ha1.1 ga
  have hla' := hlev u' Λ' ((Y.cs u').h ((Y.cs u').base Λ')) xn' n' hxn' hn' ha1'.1 ga'
  show levi Y.TR (kOf X u u' hb hb' q.1.1) = levi Y.TR (kOf X u u' hb hb' p.1.1)
  rw [hk, levi_mul Y.TR (good_mul X ga gκ) ga', levi_mul Y.TR ga gκ, hla, hla', one_mul, mul_one]

theorem ampRepNC_holds : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC := by
  intro D X Y u u' Λ Λ' hΛ hΛ' p q hpq Ωp Ωq hΩp hΩq _
  obtain ⟨n, n', xn, xn', hn, hn', hxn, hxn', hq, hq1⟩ := rep_split Y hΛ hΛ' p q hpq
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hbl' : (Y.cs u').lamOf ((Y.cs u').base Λ') = Λ' := (Y.cs u').base_lam Λ' hΛ'
  obtain ⟨ha1, -, ha3⟩ := nilradical_conj_level' D X Y u ((Y.cs u).base Λ) xn n (by rw [hbl]; exact hn) hxn
  obtain ⟨ha1', -, ha3'⟩ := nilradical_conj_level' D X Y u' ((Y.cs u').base Λ') xn' n' (by rw [hbl']; exact hn') hxn'
  set hb : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf)
  set hb' : X.B.I.Gf := ((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf)
  set a := (hb * X.xu u)⁻¹ * xn.2 * (hb * X.xu u) with hadef
  set a' := (hb' * X.xu u')⁻¹ * xn'.2 * (hb' * X.xu u') with ha'def
  have hκK := termK_car (Y.cs u) (Y.cs u') hΛ hΛ' p
  have hκN := adm_norm_of_carrier (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') (Formalism.L2.SG.Pf.modGAt X)
    hΛ hΛ' p hκK
  have hk : kOf X u u' hb hb' q.1.1 = a * kOf X u u' hb hb' p.1.1 * a' := by
    rw [hq1, hadef, ha'def]; simp only [kOf, Prod.snd_mul]; group
  have haN : NCong X a := ⟨ha1.2.1, ha1.2.2.1⟩
  have haN' : NCong X a' := ⟨ha1'.2.1, ha1'.2.2.1⟩
  have hχ : chiN X (kOf X u u' hb hb' q.1.1) =
      X.psiFinU u xn.2 * chiN X (kOf X u u' hb hb' p.1.1) * X.psiFinU u' xn'.2 := by
    rw [hk, Formalism.L2.SG.Pf.ChiNMul.chiN_mul X (K_mul X.B.I ha1.1 hκK) (ncong_mul X ha1.1 haN hκN) haN',
      Formalism.L2.SG.Pf.ChiNMul.chiN_mul X ha1.1 haN hκN]
    have e1 := (ha3 1 Y.hK.1).1
    have e2 := (ha3' 1 Y.hK.1).1
    rw [mul_one, Formalism.L2.SG.Pf.ChiNMul.chiN_one, mul_one] at e1 e2
    rw [e1, e2]
  have hΩq' : Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' (n * p.1.2 * n')) Ωq := by
    rw [← hq]; exact hΩq
  have hoo := oo_rel Formalism.L2.SG.Pf.nLamNinf_holds chiTrivialC_outright Y hΛ hΛ' p hn hn' hxn hxn' hΩp hΩq'
  have hP1 := Formalism.L2.SG.Pf.psiProd_all D X u xn (ratLink_mem X hxn)
    (Formalism.L2.SG.Pf.nLamNinf_holds D X u _ xn n hxn hn) (Formalism.L2.SG.Pf.nLamNfin_holds D X u _ xn n hxn hn)
  have hP2 := Formalism.L2.SG.Pf.psiProd_all D X u' xn' (ratLink_mem X hxn')
    (Formalism.L2.SG.Pf.nLamNinf_holds D X u' _ xn' n' hxn' hn') (Formalism.L2.SG.Pf.nLamNfin_holds D X u' _ xn' n' hxn' hn')
  rw [hχ, hq1]
  rw [hoo, smul_smul]
  have hc : X.psiFinU u xn.2 * chiN X (kOf X u u' hb hb' p.1.1) * X.psiFinU u' xn'.2 *
      (X.psiInfU u xn.1 * X.psiInfU u' xn'.1) = chiN X (kOf X u u' hb hb' p.1.1) := by
    linear_combination (chiN X (kOf X u u' hb hb' p.1.1)) *
      (X.psiInfU u xn.1 * X.psiFinU u xn.2 * hP2 + hP1)
  rw [hc]

end Formalism.L2.SG.Pf
