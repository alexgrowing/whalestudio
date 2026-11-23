import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfDetSymSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierRatioLocalNorm

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped Classical

namespace GlobalTheory.DetMet

theorem pn_prod {D : D7} (O : Setup D) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ)
    (G : EigMet O.s.T.Z (embOf O.κ.e σ)) {ι : Type} [Fintype ι] (n : ι → Letter O.S.Dw → ℤ) :
    (cxSt _).pn _ σ _ ((O.Φ.C c).met G (∑ i, n i))
      ((cxSt _).cx _ σ (((∏ i, eqn (divOf (O.Φ.C c) (n i)) (under z) : (O.var c).Fnˣ) : (O.var c).Fn)⁻¹)) z =
      ∏ i, (cxSt _).pn _ σ _ ((O.Φ.C c).met G (n i))
        ((cxSt _).cx _ σ (genAt (divOf (O.Φ.C c) (n i)) (under z))) z := by
  have hA := OmCx.prod_isEqn O c (under z) Finset.univ n
  rw [← Units.val_inv_eq_inv_val]
  exact (Var.pn_frame hA).trans ((OmCx.prod_h O c σ z G Finset.univ n).trans
    (Finset.prod_congr rfl fun i _ => (Var.pn_frame (Base.isEqn_eqn _ _)).symm))

theorem lnRatio_sum {D : D7} (O : Setup D) (h : O.Core) (c : O.s.Comp) (R : Option ℝ) (σ : D.what₂.LL →+* ℂ)
    (z : Pts (O.var c) σ) {ι : Type} [Fintype ι] (n : ι → Letter O.S.Dw → ℤ) :
    lnRatio (O.met.hm c R σ (∑ i, n i)) (O.met.h0 c σ (∑ i, n i)) z =
      ∑ i, lnRatio (O.met.hm c R σ (n i)) (O.met.h0 c σ (n i)) z := by
  have hA := OmCx.prod_isEqn O c (under z) Finset.univ n
  have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 hA
  rw [lnRatio_eq hgen (h.posAt_hm c σ R _ z) (h.referenceMetric_posAt c σ _ z)]
  have p1 : ∀ i, 0 < (cxSt _).pn _ σ _ (O.met.hm c R σ (n i))
      ((cxSt _).cx _ σ (genAt (divOf (O.Φ.C c) (n i)) (under z))) z := fun i => h.posAt_hm c σ R (n i) z
  have p0 : ∀ i, 0 < (cxSt _).pn _ σ _ (O.met.h0 c σ (n i))
      ((cxSt _).cx _ σ (genAt (divOf (O.Φ.C c) (n i)) (under z))) z := fun i => h.referenceMetric_posAt c σ (n i) z
  obtain ⟨xa, P, hc⟩ := h
  have k1 : (cxSt _).pn _ σ _ (O.met.hm c R σ (∑ i, n i))
      ((cxSt _).cx _ σ (((∏ i, eqn (divOf (O.Φ.C c) (n i)) (under z) : (O.var c).Fnˣ) : (O.var c).Fn)⁻¹)) z =
      ∏ i, (cxSt _).pn _ σ _ (O.met.hm c R σ (n i))
        ((cxSt _).cx _ σ (genAt (divOf (O.Φ.C c) (n i)) (under z))) z := by
    rw [hc.hm_eq]
    exact pn_prod O c σ z (xa.eigMetAt (embOf O.κ.e σ) R) n
  have k0 : (cxSt _).pn _ σ _ (O.met.h0 c σ (∑ i, n i))
      ((cxSt _).cx _ σ (((∏ i, eqn (divOf (O.Φ.C c) (n i)) (under z) : (O.var c).Fnˣ) : (O.var c).Fn)⁻¹)) z =
      ∏ i, (cxSt _).pn _ σ _ (O.met.h0 c σ (n i))
        ((cxSt _).cx _ σ (genAt (divOf (O.Φ.C c) (n i)) (under z))) z := by
    rw [hc.h0_eq]
    exact pn_prod O c σ z (xa.eigMet (embOf O.κ.e σ)) n
  simp only [lnRatio, lnN]
  rw [k1, k0, Real.log_prod fun i _ => (p1 i).ne', Real.log_prod fun i _ => (p0 i).ne', Finset.sum_sub_distrib,
    Finset.sum_div, Finset.sum_div]

theorem expo_det {D : D7} (O : Setup D) (a : ℕ → Bool) (R : Option ℝ) (τ : D.what₂.Tau) :
    expo O.S.Dw (detSym O.S.Dw a R (DV.tauEmb D τ)) = ∑ i : Fin O.N, O.ex (τ, i) := by
  unfold detSym
  rw [OmCx.expo_finset_sum, O.S.rank_eq, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => expo_rootSym _ _ _ _ _

theorem det_metric : ∀ (D : D7) (O : Setup D), O.Core → ∀ (a : ℕ → Bool) (c : O.s.Comp) (τ : D.what₂.Tau) (b : (O.var c).X),
    IsClosed ({b} : Set (O.var c).X) → (O.Φ.C c).π b ∉ GlobalTheory.Toroidal.genBd O.s.T.Z →
    (adlOf (O.Φ.C c) (O.met.hm c) (detSym O.S.Dw a none (DV.tauEmb D τ))).ht b =
      (O.adl0 c (detSym O.S.Dw a none (DV.tauEmb D τ))).ht b + (∑ σ : D.what₂.LL →+* ℂ, ∑ᶠ (z : Pts (O.var c) σ) (_ : under z = b),
          O.chg c none (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ z) /
        ((Module.finrank ℚ D.what₂.LL : ℝ) * (Nat.card {y : AlgPt (O.var c) // below y.1 = b} : ℝ)) := by
  intro D O h a c τ b hb _
  have key := ht_adlOf_eq (O.Φ.C c) (O.met.hm c) (O.met.h0 c) _ (PlaceBd.parOf_detSym a (DV.tauEmb D τ))
    (expo_det O a none τ) hb
  have hz (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ) :
      O.chg c none (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ z =
        (-1 : ℝ) * lnRatio (O.met.hm c none σ (∑ i : Fin O.N, O.ex (τ, i))) (O.met.h0 c σ (∑ i : Fin O.N, O.ex (τ, i))) z := by
    rw [lnRatio_sum O h c none σ z fun i : Fin O.N => O.ex (τ, i), Setup.chg, Fintype.sum_prod_type,
      Finset.sum_eq_single τ (fun σ' _ hne => by simp [hne]) (fun hh => (hh (Finset.mem_univ _)).elim), Finset.mul_sum]
    simp
  simp only [hz, finsum_under_mul _ hb, ← Finset.mul_sum]
  rw [key, Setup.adl0]
  ring

end GlobalTheory.DetMet
