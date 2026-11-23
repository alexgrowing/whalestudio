import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Formalism.LocalToGlobal.ProjectiveLattices.PhiSetPullSub
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PhiCLeNormalizedValuationProductFormAlgebraicStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaVal

theorem two_mul_le_of_card_div_le {N i : ℕ} {a p p' : ℝ} {v : EReal} (hN : N = 2 * 5 ^ 4 * i) (hp : p = p')
    (hv : (((N : ℝ) / ((5 : ℕ) : ℝ) ^ 4 * (a * p') : ℝ) : EReal) ≤ v) : ((2 * i * (a * p) : ℝ) : EReal) ≤ v := by
  have h5 : (N : ℝ) / ((5 : ℕ) : ℝ) ^ 4 = 2 * i := by
    rw [hN]; push_cast; ring
  rw [h5, ← hp] at hv
  exact hv

theorem val_at_partner {D : D7} {Q : Par D} (G : In66 Q) (hT : G.PinTower) (hL : G.PinLat) {j : ℕ} (h1 : 1 ≤ j)
    (h2 : j < D.R.m) (i : ℕ) (f : Rul (Q.Xo j) Q.c) (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ)
    (xs : J → Fin n → LatMod (Q.Dw j) (5 ^ 4)) (hcard : Nat.card (LevGrp (Q.Dw j) (5 ^ 4)) = 2 * 5 ^ 4 * i)
    (hsp : Spans xs) (hrule : IsEtaRule (Q.Xo j) Q.c 5 cf xs f) (la : HeightOneSpectrum (𝓞 Q.c.F))
    (y : PtV (Q.Xo j) Q.c (algCls (Q.Xo j) Q.c) (G.PY j (WeightAlgebra.resCh la)) (G.lies j la) la) :
    ((2 * i * ((eWL Q.c.F la : ℝ) * (G.P.loc (G.dat j) (WeightAlgebra.resCh la)).phiCy (imgV y)) : ℝ) : EReal) ≤ vAtV y f := by
  obtain ⟨S, io, e, ho, y', hy, eta, hl, hq⟩ := y.2
  have hi : imgV y = eta := congrArg Prod.snd hq
  have hf : vAtV y f = nval S.V e (evI y' f) := congrFun (congrArg Prod.fst hq) f
  rw [hi, hf]
  obtain ⟨z, hr, hz⟩ := hl h2
  obtain ⟨A, bA, hb, hv⟩ := GlobalTheory.T.phiC_le_normalized_valuation_product_form_algebraic D.host.E _ (Q.Dw j) _ (Q.Xo j) Q.c la
    (G.Tw j (WeightAlgebra.resCh la)) (hT j h1 h2 _ (resCh_prime la)) S io e y' z ho hy hz
    (fun x : D.host.E => D.host.conj x) (fun a => by
      apply D.host.φ₀.injective
      rw [NumberField.IsCMField.complexEmbedding_complexConj]
      exact WeightFamilies.emb_conj D _ a)
  have hphi := In66.phiCy_eq G hL h1 h2 ⟨S, io, e, y', ho, hy, hz⟩ hr A bA hb
  have key := hv 5 (by decide) (by norm_num) J n cf xs f hsp hrule
  exact two_mul_le_of_card_div_le hcard hphi key

theorem recPJ_phiC {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) (h2 : j < D.R.m)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la) :
    (recPJ h j hj).phiC la y =
      (eWL T.Q.c.F la : ℝ) * (T.G.P.loc (T.G.dat j) (WeightAlgebra.resCh la)).phiCy (imgV y) := by
  unfold WeightAlgebra.PJ.phiC
  rw [if_pos h2]
  rfl

theorem etVal_of_isEtaRule : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)) (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod (T.Q.Dw j) (5 ^ 4)), Nat.card (LevGrp (T.Q.Dw j) (5 ^ 4)) = 2 * 5 ^ 4 * i → Spans xs → IsEtaRule (T.Q.Xo j) T.Q.c 5 cf xs η.1 → EtVal h j ⟨h1, h2.le⟩ i η := by
  intro D T h j h1 h2 i η J _ n cf xs hcard hsp hrule la y
  have e1 := recPJ_vAt_inc h j ⟨h1, h2.le⟩ la y _ η
  have e2 := recPJ_phiC h ⟨h1, h2.le⟩ h2 la y
  have key := val_at_partner T.G h.tower h.lattice_condition h1 h2 i η.1 J n cf xs hcard hsp hrule la y
  rw [← e2, ← e1] at key
  exact key

end GlobalTheory.EtaVal
