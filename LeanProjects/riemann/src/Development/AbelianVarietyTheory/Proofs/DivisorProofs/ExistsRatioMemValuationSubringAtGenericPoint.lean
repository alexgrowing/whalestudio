import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.Adelic.LinSys

theorem exists_ratio_mem_of_point {F K : Type} [Field F] [Field K] (S : LinSys F) (hS : S.IsVariety) (r e : ℕ)
    (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (hcov : ∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i)))
    (x : Sp K ⟶ S.Y) (V : ValuationSubring K) (hV : ∀ c, S.baseHom x c ∈ V) :
    ∃ i, S.val x (S.comb (u i)) ≠ 0 ∧ S.powVal x th / S.val x (S.comb (u i)) ^ e ∈ V := by
  have hpr : IsProper S.str := GlobalTheory.CommonModel.isProper_of_isProjOver hS.proj
  let φ : F →+* V := (S.baseHom x).codRestrict V hV
  have hsq : x ≫ S.str = specAlgebraMap V K ≫ spMap φ := by
    rw [S.comp_str x, ← Spec.map_comp]
    rfl
  obtain ⟨l, hl, -⟩ := exists_valuativeExtension S.str (spMap φ) x hsq
  have hx : spMap (algebraMap V K) ≫ l = x := hl
  obtain ⟨i, hi⟩ := hcov (l (IsLocalRing.closedPoint V))
  have hyc := S.mem_chartAt (l (IsLocalRing.closedPoint V))
  set c := S.chartAt (l (IsLocalRing.closedPoint V))
  have hU : ⊤ ≤ l ⁻¹ᵁ S.L.U c := (GlobalTheory.ZH.CrdCalc.top_le_iff l _).2 hyc
  have hB : ⊤ ≤ l ⁻¹ᵁ S.Y.basicOpen ((S.comb (u i)).f c) :=
    (GlobalTheory.ZH.CrdCalc.top_le_iff l _).2 ((mem_nonzeroLocus_iff_basicOpen _ hyc).1 hi)
  obtain ⟨w, hw⟩ := (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff l _ hU _).2 hB
  obtain ⟨hU', hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap V K) l _ hU
  rw [hx] at hU' hval
  obtain ⟨c₀, hc₀, h₁, h₂⟩ := S.exists_frame_change x c ((le_iff_ptOf_mem x _).1 hU')
  have ha := (h₁ (S.comb (u i))).symm.trans (hval _)
  have ht := (h₂ e th).symm.trans (hval _)
  rw [← hw] at ha
  have hw₀ : algebraMap V K (w : V) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 w.ne_zero
  have hv : S.val x (S.comb (u i)) ≠ 0 := fun h => hw₀ (by rw [← ha, h, mul_zero])
  refine ⟨i, hv, ?_⟩
  have key : S.powVal x th / S.val x (S.comb (u i)) ^ e =
      algebraMap V K (valR l _ (Twist.zfun th c) * ((w⁻¹ : Vˣ) : V) ^ e) := by
    have hinv : algebraMap V K ((w⁻¹ : Vˣ) : V) = (algebraMap V K (w : V))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    rw [map_mul, map_pow, ← ht, hinv, ← ha, zpow_natCast]
    rw [inv_pow, mul_pow]
    field_simp
  rw [key]
  exact (valR l _ (Twist.zfun th c) * ((w⁻¹ : Vˣ) : V) ^ e).2

theorem exists_ratio_mem_valuationSubring : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∀ η : S.Y, IsGenericPoint η Set.univ → ∀ V : ValuationSubring (S.Y.residueField η), (∀ c, S.baseHom (resPt η) c ∈ V) → ∃ i, S.val (resPt η) (S.comb (u i)) ≠ 0 ∧ S.powVal (resPt η) th / S.val (resPt η) (S.comb (u i)) ^ e ∈ V :=
  fun _ _ S hS r e u th hcov η _ V hV => exists_ratio_mem_of_point S hS r e u th hcov (resPt η) V hV

end GlobalTheory.Adelic.LinSys
