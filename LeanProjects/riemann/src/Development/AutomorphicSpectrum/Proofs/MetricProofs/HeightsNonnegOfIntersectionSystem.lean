import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionPointHeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology NumberField
open GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def VanishesOnChart (W : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (t : Ω) : Prop :=
  ∃ (δ : K → ℕ) (G : MRing ι), IsMultiHomog G δ ∧ G ∈ W ∧ aeval y G = t * ∏ k, y ⟨k, c k⟩ ^ δ k

theorem prod_pow_add' (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ₁ δ₂ : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k = (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ ↦ by rw [Pi.add_apply, pow_add]

theorem xpow_notMem {W : Ideal (MRing ι)} (hW : W.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) (e : K → ℕ) : xpow c e ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).1 h
  exact hc k (hW.mem_of_pow_mem _ hk)

theorem vanishesOnChart_zero (W : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    VanishesOnChart W y c 0 :=
  ⟨0, 0, fun m hm ↦ by simp at hm, W.zero_mem, by simp⟩

theorem VanishesOnChart.add {W : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {a b : Ω}
    (ha : VanishesOnChart W y c a) (hb : VanishesOnChart W y c b) : VanishesOnChart W y c (a + b) := by
  classical
  obtain ⟨δ₁, e₁, h₁, m₁, v₁⟩ := ha
  obtain ⟨δ₂, e₂, h₂, m₂, v₂⟩ := hb
  refine ⟨δ₁ + δ₂, e₁ * xpow c δ₂ + e₂ * xpow c δ₁,
    isMultiHomog_add (isMultiHomog_mul h₁ (isMultiHomog_xpow c δ₂)) ?_,
    W.add_mem (W.mul_mem_right _ m₁) (W.mul_mem_right _ m₂), ?_⟩
  · rw [add_comm δ₁]
    exact isMultiHomog_mul h₂ (isMultiHomog_xpow c δ₁)
  · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_xpow, aeval_xpow, prod_pow_add']
    ring

theorem VanishesOnChart.mul_left {W : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {u t : Ω} (hu : u ∈ chartRingZ y c) (ht : VanishesOnChart W y c t) :
    VanishesOnChart W y c (u * t) := by
  obtain ⟨δ, e, h, m, v⟩ := ht
  obtain ⟨δ', e', h', v'⟩ := exists_form y c hc hu
  refine ⟨δ' + δ, e' * e, isMultiHomog_mul h' h, W.mul_mem_left _ m, ?_⟩
  rw [map_mul, v, v', prod_pow_add']
  ring

theorem not_vanishesOnChart_one {W : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}
    (hle : mCoordIdeal y ≤ W) (hW : W.IsPrime) (hcW : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) :
    ¬ VanishesOnChart W y c 1 := by
  classical
  rintro ⟨δ, G, hG, hm, hv⟩
  have h0 : G - xpow c δ ∈ mCoordIdeal y :=
    (mem_mCoordIdeal_iff y (isMultiHomog_sub hG (isMultiHomog_xpow c δ))).2
      (by rw [map_sub, hv, aeval_xpow, one_mul, sub_self])
  refine xpow_notMem hW hcW δ ?_
  have := W.sub_mem hm (hle h0)
  simpa using this

theorem exists_form_notMem {W : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}
    (hle : mCoordIdeal y ≤ W) (hW : W.IsPrime) (hcW : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {q : ℕ} {u v : Fin q → Ω} (hu : ∀ j, u j ∈ chartRingZ y c)
    (hv : ∀ j, v j ∈ chartRingZ y c) (h1 : ∑ j, u j * v j = 1) :
    ∃ (j : Fin q) (δ : K → ℕ) (g : MRing ι), IsMultiHomog g δ ∧ g ∉ W ∧
      aeval y g = v j * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  by_contra hno
  have hall : ∀ j, VanishesOnChart W y c (v j) := fun j ↦ by
    obtain ⟨δ, g, hg, hgv⟩ := exists_form y c hc (hv j)
    refine ⟨δ, g, hg, ?_, hgv⟩
    by_contra hn
    exact hno ⟨j, δ, g, hg, hn, hgv⟩
  have hs : VanishesOnChart W y c (∑ j, u j * v j) :=
    Finset.sum_induction _ (VanishesOnChart W y c) (fun _ _ ↦ VanishesOnChart.add)
      (vanishesOnChart_zero W y c) fun j _ ↦ VanishesOnChart.mul_left hc (hu j) (hall j)
  rw [h1] at hs
  exact not_vanishesOnChart_one hle hW hcW hs

theorem height_nonneg_of_forms {II : IntersectionSystem} (hII : IsIntersectionSystem II)
    {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {s : Ω} {W : Ideal (MRing ι)}
    (hW : IsArithVar W 1) (hPW : mCoordIdeal y ≤ W) (hA : IsSmoothHerm A) (hτ : 1 ≤ τ)
    (hs : s ∈ chartLatNm y A.a τ) (hsmall : IsSmallH (mCoordIdeal y) y A τ s)
    {G H : MRing ι} {dg dh : K → ℕ} (hG : IsMultiHomog G dg) (hH : IsMultiHomog H dh)
    (hdeg : ∀ k, (dg k : ℤ) = dh k + τ * A.a k) (hGH : aeval y G = s * aeval y H)
    (hGW : G ∉ W) (hHW : H ∉ W) : 0 ≤ II K ι W 1 ![A] := by
  classical
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set E := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.powLine A τ with hEdef
  have hE : IsSmoothHerm E := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_powLine hA τ
  set B := HermLine.sqMetric (ι := ι) dh with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric _
  have hEB : IsSmoothHerm (E.tensor B) := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor hE hB
  have hEBa : ∀ k, (E.tensor B).a k = (dg k : ℕ) := fun k ↦ by
    show E.a k + B.a k = _
    rw [hEdef, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.powLine_a, hdeg k]
    show _ + (dh k : ℤ) = _
    ring
  have hsecG : IsSectionOn W (E.tensor B) G := ⟨_, hEBa, hG, hGW⟩
  have hsecH : IsSectionOn W B H := ⟨_, fun k ↦ rfl, hH, hHW⟩
  have hRG := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hEB hEBa hG hGW
  have hRH := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hB (fun k ↦ rfl) hH hHW
  have hadd := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.inter_tensor (II K ι) hI hW hE hB
  have hpow := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.inter_powLine (II K ι) hI hW hA τ
  rw [recR_eq, GroundTheory.Heights₂.Heights.Inter.cycR_eq_vertR_of_dimOne GroundTheory.Heights₂.Heights.Inter.arithVarZero _ hW hsecG] at hRG
  rw [recR_eq, GroundTheory.Heights₂.Heights.Inter.cycR_eq_vertR_of_dimOne GroundTheory.Heights₂.Heights.Inter.arithVarZero _ hW hsecH] at hRH
  have hvert := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.vertR_le
    (GroundTheory.Heights₂.Heights.HilbertSamuel.SectionOrderAtPoint.proof K ι Ω y A.a τ s W G H dg dh hW hPW hs hG hH hdeg hGH hGW hHW)
  have harch : arInt W G (E.tensor B) (Fin.elim0 : Fin 0 → HermLine ι) ≤
      arInt W H B (Fin.elim0 : Fin 0 → HermLine ι) := by
    unfold arInt
    rw [GroundTheory.Heights₂.Heights.Inter.ptsIntegral_add_of_dimOne fibreFinite hW _ (g₁ := logNorm B H)
      (g₂ := fun z ↦ logNorm (E.tensor B) G z - logNorm B H z) fun z _ ↦ by ring]
    refine add_le_of_nonpos_right (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.ptsIntegral_nonpos W _ fun z hz ↦ ?_)
    show logNorm (E.tensor B) G z - logNorm B H z ≤ 0
    have hGz := norm_pos_iff.mpr (GroundTheory.Heights₂.Heights.Inter.eval_ne_zero_of_dimOne GroundTheory.Heights₂.Heights.Inter.arithVarZero hW hsecG hz)
    have hHz := norm_pos_iff.mpr (GroundTheory.Heights₂.Heights.Inter.eval_ne_zero_of_dimOne GroundTheory.Heights₂.Heights.Inter.arithVarZero hW hsecH hz)
    have hAz := A.pos z hz.1
    have hBz := B.pos z hz.1
    have hEz : E.h z = A.h z ^ τ := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.powLine_h A τ z
    have hEz0 : 0 < E.h z := hEz ▸ pow_pos hAz τ
    have hzP : z ∈ mcPts (mCoordIdeal y) := ⟨hz.1, fun f hf ↦ hz.2 f (hPW hf)⟩
    have hsm := hsmall dg dh G H z hG hH hdeg hGH hzP
    rw [← hEz] at hsm
    refine sub_nonpos.mpr (Real.log_le_log (div_pos hGz (mul_pos hEz0 hBz)) ?_)
    show _ / (E.h z * B.h z) ≤ _ / B.h z
    rw [div_le_div_iff₀ (mul_pos hEz0 hBz) hBz]
    nlinarith [mul_le_mul_of_nonneg_right hsm hBz.le]
  have hτI : 0 ≤ (τ : ℝ) * II K ι W 1 ![A] := by
    rw [← hpow]
    linarith
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
  exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hτI) hτ0

theorem heightsNonneg_of_smallGenerators :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (II : IntersectionSystem) (q : ℕ) (w : Fin q → Ω),
      IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
      (∀ j, w j ∈ chartLat y A.a 1) → KH.GeneratesOn y A.a w →
      (∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) → HeightsNonneg II (mCoordIdeal y) A := by
  intro K _ ι _ Ω _ y D A II q w hII _ _ hA hw hgen hsmall W hW hPW
  classical
  obtain ⟨hWp, -, hWr⟩ := hW.2.1
  choose c hcW using hWr
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k ↦ GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.coord_ne_zero fun h ↦ hcW k (hPW h)
  obtain ⟨u, hu, hsum⟩ := hgen c hyc
  have hv : ∀ j, w j * ∏ k, y ⟨k, c k⟩ ^ (-A.a k) ∈ chartRingZ y c := fun j ↦ by
    simpa using hw j c hyc
  obtain ⟨j, δ, g, hg, hgW, hgv⟩ := exists_form_notMem hPW hWp hcW hyc hu hv hsum
  have hGH := (chart_iff y c hyc A.a (w j) g δ).1 hgv
  have hmem : w j ∈ chartLatNm y A.a 1 := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.chartLat_le_chartLatNm y A.a 1 (hw j)
  refine height_nonneg_of_forms hII hW hPW hA le_rfl hmem (hsmall j)
    (isMultiHomog_mul hg (isMultiHomog_xpow c _)) (isMultiHomog_xpow c _) (fun k ↦ ?_) hGH ?_
    (xpow_notMem hWp hcW _)
  · have := Int.toNat_sub_toNat_neg (A.a k)
    simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one, one_mul]
    linarith
  · intro h
    rcases hWp.mem_or_mem h with h | h
    · exact hgW h
    · exact xpow_notMem hWp hcW _ h

end

end GlobalTheory.CompanionTheory.Ar.Giv
