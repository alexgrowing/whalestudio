import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteThetaDatumNeZeroFrameAdjointSpec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LevelSupport

open GlobalTheory.IdemModTwo GlobalTheory.SplitHecke GlobalTheory.ThetaSupport

variable {D : D7}

theorem exists_val_ge {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (hB : ∀ i k, w (B i k) ≤ 1)
    (hBA : ∀ i k, w ((B * A) i k - if i = k then 1 else 0) < 1) (d : Fin n → K) (j : Fin n) (hj : d j ≠ 0)
    (hd : ∀ i, w (d i) ≤ w (d j)) : ∃ i, w (d j) ≤ w ((A *ᵥ d) i) := by
  by_contra h
  push Not at h
  have h0 : w (d j) ≠ 0 := (Valuation.ne_zero_iff _).2 hj
  have h1 := val_row_lt w ((B * A) j) d j hj hd (hBA j)
  have e1 : (B * A) j ⬝ᵥ d = B j ⬝ᵥ (A *ᵥ d) := by
    change ((B * A) *ᵥ d) j = (B *ᵥ (A *ᵥ d)) j
    rw [Matrix.mulVec_mulVec]
  have h2 : w ((B * A) j ⬝ᵥ d) < w (d j) := by
    rw [e1]
    refine Valuation.map_sum_lt _ h0 fun i _ => ?_
    rw [Valuation.map_mul]
    exact (mul_le_of_le_one_left' (hB j i)).trans_lt (h i)
  have h3 := Valuation.map_sub w ((B * A) j ⬝ᵥ d) ((B * A) j ⬝ᵥ d - d j)
  rw [sub_sub_cancel] at h3
  exact lt_irrefl _ (h3.trans_lt (max_lt h2 h1))

set_option maxHeartbeats 2000000 in
open Classical in

theorem exists_sum_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (S T : HSp D)
    (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) {e : AE D} {PP : Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) (c : Fin T.rank → AE D) (hc : ∃ i, e * c i ≠ 0) (hr : T.rank ≤ S.rank) :
    ∃ (n : ℕ) (l : Fin n → Fin S.rank → AE D), 0 < n ∧ (∀ k a, e * l k a = l k a) ∧
      ∀ t, IsIntM (frMapAdj S T βS βT t) → IsUnit (topL T.rank (redM PP (frMapAdj S T βS βT t))).det →
        ∑ k, ψ (symplO S T t (vecMulVec c (l k))) = 0 := by
  haveI : Fintype (kP PP) := Fintype.ofFinite _
  obtain ⟨v, hv⟩ := (isSplitIdem_iff e).1 he.1
  have hπ := GlobalTheory.SplitChart.chart_comp hv
  set π := GlobalTheory.SplitChart.comp hv with hπdef
  obtain ⟨φ, hφ, hres⟩ := exists_chart_levels he hπ
  obtain ⟨x, hx, hx'⟩ := exists_edge hψ v
  obtain ⟨hi, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP he
  have hint : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, Valued.v (φ s) ≤ 1 := fun s => by
    obtain ⟨a, ha⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) s
    rw [← ha, hφ]
    refine isInt_Ov.1 ((hπ.2.2.2 a).1 (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_))
    rw [RingHom.map_mul, ha]
    exact mul_mem hi s.2
  have hx0 : Valued.v x ≠ 0 := fun h => by
    rw [map_eq_zero] at h
    have := psiV_natCast ψ hv 0 x
    rw [Nat.cast_zero, zero_mul, pow_zero, ← h] at this
    exact hx this
  let d : Fin T.rank → Fv D.host.F v := (βT⁻¹).val.map φ *ᵥ (π ∘ c)
  have hd : βT.val.map φ *ᵥ d = π ∘ c := by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ φ.map_zero φ.map_one, Matrix.one_mulVec]
  obtain ⟨i₀, hi₀⟩ := hc
  obtain ⟨j, -, hj⟩ := Finset.univ.exists_max_image (fun i => Valued.v (d i)) ⟨i₀, Finset.mem_univ _⟩
  have hj0 : d j ≠ 0 := fun h => by
    have h0 : d = 0 := funext fun i => by
      have := hj i (Finset.mem_univ _)
      rwa [h, map_zero, le_zero_iff, map_eq_zero] at this
    rw [h0, Matrix.mulVec_zero] at hd
    exact hi₀ ((hπ.2.1 _).1 (congrFun hd i₀).symm)
  have hdj : Valued.v (d j) ≠ 0 := (Valuation.ne_zero_iff _).2 hj0
  have hξ : π (incA D D.host.xi0) ≠ 0 :=
    (_root_.map_ne_zero (π.comp (incA D))).2 (GlobalTheory.IndefiniteRowSideFullHecke.BesselData.embedding_xi_zero_ne_zero D)
  let rep : kP PP → 𝓞 D.host.E := fun κ => (Ideal.Quotient.mk_surjective κ).choose
  have hrep : ∀ κ, Ideal.Quotient.mk PP.asIdeal (rep κ) = κ := fun κ => (Ideal.Quotient.mk_surjective κ).choose_spec
  let b : kP PP → Fv D.host.F v := fun κ => φ (oToS D.host.F D.host.E (rep κ))
  have hb1 : ∀ κ, Valued.v (b κ) ≤ 1 := fun κ => hint _
  have hbres : ∀ (s : Formalism.L2.Herm.intAf D.host.F D.host.E) κ, resS D.host.F PP s = κ → Valued.v (φ s - b κ) < 1 := by
    intro s κ h
    have := hres (s - oToS D.host.F D.host.E (rep κ)) (by rw [map_sub, Formalism.L2.DIV.resS_oToS, hrep, h, sub_self])
    rwa [AddSubgroupClass.coe_sub, RingHom.map_sub] at this
  have hb0 : Valued.v (b 0) < 1 := by
    have := hbres 0 0 (map_zero _)
    rwa [ZeroMemClass.coe_zero, map_zero, zero_sub, Valuation.map_neg] at this
  have hbadd : ∀ κ κ', Valued.v (b (κ + κ') - b κ - b κ') < 1 := by
    intro κ κ'
    have := hbres (oToS D.host.F D.host.E (rep κ) + oToS D.host.F D.host.E (rep κ')) (κ + κ') (by
      rw [map_add, Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_oToS, hrep, hrep])
    rw [AddMemClass.coe_add, RingHom.map_add] at this
    rw [← Valuation.map_neg, show -(b (κ + κ') - b κ - b κ') = b κ + b κ' - b (κ + κ') by ring]
    exact this
  have he1 : π e = 1 := by
    have := (hπ.2.1 (1 - e)).2 (by rw [mul_sub, mul_one, hv.1, sub_self])
    rwa [map_sub, map_one, sub_eq_zero, eq_comm] at this
  have hdense : ∀ y : Fv D.host.F v, Valued.v y ≤ 1 → ∃ κ, Valued.v (b κ - y) < 1 := by
    intro y hy
    obtain ⟨a, rfl⟩ := hπ.1 y
    have hw : finPart D (e * a) ∈ intAE D := (hπ.2.2.2 a).2 (isInt_Ov.2 hy)
    let s : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨toEAf D (e * a), GlobalTheory.IdemRes.toEAf_mem_of_finPart hw⟩
    refine ⟨resS D.host.F PP s, ?_⟩
    have h1 := hbres s _ rfl
    have h2 : φ s = π a := by
      change φ (toEAf D (e * a)) = π a
      rw [hφ, map_mul, he1, one_mul]
    rw [← Valuation.map_neg, neg_sub, ← h2]
    exact h1

  let s : Fv D.host.F v := -(x / (π (incA D D.host.xi0) * d j))
  choose l₀ hl₀ using fun (κ : Fin T.rank → kP PP) (a : Fin S.rank) =>
    hπ.1 (s * ∑ i, b (κ i) * φ ((βS⁻¹).val (Fin.castLE hr i) a))
  let eqv := Fintype.equivFin (Fin T.rank → kP PP)
  refine ⟨Fintype.card (Fin T.rank → kP PP), fun k a => e * l₀ (eqv.symm k) a, Fintype.card_pos,
    fun k a => by rw [← mul_assoc, hv.1], fun t ht ht' => ?_⟩
  set U := (frMapAdj S T βS βT t).map φ with hUdef
  have hU : U = (βS⁻¹).val.map φ * (adj S T t).map π * βT.val.map φ := by
    have : (adj S T t).map π = ((adj S T t).map (toEAf D)).map φ := Matrix.ext fun a b => (hφ _).symm
    rw [this, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  let z : Fin T.rank → Fv D.host.F v := fun i => (U *ᵥ d) (Fin.castLE hr i)
  have hUint : ∀ a b, Valued.v (U a b) ≤ 1 := fun a b => hint ⟨_, ht a b⟩
  have hz : ∀ i, Valued.v (z i) ≤ Valued.v (d j) := fun i => by
    show Valued.v (∑ k, U (Fin.castLE hr i) k * d k) ≤ _
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [Valuation.map_mul]
    exact (mul_le_of_le_one_left' (hUint _ _)).trans (hj k (Finset.mem_univ _))
  have hpair : ∀ κ, ψ (symplO S T t (vecMulVec c fun a => e * l₀ κ a)) =
      psiV D.host.F ψ v (x / d j * ∑ i, b (κ i) * z i) := by
    intro κ
    have h1 : π (l₀ κ ⬝ᵥ adj S T t *ᵥ c) = s * ∑ i, b (κ i) * z i := by
      have h3 : π ∘ (adj S T t *ᵥ c) = (adj S T t).map π *ᵥ (π ∘ c) := funext fun a => RingHom.map_mulVec π _ _ a
      have h4 : U *ᵥ d = (βS⁻¹).val.map φ *ᵥ ((adj S T t).map π *ᵥ (π ∘ c)) := by
        rw [hU, ← Matrix.mulVec_mulVec, hd, ← Matrix.mulVec_mulVec]
      simp only [z, h4]
      rw [RingHom.map_dotProduct, h3]
      generalize (adj S T t).map π *ᵥ (π ∘ c) = w
      simp only [dotProduct, Matrix.mulVec, Function.comp_apply, hl₀, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul,
        mul_assoc]
      exact Finset.sum_comm
    rw [symplO_vecMulVec, char_trace ψ hv, ← hπdef, RingHom.map_neg, RingHom.map_mul, h1]
    congr 1
    simp only [s]
    field_simp

  have hsmall : ∀ w', Valued.v w' < Valued.v (d j) → psiV D.host.F ψ v (x / d j * w') = 1 := fun w' h => by
    refine hx' _ ?_
    have : x / d j * w' = x * (w' / d j) := by ring
    rw [this, Valuation.map_mul, map_div₀]
    exact mul_lt_of_lt_one_right (zero_lt_iff.2 hx0) ((div_lt_one₀ (zero_lt_iff.2 hdj)).2 h)
  have hterm : ∀ y i, Valued.v y < 1 → Valued.v (y * z i) < Valued.v (d j) := fun y i h => by
    rw [Valuation.map_mul]
    exact (mul_le_mul_right (hz i) _).trans_lt (mul_lt_of_lt_one_left (zero_lt_iff.2 hdj) h)
  let χ : AddChar (Fin T.rank → kP PP) ℂ :=
    { toFun := fun κ => psiV D.host.F ψ v (x / d j * ∑ i, b (κ i) * z i)
      map_zero_eq_one' := hsmall _ (Valuation.map_sum_lt _ hdj fun i _ => hterm _ i hb0)
      map_add_eq_mul' := fun κ κ' => by
        change psiV D.host.F ψ v (x / d j * ∑ i, b ((κ + κ') i) * z i) =
          psiV D.host.F ψ v (x / d j * ∑ i, b (κ i) * z i) * psiV D.host.F ψ v (x / d j * ∑ i, b (κ' i) * z i)
        rw [← psiV_add ψ hv, ← mul_add, ← Finset.sum_add_distrib]
        have e2 : ∑ i, b ((κ + κ') i) * z i = ∑ i, (b (κ i) * z i + b (κ' i) * z i) +
            ∑ i, (b (κ i + κ' i) - b (κ i) - b (κ' i)) * z i := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.add_apply]
          ring
        rw [e2, mul_add, psiV_add ψ hv, hsmall _ (Valuation.map_sum_lt _ hdj fun i _ => hterm _ i (hbadd _ _)), mul_one] }

  have hAB := Matrix.nonsing_inv_mul _ ht'
  set Ab := topL T.rank (redM PP (frMapAdj S T βS βT t)) with hAb
  let A : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v) := fun i k => U (Fin.castLE hr i) k
  let B : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v) := fun i k => b (Ab⁻¹ i k)
  have hBA : ∀ i k, Valued.v ((B * A) i k - if i = k then 1 else 0) < 1 := by
    intro i k
    let σ : Formalism.L2.Herm.intAf D.host.F D.host.E :=
      ∑ m, oToS D.host.F D.host.E (rep (Ab⁻¹ i m)) * ⟨frMapAdj S T βS βT t (Fin.castLE hr m) k, ht _ _⟩ -
        (if i = k then 1 else 0)
    have hσ : resS D.host.F PP σ = 0 := by
      have h1 := congrFun (congrFun hAB i) k
      rw [Matrix.mul_apply, Matrix.one_apply] at h1
      simp only [σ, map_sub, map_sum, map_mul, Formalism.L2.DIV.resS_oToS, hrep]
      rw [sub_eq_zero, apply_ite (resS D.host.F PP), map_one, map_zero, ← h1]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hAb, topL, dif_pos ⟨(Fin.castLE hr m).2, k.2⟩, redM, dif_pos (ht _ _)]
      rfl
    have h2 := hres σ hσ
    convert h2 using 2
    simp only [σ, AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, RingHom.map_sub,
      map_sum, RingHom.map_mul]
    rw [Matrix.mul_apply]
    congr 1
    split_ifs <;> simp
  obtain ⟨i₁, hi₁⟩ := exists_val_ge Valued.v A B (fun i k => hb1 _) hBA d j hj0 (fun i => hj i (Finset.mem_univ _))
  have hzi : Valued.v (z i₁) = Valued.v (d j) := le_antisymm (hz i₁) hi₁
  have hz0 : z i₁ ≠ 0 := fun h => hdj (by rw [← hzi, h, map_zero])
  obtain ⟨κ₀, hκ₀⟩ := hdense (d j / z i₁) (by rw [map_div₀, hzi, div_self hdj])
  have hχ : χ ≠ 1 := by
    intro h
    have h1 : χ (Pi.single i₁ κ₀ : Fin T.rank → kP PP) = 1 := by rw [h, AddChar.one_apply]
    have e3 : ∑ i, b ((Pi.single i₁ κ₀ : Fin T.rank → kP PP) i) * z i = d j + ∑ i, (b ((Pi.single i₁ κ₀ : Fin T.rank → kP PP) i) * z i - if i = i₁ then d j else 0) := by
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      ring
    have hw : Valued.v (∑ i, (b ((Pi.single i₁ κ₀ : Fin T.rank → kP PP) i) * z i - if i = i₁ then d j else 0)) < Valued.v (d j) := by
      refine Valuation.map_sum_lt _ hdj fun i _ => ?_
      by_cases hi : i = i₁
      · subst hi
        rw [if_pos rfl, Pi.single_eq_same]
        have : b κ₀ * z i - d j = (b κ₀ - d j / z i) * z i := by field_simp
        rw [this, Valuation.map_mul, ← hzi]
        exact mul_lt_of_lt_one_left (zero_lt_iff.2 (hzi ▸ hdj)) hκ₀
      · rw [if_neg hi, sub_zero, Pi.single_eq_of_ne hi]
        exact hterm _ i hb0
    change psiV D.host.F ψ v (x / d j * ∑ i, b ((Pi.single i₁ κ₀ : Fin T.rank → kP PP) i) * z i) = 1 at h1
    rw [e3, mul_add, div_mul_cancel₀ x hj0, psiV_add ψ hv, hsmall _ hw, mul_one] at h1
    exact hx h1
  rw [← (Equiv.sum_comp eqv.symm (fun κ => χ κ)).trans (AddChar.sum_eq_zero_of_ne_one hχ)]
  exact Finset.sum_congr rfl fun k _ => hpair _

set_option maxHeartbeats 1000000 in
open Classical in

theorem exists_sum_heisO_eq_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {LT : LevDat D.host.E ℂ T.rank}
    {Q : Finset (Pl D.host.E)} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hr : T.rank ≤ S.rank) {PP : Pl D.host.E} (hPP : PP ∈ LT.Pg)
    (h : IsLevelVec ψ θ S T sT ΛS ΛT βS βT LT Q m f₀ f)
    (c : Fin T.rank → AE D) (hc : ∀ e, IsSplitIdem D e → ∃ i, e * c i ≠ 0) :
    ∃ (n : ℕ) (l : Fin n → Fin S.rank → AE D), 0 < n ∧ (∀ k, (vecMulVec c (l k)).map (infPart D) = 0) ∧
      ∑ k, heisO ψ S T (vecMulVec c (l k)) f = 0 := by
  obtain ⟨hv, e, he, ⟨Tm, hTm⟩, hall⟩ := h
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hinf := ho.conj.infPart_eq
  have hSB := GlobalTheory.PlaceVec.isSBHalf_of_red hS.1 hT.1 hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
    (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) (LT.Pg ∪ Q)
    (fun y => omegaG LT m y * omegaQ Q T.rank m (-1) y) fun y y' h => by
      rw [GlobalTheory.PlaceDatum.omegaG_congr LT m y y' fun PP hPP => h PP (Finset.mem_union_left _ hPP),
        GlobalTheory.PlaceVec.omegaQ_congr Q _ m _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)]
  obtain ⟨⟨es, h1, h2⟩, -⟩ := he
  have hP := Finset.mem_union_left Q hPP
  have h3 : es PP * ∑ j ∈ LT.Pg ∪ Q, es j = es PP :=
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij =>
      (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h =>
        hij (GlobalTheory.PlaceVec.isIdemAt_inj (h1 j hj) (h ▸ h1 i hi))) hP
  rw [← h2] at h3
  obtain ⟨n, l, hn, hl, hsum⟩ := exists_sum_zero hv.1.1 S T βS βT (h1 PP hP) c (hc _ (h1 PP hP).1) hr
  have hhalf : ∀ k, IsHalf e (vecMulVec c (l k)) := fun k i j => by
    rw [vecMulVec_apply, ← hl k j]
    linear_combination (c i * l k j) * h3
  refine ⟨n, l, hn, fun k => Matrix.ext fun i j => by
    rw [Matrix.map_apply, ← hhalf k i j, RingHom.map_mul, ho.infPart_eq, zero_mul]; rfl, ?_⟩
  have hk : ∀ k, heisO ψ S T (vecMulVec c (l k)) f =
      Tm (fun t => ψ (symplO S T t (vecMulVec c (l k))) * GlobalTheory.FinZeta.levDatum S T βS βT LT Q m e t) := fun k => by
    rw [hall Tm hTm, ← hTm.modul _ hSB _ (by rw [GlobalTheory.LatVac.cA_cA]; exact hhalf k)]
    rfl
  rw [Finset.sum_congr rfl fun k _ => hk k, ← map_sum]
  have hz : (∑ k, fun t => ψ (symplO S T t (vecMulVec c (l k))) * GlobalTheory.FinZeta.levDatum S T βS βT LT Q m e t) = 0 := by
    funext t
    rw [Finset.sum_apply, ← Finset.sum_mul, Pi.zero_apply]
    by_cases h0 : GlobalTheory.FinZeta.levDatum S T βS βT LT Q m e t = 0
    · rw [h0, mul_zero]
    · obtain ⟨-, hI, hU, -⟩ := GlobalTheory.FinZeta.levDatum_ne_zero_spec S T βS βT LT Q m e t h0
      rw [hsum t hI (hU PP (Or.inl hPP)), zero_mul]
  rw [hz, map_zero]

theorem sum_heisO_along_eq_zero_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m om BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m om BW f₀ f c io → ∀ Q h g ξ, IsoVec (Wc D i) ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin (Vc D i).rank → AE D, ∑ k, heisO R.ψ (Vc D i) (Wc D i) (along (Vc D i) (Wc D i) ξ (a k)) (om (h, g) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ BW f Q)) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m om BW f₀ f c io hD Q h g ξ hξ
  obtain ⟨hcore, -, -, -, -, hω, -, hlv, hpt, -, -⟩ := hD
  have hL := hcore.lev
  have hθ : IsInfFam R.θ := hcore.models.inf
  obtain ⟨PP, hPP⟩ := exists_mem_Pg hL
  let c' : Fin (Wc D i).rank → AE D := Formalism.L2.Theta.mt (Wc D i) g⁻¹ *ᵥ fun a => incA D (ξ a)
  have hc : Formalism.L2.Theta.mt (Wc D i) g *ᵥ c' = fun a => incA D (ξ a) := by
    rw [Matrix.mulVec_mulVec, mt_mul_inv, Matrix.one_mulVec]
  obtain ⟨n, l, hn, hl0, hl⟩ := exists_sum_heisO_eq_zero
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) hPP hlv c' fun e he => by
      by_contra hn
      push Not at hn
      obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
      refine hξ.1 (funext fun a => ?_)
      refine (map_eq_zero (π.comp (incA D))).1 ?_
      rw [RingHom.comp_apply, ← congrFun hc a, RingHom.map_mulVec]
      have : π ∘ c' = 0 := funext fun b => (hπ.2.1 _).2 (hn b)
      rw [this, Matrix.mulVec_zero]
      rfl
  refine ⟨n, hn, fun k => l k ᵥ* Formalism.L2.Theta.mt (Vc D i) h⁻¹, ?_⟩
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := by
    have := hpt 1
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt, GlobalTheory.FiniteFock.pureTensorO_one] at this
  have htr := GlobalTheory.FinTranslate.finite_translate D R.ψ R.θ _ _ hω.std hθ _ hf
  have key : ∀ k, heisO R.ψ (Vc D i) (Wc D i) (along (Vc D i) (Wc D i) ξ (l k ᵥ* Formalism.L2.Theta.mt (Vc D i) h⁻¹))
      (om (h, g) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ BW f Q)) =
      om (h, g) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ BW (heisO R.ψ (Vc D i) (Wc D i) (vecMulVec c' (l k)) f) Q) := fun k => by
    have h1 : along (Vc D i) (Wc D i) ξ (l k ᵥ* Formalism.L2.Theta.mt (Vc D i) h⁻¹) =
        actO (Vc D i) (Wc D i) h g (vecMulVec c' (l k)) := by
      rw [actO, Matrix.mul_vecMulVec, hc, Matrix.vecMulVec_mul, along]
    rw [h1, ← hω.om_heis h g _ _ (hpt Q)]
    refine congrArg _ ?_
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt, ((htr.2 _ (hl0 k)).2)]
  rw [Finset.sum_congr rfl fun k _ => key k, ← map_sum]
  have hs := GlobalTheory.SpecFac.pureTensorO_sum hω.std hθ (fun _ => 1) (R.BV i) (cart (R.MW i σ)) BW Finset.univ
    (fun _ => (1 : ℂ)) (fun k => heisO R.ψ (Vc D i) (Wc D i) (vecMulVec c' (l k)) f) (fun k _ => (htr.2 _ (hl0 k)).1) Q
  simp only [one_smul] at hs
  have h0 := GlobalTheory.FiniteFock.pureTensorO_smul R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW 0 0 Q
  rw [zero_smul, zero_smul] at h0
  change om (h, g) (∑ k, Datum.pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW
    (heisO R.ψ (Vc D i) (Wc D i) (vecMulVec c' (l k)) f) Q) = 0
  rw [← hs, hl, h0, map_zero]

end GlobalTheory.LevelSupport

end
