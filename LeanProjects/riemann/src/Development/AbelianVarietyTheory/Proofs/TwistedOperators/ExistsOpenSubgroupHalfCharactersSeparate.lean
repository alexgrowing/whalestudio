import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSeparate

open GlobalTheory.IdemModTwo

theorem sum_incA_inv_mul {D : D7} (W : HSp D) (p i : Fin W.rank) :
    ∑ k, incA D (W.gram⁻¹ p k) * incA D (W.gram k i) = if p = i then 1 else 0 := by
  have h1 : (∑ k, incA D (W.gram⁻¹ p k) * incA D (W.gram k i)) = incA D ((W.gram⁻¹ * W.gram) p i) := by
    rw [Matrix.mul_apply, map_sum (incA D)]
    exact Finset.sum_congr rfl fun k _ => ((incA D).map_mul _ _).symm
  rw [h1, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit W), Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

set_option maxHeartbeats 1000000 in

theorem exists_pair_entry {D : D7} {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)}
    {e : AE D} (he : SplitAt D v e) (W : HSp D) {r : ℕ} (p : Fin W.rank) (q : Fin r) (c : Fv D.host.F v) :
    ∃ a : Mx D W.rank r, IsHalf e a ∧ ∀ t : Mx D W.rank r,
      halfPair W a t = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * t p q := by
  let a : Mx D W.rank r := Matrix.of fun k j => if j = q then
    incA D (star (W.gram⁻¹ p k)) * incA D (star D.host.xi0⁻¹) * fj D (singleV D.host.F v c) * e else 0
  have hca : ∀ k, cA D (a k q) = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * incA D (W.gram⁻¹ p k) := by
    intro k
    show cA D (if q = q then _ else 0) = _
    rw [if_pos rfl, map_mul, map_mul, map_mul, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.cA_incA, star_star, star_star,
      cA_fj]
    ring
  refine ⟨a, fun k j => ?_, fun t => ?_⟩
  · show e * a k j = a k j
    simp only [a, Matrix.of_apply]
    split_ifs
    · rw [mul_left_comm, he.1]
    · rw [mul_zero]
  have hG := sum_incA_inv_mul W p
  unfold halfPair
  calc ∑ i, ∑ j, ∑ k, cA D (a k j) * incA D (W.gram k i) * t i j
      = ∑ i, incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * (if p = i then 1 else 0) * t i q :=
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_eq_single q (fun j _ hj => Finset.sum_eq_zero fun k _ => by
            rw [show a k j = 0 from if_neg hj, map_zero, zero_mul, zero_mul]) (fun h => absurd (Finset.mem_univ q) h)]
          rw [← hG i, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by rw [hca]; ring
    _ = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * t p q := by
      rw [Finset.sum_eq_single p (fun i _ hi => by rw [if_neg (Ne.symm hi), mul_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ p) h), if_pos rfl, mul_one]

end GlobalTheory.HalfSeparate

namespace GlobalTheory.HalfSeparate

open GlobalTheory.IdemModTwo

set_option maxHeartbeats 1000000 in

theorem exists_open_separated : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (e : AE D), IsSplitIdem D e → ∀ U : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (U : Set (halfMx (cA D e) W.rank r)) → ∃ L : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ L ≤ U ∧ ∀ x, x ∉ L → ∃ a : halfMx e W.rank r, (∀ l ∈ L, ψ (halfSympl W (a : Mx D W.rank r) (l : Mx D W.rank r)) = 1) ∧ ψ (halfSympl W (a : Mx D W.rank r) (x : Mx D W.rank r)) ≠ 1 := by
  intro D ψ hψ W r e hε U hU
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  have he' := he.conj
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  let sg : Fv D.host.F v →+ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F := AddMonoidHom.ofMapSub (singleV D.host.F v) (singleV_sub D v)
  let ι : Fv D.host.F v →+ AF D.host.F := AddMonoidHom.mk' (fun y => pairA D.host.F 0 (sg y)) fun a b => by
    rw [map_add]; exact Prod.ext (add_zero _).symm rfl
  have hι : Continuous ι := Continuous.prodMk continuous_const (GlobalTheory.SplitAnnihilator.continuous_singleV D.host.F v)
  have hψc : Continuous fun x => ψ (ι x) := hψ.1.1.comp hι

  obtain ⟨ε0, hε0, hψε⟩ : ∃ ε > 0, ∀ x : Fv D.host.F v, ‖x‖ < ε → ψ (ι x) = 1 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hψc.continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun x hx => GlobalTheory.ThetaStalk.eq_one_of_pow_near fun n => ?_⟩
    have := h (x := n • x) (by
      rw [dist_zero_right]; exact (IsUltrametricDist.norm_nsmul_le x n).trans_lt hx)
    rwa [map_zero, AddChar.map_zero_eq_one, dist_eq_norm, map_nsmul, AddChar.map_nsmul_eq_pow] at this
  obtain ⟨y1, hy1⟩ : ∃ y, ψ (ι y) ≠ 1 := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v

  let G := Fin W.rank × Fin r → Fv D.host.F v
  let J : G →+ Mx D W.rank r := AddMonoidHom.mk' (fun y => Matrix.of fun i k => fj D (sg (y (i, k))) * cA D e)
    fun a b => by
      ext i k
      simp only [G, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul]
  have hJ : Continuous J := continuous_matrix fun i k =>
    ((IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))).comp
      (hι.comp (continuous_apply (i, k)))).mul continuous_const
  have hJh : ∀ y, J y ∈ halfMx (cA D e) W.rank r := fun y i k => by
    show cA D e * (_ * cA D e) = _ * cA D e
    rw [mul_left_comm, he'.1]
  let J' : G →+ halfMx (cA D e) W.rank r := J.codRestrict (halfMx (cA D e) W.rank r) hJh
  have hJ' : Continuous J' := hJ.subtype_mk _
  have hJs : Function.Surjective J' := fun u => by
    choose y hy using fun p : Fin W.rank × Fin r => he'.exists_scalar ((u : Mx D W.rank r) p.1 p.2)
    exact ⟨y, Subtype.ext (Matrix.ext fun i k => (hy (i, k)).symm.trans (u.2 i k))⟩
  have : T2Space (halfMx (cA D e) W.rank r) := t2Space_halfAdelicMatrixAddSubgroup (cA D e) W.rank r
  have : LocallyCompactSpace (halfMx (cA D e) W.rank r) := lcHalf (cA D e) W.rank r
  have : R1Space (halfMx (cA D e) W.rank r) := T2Space.r1Space
  have : BaireSpace (halfMx (cA D e) W.rank r) := BaireSpace.of_t2Space_locallyCompactSpace
  have hopen : IsOpenMap J' := AddMonoidHom.isOpenMap_of_sigmaCompact J' hJs hJ'
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hJ') 0 (by
    show J' 0 ∈ U
    rw [map_zero]; exact U.zero_mem)

  have hR : 0 ≤ ‖y1‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  let LG : AddSubgroup G :=
    { carrier := {y | ∀ p, ∀ c : Fv D.host.F v, ‖c‖ ≤ ‖y1‖ / ρ → ψ (ι (c * y p)) = 1}
      add_mem' := fun {a b} ha hb p c hc => by
        rw [Pi.add_apply, mul_add, map_add, AddChar.map_add_eq_mul, ha p c hc, hb p c hc, one_mul]
      zero_mem' := fun p c _ => by rw [Pi.zero_apply, mul_zero, map_zero, AddChar.map_zero_eq_one]
      neg_mem' := fun {a} ha p c hc => by
        have h := ψ.map_add_eq_mul (ι (c * (-a) p)) (ι (c * a p))
        rw [← map_add, Pi.neg_apply, mul_neg, neg_add_cancel, map_zero, AddChar.map_zero_eq_one, ha p c hc,
          mul_one] at h
        rw [Pi.neg_apply, mul_neg]
        exact h.symm }
  have hLGopen : IsOpen (LG : Set G) := by
    refine AddSubgroup.isOpen_of_mem_nhds LG (g := 0) (Metric.mem_nhds_iff.2 ⟨ε0 / (‖y1‖ / ρ + 1), by positivity,
      fun y hy p c hc => hψε _ ?_⟩)
    have hy' : ‖y‖ < ε0 / (‖y1‖ / ρ + 1) := mem_ball_zero_iff.1 hy
    rw [lt_div_iff₀ (by positivity)] at hy'
    calc ‖c * y p‖ = ‖c‖ * ‖y p‖ := norm_mul _ _
      _ ≤ ‖y1‖ / ρ * ‖y‖ := mul_le_mul hc (norm_le_pi_norm y p) (norm_nonneg _) hR
      _ ≤ ‖y‖ * (‖y1‖ / ρ + 1) := by nlinarith [norm_nonneg y]
      _ < ε0 := hy'
  have hLGsmall : ∀ y ∈ LG, ‖y‖ < ρ := fun y hy => (pi_norm_lt_iff hρ).2 fun p => by
    by_contra hn
    push_neg at hn
    have hp : 0 < ‖y p‖ := hρ.trans_le hn
    have h := hy p (y1 / y p) (by rw [norm_div]; exact div_le_div_of_nonneg_left (norm_nonneg _) hρ hn)
    rw [div_mul_cancel₀ _ (norm_pos_iff.1 hp)] at h
    exact hy1 h
  refine ⟨LG.map J', by rw [AddSubgroup.coe_map]; exact hopen _ hLGopen, ?_, fun x hx => ?_⟩
  · rw [AddSubgroup.map_le_iff_le_comap]
    intro y hy
    exact hball (mem_ball_zero_iff.2 (hLGsmall y hy))
  obtain ⟨y, rfl⟩ := hJs x
  have hy : ¬ ∀ p, ∀ c : Fv D.host.F v, ‖c‖ ≤ ‖y1‖ / ρ → ψ (ι (c * y p)) = 1 :=
    fun h => hx (AddSubgroup.mem_map_of_mem _ h)
  push_neg at hy
  obtain ⟨p, c, hc, hne⟩ := hy
  obtain ⟨a, ha, hpair⟩ := exists_pair_entry he W p.1 p.2 c
  have key : ∀ y', ψ (halfSympl W a (J y')) = ψ (ι (c * y' p)) := fun y' => by
    congr 1
    have h1 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one]
    have h2 : incA D D.host.xi0 * halfPair W a (J y') =
        fj D (singleV D.host.F v c) * cA D e * (fj D (singleV D.host.F v (y' p)) * cA D e) := by
      rw [hpair]
      show incA D D.host.xi0 * (incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e *
        (fj D (singleV D.host.F v (y' p)) * cA D e)) = _
      linear_combination (fj D (singleV D.host.F v c) * cA D e * (fj D (singleV D.host.F v (y' p)) * cA D e)) * h1
    rw [halfSympl, h2]
    exact GlobalTheory.SplitAnnihilator.trace_split he' c (y' p)
  refine ⟨⟨a, ha⟩, fun l hl => ?_, (key y).trans_ne hne⟩
  obtain ⟨y', hy', rfl⟩ := AddSubgroup.mem_map.1 hl
  exact (key y').trans (hy' p c hc)

end GlobalTheory.HalfSeparate
