import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemOfMkEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMul
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwoPlaceIdem

variable {D : D7}

theorem AF_ext {F : Type} [Field F] [NumberField F] {x y : AF F} (h1 : fstA F x = fstA F y)
    (h2 : sndA F x = sndA F y) : x = y := Prod.ext h1 h2

theorem fstA_pairA {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) : fstA F (pairA F a b) = a := rfl

theorem sndA_pairA {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) : sndA F (pairA F a b) = b := rfl

theorem placeIdem_eq_single
    (hsv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), singleV D.host.F v 1 ∈ intAf D.host.F ∧
      evalV D.host.F v (singleV D.host.F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV D.host.F v' (singleV D.host.F v 1) = 0)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    ε = pairA D.host.F 0 (singleV D.host.F v 1) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  change evalV D.host.F u α = evalV D.host.F u (singleV D.host.F v 1)
  by_cases huv : u = v
  · subst huv; rw [h1, (hsv u).2.1]
  · rw [h0 u huv, (hsv v).2.2 u huv]

theorem single_mul_single
    (hsv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), singleV D.host.F v 1 ∈ intAf D.host.F ∧
      evalV D.host.F v (singleV D.host.F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV D.host.F v' (singleV D.host.F v 1) = 0)
    {v w : HeightOneSpectrum (𝓞 D.host.F)} (hvw : v ≠ w) :
    pairA D.host.F 0 (singleV D.host.F v 1) * pairA D.host.F 0 (singleV D.host.F w 1) = 0 := by
  refine AF_ext ?_ ?_
  · rw [map_mul, fstA_pairA, fstA_pairA, map_zero, mul_zero]
  · rw [map_mul, sndA_pairA, sndA_pairA, map_zero]
    refine Subtype.ext (funext fun u => ?_)
    change evalV D.host.F u (singleV D.host.F v 1 * singleV D.host.F w 1) = evalV D.host.F u 0
    rw [map_mul, map_zero]
    by_cases huv : u = v
    · subst huv; rw [(hsv w).2.2 u hvw, mul_zero]
    · rw [(hsv v).2.2 u huv, zero_mul]

theorem finPart_algebraMap (x : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) x) = sndA D.host.F x ⊗ₜ[D.host.F] (1 : D.host.E) := by
  change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (algebraMap (AF D.host.F) (AE D) x) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  rfl

set_option maxHeartbeats 1000000 in
theorem exists_idem_half : ∀ (D : D7), ∃ e : AE D, e * e = e ∧ e * cA D e = 0 ∧ finPart D e ∈ intAE D ∧
    finPart D (cA D e) ∈ intAE D ∧ ∃ h : AE D, finPart D h ∈ intAE D ∧ 2 * h = 1 - e - cA D e := by
  intro D
  obtain ⟨P, hP2, hsv, β, hβ, h1⟩ := GlobalTheory.LatVac.one_eq_sum_singleV_add_two_mul D.host.F
  have H : ∀ v ∈ P, ∃ e : AE D, e * e = e ∧ e * cA D e = 0 ∧
      e + cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv
    obtain ⟨e, ε, he, hε, hs⟩ := Formalism.IndefR.Fin.twoSplitIdem D v (hP2 v hv)
    exact ⟨e, he.1, he.2.1, by rw [hs, placeIdem_eq_single hsv hε]⟩
  choose! E hEE hEc hEs using H
  have absE : ∀ v ∈ P, E v = E v * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv; rw [← hEs v hv, mul_add, hEE v hv, hEc v hv, add_zero]
  have absC : ∀ v ∈ P, cA D (E v) = cA D (E v) * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv
    rw [← hEs v hv, mul_add, mul_comm (cA D (E v)) (E v), hEc v hv, ← map_mul, hEE v hv, zero_add]
  have cross : ∀ (x y : AE D) (v w : HeightOneSpectrum (𝓞 D.host.F)), v ≠ w →
      x = x * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) →
      y = y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F w 1)) → x * y = 0 := by
    intro x y v w hvw hx hy
    calc x * y = (x * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1))) *
          (y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F w 1))) := by rw [← hx, ← hy]
      _ = x * y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1) *
          pairA D.host.F 0 (singleV D.host.F w 1)) := by rw [map_mul]; ring
      _ = 0 := by rw [single_mul_single hsv hvw, map_zero, mul_zero]
  have hee : (∑ v ∈ P, E v) * (∑ v ∈ P, E v) = ∑ v ∈ P, E v := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.sum_eq_single v (fun w hw hwv => cross _ _ v w (Ne.symm hwv) (absE v hv) (absE w hw))
      (fun h => absurd hv h), hEE v hv]
  have hec : (∑ v ∈ P, E v) * cA D (∑ v ∈ P, E v) = 0 := by
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [Finset.sum_eq_single v (fun w hw hwv => cross _ _ v w (Ne.symm hwv) (absE v hv) (absC w hw))
      (fun h => absurd hv h), hEc v hv]
  have hsum : (∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v) =
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := by
    have hcs : cA D (∑ v ∈ P, E v) = ∑ v ∈ P, cA D (E v) := map_sum (cA D) E P
    calc (∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v) = (∑ v ∈ P, E v) + ∑ v ∈ P, cA D (E v) := congrArg (fun z => (∑ v ∈ P, E v) + z) hcs
      _ = ∑ v ∈ P, (E v + cA D (E v)) := Finset.sum_add_distrib.symm
      _ = ∑ v ∈ P, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) :=
          Finset.sum_congr rfl fun v hv => hEs v hv
      _ = algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := (map_sum _ _ _).symm
  have hi1 : finPart D (∑ v ∈ P, E v) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ ((map_mul (finPart D) _ _).symm.trans (congrArg (finPart D) hee))
  have hi2 : finPart D (cA D (∑ v ∈ P, E v)) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ ((map_mul (finPart D) _ _).symm.trans
      (congrArg (finPart D) ((map_mul (cA D) _ _).symm.trans (congrArg (cA D) hee))))
  refine ⟨∑ v ∈ P, E v, hee, hec, hi1, hi2, ?_⟩
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β), ?_, ?_⟩
  · rw [finPart_algebraMap, sndA_pairA]
    exact AddSubgroup.subset_closure ⟨β, hβ, 1, by simp⟩
  · have key : 2 * pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β =
        1 - ∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1) := by
      refine AF_ext ?_ ?_
      · rw [map_mul, map_sub, map_sum, map_one, map_ofNat, fstA_pairA]
        simp only [fstA_pairA, Finset.sum_const_zero, sub_zero]
        rw [← map_ofNat (algebraMap D.host.F (Ainf D.host.F)) 2, ← map_mul]
        norm_num
      · rw [map_mul, map_sub, map_sum, map_one, map_ofNat, sndA_pairA]
        simp only [sndA_pairA]
        linear_combination -h1
    calc (2 : AE D) * algebraMap (AF D.host.F) (AE D) (pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β)
        = algebraMap (AF D.host.F) (AE D) (2 * pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β) := by
          rw [show (2 : AE D) = algebraMap (AF D.host.F) (AE D) 2 from (map_ofNat _ 2).symm]
          exact (map_mul _ _ _).symm
      _ = algebraMap (AF D.host.F) (AE D) (1 - ∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) :=
          congrArg _ key
      _ = 1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := by
          rw [map_sub, map_one]
      _ = 1 - ((∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v)) := by rw [hsum]
      _ = 1 - ∑ v ∈ P, E v - cA D (∑ v ∈ P, E v) := by rw [sub_sub]

end GlobalTheory.TwoPlaceIdem
