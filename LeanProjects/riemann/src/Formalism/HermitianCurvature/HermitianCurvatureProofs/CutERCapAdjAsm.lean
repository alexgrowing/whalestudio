import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjSCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjFrom

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section clm

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E']

theorem contDiff_clm_comp (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (fun g => Λ (ψ g)) :=
  (Λ.restrictScalars ℝ).contDiff.comp hψ

theorem rdV_clm (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    RdV X (fun g => Λ (ψ g)) = fun g => Λ (RdV X ψ g) := by
  rw [rdV_global (contDiff_clm_comp Λ hψ) X, rdV_global hψ X]
  funext g
  have hd : HasFDerivAt ψ (fderiv ℝ ψ g) g := ((hψ.differentiable (by simp)) g).hasFDerivAt
  have h := (Λ.restrictScalars ℝ).hasFDerivAt.comp g hd
  exact (DFunLike.congr_fun h.fderiv (g * X)).trans rfl

theorem rw_clm' (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ w : List (B.Mat k r), B.Rw w (fun g => Λ (ψ g)) = fun g => Λ (B.Rw w ψ g)
  | [] => rfl
  | X :: w => by
    show RdV X (B.Rw w (fun g => Λ (ψ g))) = fun g => Λ (RdV X (B.Rw w ψ) g)
    rw [rw_clm' Λ hψ w, rdV_clm Λ (rw_contDiff hψ w) X]

end clm

section comps

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def lam (i : Fin (Module.finrank ℂ Wq)) (j : Fin (Module.finrank ℂ Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] ℂ :=
  (innerSL ℂ (stdOrthonormalBasis ℂ Wp j)).comp (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i))

theorem lam_apply (i j) (A : Wq →L[ℂ] Wp) :
    lam i j A = inner ℂ (stdOrthonormalBasis ℂ Wp j) (A (stdOrthonormalBasis ℂ Wq i)) := rfl

theorem hsInner_eq_sum (A C : Wq →L[ℂ] Wp) :
    B.hsInner A C = ∑ i, ∑ j, lam i j A * star (lam i j C) := by
  unfold B.hsInner B.hsVec
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.toLp_apply]
  rw [← (stdOrthonormalBasis ℂ Wp).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lam_apply, lam_apply, mul_comm]
  congr 1
  rw [← inner_conj_symm]
  rfl

end comps

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lam_opAdj_tail (i j) (s : ℂ) {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ (L : List (ℂ × List (B.Mat k r))), (∀ cw ∈ L, ∀ X ∈ cw.2, B.inLie k r X) → ∀ g,
    lam i j (((L.map fun cw => TLB.cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2).map
        (fun T => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (ψ x)) g)).sum) =
      conj s * (L.map fun cw => conj cw.1 * (-1 : ℂ) ^ cw.2.length *
        B.Rw cw.2.reverse (fun x => lam i j (ψ x)) g).sum
  | [], _, g => by simp
  | cw :: L, hL, g => by
    simp only [List.map_cons, List.sum_cons, map_add, mul_add]
    rw [lam_opAdj_tail i j s hψ L (fun cw' h => hL cw' (List.mem_cons_of_mem _ h)) g]
    congr 1
    rw [TLB.cTerm_word (hL cw List.mem_cons_self)]
    have e : (fun x => (TLB.cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2).coefAdj x (ψ x)) =
        conj (s * cw.1) • ψ := by
      funext x; simp [TLB.cTerm]
    rw [e, Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, map_smul, Pi.smul_apply, map_smul]
    have e2 := congrFun (rw_clm' (lam i j) hψ cw.2.reverse) g
    rw [← e2, smul_eq_mul, smul_eq_mul, map_mul]
    ring

theorem lam_wordSum (i j) {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ (L : List (ℂ × List (B.Mat k r))) (g : B.Mat k r),
    lam i j ((L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum) =
      (L.map fun cw => cw.1 • B.Rw cw.2 (fun x => lam i j (ψ x)) g).sum
  | [], _ => by simp
  | cw :: L, g => by
    simp only [List.map_cons, List.sum_cons, map_add, map_smul]
    rw [lam_wordSum i j hψ L g, congrFun (rw_clm' (lam i j) hψ cw.2) g]

theorem wsAdj_contDiff (L : List (ℂ × List (B.Mat k r))) {b : B.Mat k r → ℂ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (wsAdj L b) := by
  unfold wsAdj
  exact contDiff_listSum (fun (cw : ℂ × List (B.Mat k r)) x => conj cw.1 * (-1 : ℂ) ^ cw.2.length * B.Rw cw.2.reverse b x) L
    fun cw _ => contDiff_const.mul (rw_contDiff hb _)

end terms

theorem capacity_adjoint_integral_scalar : CapAdjIntOfScalar := by
  intro hS k r Wp Wq _ _ _ _ _ _ s Y μ hμ φ ψ hφ hφc hψ hψc
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  have hLw := (Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)).1
  obtain ⟨L', hL', hCV'⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r (conj Y)
  set a : Fin (Module.finrank ℂ Wq) → Fin (Module.finrank ℂ Wp) → B.Mat k r → ℂ :=
    fun i j g => lam i j (φ g) with ha
  set b : Fin (Module.finrank ℂ Wq) → Fin (Module.finrank ℂ Wp) → B.Mat k r → ℂ :=
    fun i j g => lam i j (ψ g) with hb
  have ha_s : ∀ i j, ContDiff ℝ ∞ (a i j) := fun i j => contDiff_clm_comp (lam i j) hφ
  have hb_s : ∀ i j, ContDiff ℝ ∞ (b i j) := fun i j => contDiff_clm_comp (lam i j) hψ
  have ha_c : ∀ i j, HasCompactSupport (a i j) := fun i j => hφc.comp_left (map_zero (lam i j))
  have hb_c : ∀ i j, HasCompactSupport (b i j) := fun i j => hψc.comp_left (map_zero (lam i j))

  have hAdj : ∀ i j g, lam i j (B.opAdj (capTh k r Wp Wq s Y) ψ g) = conj s * wsAdj (capLw k r Y) (b i j) g := by
    intro i j g
    unfold B.opAdj
    rw [capTh, TLB.capOp, List.map_cons, List.sum_cons, map_add]
    have h0 : (fun x => (TLB.cTerm (Wp := Wp) (Wq := Wq) 0
        (List.replicate (2 * r + k + 1) (0 : B.Mat k r))).coefAdj x (ψ x)) = (0 : ℂ) • ψ := by
      funext x; simp [TLB.cTerm]
    rw [h0, Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, zero_smul]
    rw [lam_opAdj_tail i j s hψ (capLw k r Y) (fun cw h X hX => ((hLw cw h).1 X hX).1) g]
    simp [wsAdj, b]

  have hCVc : ∀ i j, ∀ g ∈ B.GV k r, lam i j (Q.CV k r (conj Y) ψ g) = Q.CV k r (conj Y) (b i j) g := by
    intro i j g hg
    rw [hCV' _ (B.GV k r) ψ (ckOn_of_contDiff hψ _ _) g hg hg,
      hCV' _ (B.GV k r) (b i j) (ckOn_of_contDiff (hb_s i j) _ _) g hg hg]
    exact lam_wordSum i j hψ L' g

  have hP1 : ∀ x : Mt k r, B.hsInner (φ (Matrix.of x)) (B.opAdj (capTh k r Wp Wq s Y) ψ (Matrix.of x)) =
      ∑ i, ∑ j, s * (a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) := by
    intro x
    rw [hsInner_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hAdj, star_mul', Complex.star_def, Complex.conj_conj]
    simp only [ha]; ring
  have hP2 : ∀ᵐ x ∂μ, B.hsInner (φ (Matrix.of x)) (conj s • Q.CV k r (conj Y) ψ (Matrix.of x)) =
      ∑ i, ∑ j, s * (a i j (Matrix.of x) * star (Q.CV k r (conj Y) (b i j) (Matrix.of x))) := by
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx
    rw [hsInner_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hCVc i j _ hx, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_conj]
    simp only [ha]; ring

  have hI1 : ∀ i j, Integrable (fun x : Mt k r => s * (a i j (Matrix.of x) *
      star (wsAdj (capLw k r Y) (b i j) (Matrix.of x)))) μ := by
    intro i j
    have hc : Continuous (fun x : Mt k r => a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) :=
      (ha_s i j).continuous.mul (continuous_star.comp (wsAdj_contDiff _ (hb_s i j)).continuous)
    have hcs : HasCompactSupport
        (fun x : Mt k r => a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) :=
      (ha_c i j).mul_right
    exact (hc.integrable_of_hasCompactSupport (μ := μ) hcs).const_mul s
  have hI2 : ∀ i j, Integrable (fun x : Mt k r => s * (a i j (Matrix.of x) *
      star (Q.CV k r (conj Y) (b i j) (Matrix.of x)))) μ := by
    intro i j
    have hS' : ContDiff ℝ ∞ (fun g => (L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) g).sum) :=
      contDiff_listSum (fun cw g => cw.1 • B.Rw cw.2 (b i j) g) L' fun cw _ =>
        (rw_contDiff (hb_s i j) _).const_smul _
    have hc : Continuous (fun x : Mt k r => a i j (Matrix.of x) *
        star ((L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) (Matrix.of x)).sum)) :=
      (ha_s i j).continuous.mul (continuous_star.comp hS'.continuous)
    have hcs : HasCompactSupport (fun x : Mt k r => a i j (Matrix.of x) *
        star ((L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) (Matrix.of x)).sum)) :=
      (ha_c i j).mul_right
    refine ((hc.integrable_of_hasCompactSupport (μ := μ) hcs).const_mul s).congr ?_
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx
    rw [hCV' _ (B.GV k r) (b i j) (ckOn_of_contDiff (hb_s i j) _ _) _ hx hx]
  rw [integral_congr_ae (Eventually.of_forall hP1), integral_congr_ae hP2,
    integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hI1 i j),
    integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hI2 i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => hI1 i j), integral_finset_sum _ (fun j _ => hI2 i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_const_mul,
    hS k r Y μ hμ (a i j) (b i j) (ha_s i j) (ha_c i j) (hb_s i j) (hb_c i j)]

theorem capAdjInt_of_scalar (hS : CapAdjScalar) : CapAdjInt := capacity_adjoint_integral_scalar hS

end

end Formalism.FourierDecayAlt.P.CutMP.ER
