import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilOfVacuum

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker Complex Classical
open Formalism.L2.Th1.H (matH alphaQ qOf opU slice pow4)
open scoped BigOperators ComplexConjugate Real

namespace WeilVac

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem kappa_ne_zero {γ₀ : IsoK D} (k : KapChoice γ₀) : k.kappa ≠ 0 := by
  refine finprod_induction (fun x : ℂ => x ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun p => zpow_ne_zero _ ?_
  intro h0
  have h1 := k.rt_pow p p.2.1 p.2.2
  have hpi : k.pi p ≠ 0 := by
    intro h
    have h2 := k.pi_gen p p.2.1 p.2.2
    rw [h, Ideal.span_singleton_zero] at h2
    exact pow_ne_zero _ (k.pp p).ne_bot h2
  have hE : (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) ≠ 0 := by simpa using hpi
  rw [h0, zero_pow (mul_ne_zero two_ne_zero (classNumber_ne_zero _))] at h1
  exact div_ne_zero ((map_ne_zero _).2 hE) ((map_ne_zero _).2 ((map_ne_zero _).2 hE)) h1.symm

theorem thMM_spec (B : Base D cc δ) (h : B.StdOK) : B.IsThMM B.thMM ∧ B.thMM ≠ 0 := by
  obtain ⟨e, u⟩ := ThetaVec.thetaVector _ _ _ _ _ _ _ _ h _ (kappa_ne_zero B.kc)
  have h1 : B.IsThMM B.thMM := Classical.epsilon_spec (p := IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa) e
  exact ⟨h1, (u _ h1.1 h1.2).1⟩

theorem thZero_ne_zero (B : Base D cc δ) (h : B.StdOK) (N N' : ℕ) : B.thZero N N' ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 (thMM_spec B h).2
  refine Function.ne_iff.2 ⟨fun τ _ _ => a τ, ?_⟩
  show ∏ _i : Fin N', ∏ _j : Fin N, B.thMM a ≠ 0
  exact Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun _ _ => ha

theorem areaOK (B : Base D cc δ) : B.AreaOK := by
  rw [Base.AreaOK, ThetaVec.area_eq]
  exact GlobalTheory.OddTheta.area_eq B.L _ fun z => by rw [← B.lat]; rfl

theorem q_int (B : Base D cc δ) (h : B.StdOK) {x : D.what₂.Tau → ℂ} (hx : x ∈ B.lamM) :
    ∃ m : ℤ, qOf B.cq (matH (hOne B.L D.what₂.Tau)) x = m := by
  have hs : ∀ a, slice a (0 : Fin 4 × D.what₂.Tau → ℂ) = 0 := fun _ => rfl
  have h1 := h.betaSemi.1 (B.gC (ThetaVec.ins 0 x)) ⟨ThetaVec.ins 0 x, fun a => by
    rw [ThetaVec.slice_ins]; split_ifs; exacts [hx, B.lamM.zero_mem], rfl⟩
  rw [h.betaAlpha, ← mul_self_eq_one_iff] at h1
  simp only [ThetaVec.slice_ins, Fin.prod_univ_four, hs, h.alpha0, Fin.isValue, if_true, Fin.reduceEq, if_false,
    mul_one] at h1
  rw [alphaQ, ← Complex.exp_add, Complex.exp_eq_one_iff] at h1
  obtain ⟨m, hm⟩ := h1
  refine ⟨m, ?_⟩
  have : (qOf B.cq (matH (hOne B.L D.what₂.Tau)) x : ℂ) = m := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    linear_combination hm
  exact_mod_cast this

theorem entry_mem (B : Base D cc δ) {N N' : ℕ} {x : VC D N N'}
    (hx : x ∈ La D (tor0 D cc δ) (stdL D N) (stdL D N')) : x ∈ powLat B.lamM N N' := by
  refine (AddSubgroup.closure_le _).2 ?_ hx
  rintro _ ⟨w, hw, A, hA, rfl⟩ i j
  exact AddSubgroup.subset_closure ⟨w, hw, A i j, (GlobalTheory.OddGenus.mem_iff_entries D N N' A).1 hA i j, rfl⟩

theorem Hf_eq (B : Base D cc δ) {N N' : ℕ} (z w : VC D N N') :
    Hf D (tor0 D cc δ) z w =
      ∑ i, ∑ j, matH (hOne B.L D.what₂.Tau) (fun τ => z τ i j) (fun τ => w τ i j) := by
  have hA : area (tor0 D cc δ).abelian₂ = latticeArea B.L := (areaOK B).trans (ThetaVec.area_eq _)
  have e : ∀ u v : D.what₂.Tau → ℂ, matH (hOne B.L D.what₂.Tau) u v =
      ∑ τ, u τ * conj (v τ) / (latticeArea B.L : ℂ) := fun u v => ThetaVec.stdH_apply B.L u v
  simp only [e, Hf, hA, Finset.sum_div]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem thZero_mem (B : Base D cc δ) (h : B.StdOK) (N N' : ℕ) :
    B.thZero N N' ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N') := by
  have hθ := (thMM_spec B h).1.1
  refine ⟨?_, fun x hx z => ?_⟩
  · have hd : Differentiable ℂ B.thMM := differentiableOn_univ.1 hθ.1.differentiableOn
    unfold Base.thZero tensPow
    fun_prop
  · have hx' := entry_mem B hx
    choose m hm using fun i j => q_int B h (hx' i j)
    have h1 : Real.sqrt D.host.d / 2 * (Hf D (tor0 D cc δ) x x).re = ((∑ i, ∑ j, m i j : ℤ) : ℝ) := by
      rw [Hf_eq B]
      push_cast
      simp only [Complex.re_sum, Finset.mul_sum, ← hm]
      rfl
    have h2 : al D (tor0 D cc δ) x = ∏ i, ∏ j, alphaQ B.cq (matH (hOne B.L D.what₂.Tau)) fun τ => x τ i j := by
      rw [al, h1, round_intCast, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
      simp only [alphaQ, hm, ← Complex.exp_sum, ← Finset.mul_sum]
      congr 1
      push_cast
      ring
    rw [h2, U, Hf_eq B, Hf_eq B]
    simp only [Base.thZero, tensPow, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, Complex.exp_sum,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hθ.2 _ (hx' i j) fun τ => z τ i j

def trivChar (D : D7) {N : ℕ} (hN : Even N) : HeckeU D N where
  f := 1
  n := fun _ => 0
  unitary := fun _ => by simp
  cont := ⟨1, one_pos, fun _ _ _ => rfl⟩
  aut := fun _ => by simp
  norm := fun _ => rfl
  par := fun _ => by simpa using hN
  unr := fun _ _ _ => rfl

end WeilVac

open WeilVac

end GlobalTheory.Mem.Col2
