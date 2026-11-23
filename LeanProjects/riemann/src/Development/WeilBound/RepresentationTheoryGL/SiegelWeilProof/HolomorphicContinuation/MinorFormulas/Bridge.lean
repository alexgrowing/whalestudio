import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeC

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem an_fQ (s z : ℂ) (m : ℕ) (Q : Fm n) (B₀ : MC n) (hB : B₀ ∈ OmS s) : AnalyticAt ℂ (fQ s z m Q) B₀ := by
  obtain ⟨h1, h2, h3⟩ := hB
  have hu := entAn_inv (entAn_X (Complex.I * s) B₀) h1
  have hv := entAn_inv (entAn_Y (Complex.I * s) B₀) h2
  have hf : ∀ k : Bool × Fin n × Fin n, AnalyticAt ℂ (fun B => vals s B k) B₀ := by
    rintro ⟨_ | _, a, b⟩
    · exact hu a b
    · exact hv a b
  exact (an_clsC s z m 0 1 B₀ ⟨h1, h2, h3⟩).mul (an_eval (fun k B => vals s B k) B₀ hf _)

theorem anN_fQ (s z : ℂ) (m : ℕ) (Q : Fm n) : AnalyticOnNhd ℂ (fQ s z m Q) (OmS s) := fun x hx => an_fQ s z m Q x hx

theorem fderiv_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) (Q : Fm n) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) :
    fderiv ℂ (fQ s z m Q) x (eU k l) = fQ s z m (opD s m k l Q) x := by
  have hd := (an_fQ s z m Q x hx).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℂ => x + t • eU k l) (eU k l) 0 := hasDerivAt_line x (eU k l)
  have h1 : HasDerivAt (fun t : ℂ => fQ s z m Q (x + t • eU k l)) (fderiv ℂ (fQ s z m Q) x (eU k l)) 0 :=
    hd.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
  exact h1.unique (line_fQ s hs z m Q x hx k l)

def opsSeq (s : ℂ) (m : ℕ) : (k : ℕ) → (Fin k → Fin n × Fin n) → Fm n → Fm n
  | 0, _, Q => Q
  | k + 1, dirs, Q => opD s m (dirs 0).1 (dirs 0).2 (opsSeq s m k (Fin.tail dirs) Q)

theorem iter_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) :
    ∀ (k : ℕ) (dirs : Fin k → Fin n × Fin n) (Q : Fm n) (x : MC n), x ∈ OmS s →
      iteratedFDeriv ℂ k (fQ s z m Q) x (fun i => eU (dirs i).1 (dirs i).2) = fQ s z m (opsSeq s m k dirs Q) x
  | 0, dirs, Q, x, hx => by simp [opsSeq]
  | k + 1, dirs, Q, x, hx => by
    have hdiff : DifferentiableAt ℂ (iteratedFDeriv ℂ k (fQ s z m Q)) x :=
      ((anN_fQ s z m Q).iteratedFDeriv k x hx).differentiableAt
    rw [hdiff.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℂ k (fQ s z m Q) y (Fin.tail fun i => eU (dirs i).1 (dirs i).2)) =ᶠ[𝓝 x]
        fQ s z m (opsSeq s m k (Fin.tail dirs) Q) := by
      filter_upwards [(isOpen_OmS s).mem_nhds hx] with y hy
      exact iter_fQ s hs z m k (Fin.tail dirs) Q y hy
    rw [heq.fderiv_eq]
    exact fderiv_fQ s hs z m _ x hx (dirs 0).1 (dirs 0).2

theorem opsSeq_eq (s : ℂ) (m : ℕ) : ∀ (k : ℕ) (dirs : Fin k → Fin n × Fin n) (Q : Fm n),
    opsSeq s m k dirs Q = (List.finRange k).foldr (fun i g => opD s m (dirs i).1 (dirs i).2 ∘ₗ g) LinearMap.id Q
  | 0, dirs, Q => by simp [opsSeq]
  | k + 1, dirs, Q => by
    rw [opsSeq, opsSeq_eq s m k (Fin.tail dirs) Q, List.finRange_succ, List.foldr_cons, List.foldr_map]
    rfl

theorem evQ_smul (s z a : ℂ) (P : Fm n) (B : MC n) : evQ s z (a • P) B = a * evQ s z P B := by
  rw [smulC, evQ_mul, evQ_CC]

theorem fQ_linear (s z : ℂ) (m : ℕ) {ι : Type} (t : Finset ι) (a : ι → ℂ) (P : ι → Fm n) (B : MC n) :
    fQ s z m (∑ i ∈ t, a i • P i) B = ∑ i ∈ t, a i * fQ s z m (P i) B := by
  simp only [fQ, evQ_sum, evQ_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem cay_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) (Q : Fm n) (x : MC n) (hx : x ∈ OmS s) :
    cay (fQ s z m Q) x = fQ s z m (cayF s m Q) x := by
  have hc : ContDiffAt ℂ ω (fQ s z m Q) x := (an_fQ s z m Q x hx).contDiffAt
  have hperm : ∀ σ : Equiv.Perm (Fin n), iteratedFDeriv ℂ n (fQ s z m Q) x (fun k => eU (σ k) k) =
      iteratedFDeriv ℂ n (fQ s z m Q) x (fun k => eU k (σ⁻¹ k)) := by
    intro σ
    have := hc.iteratedFDeriv_comp_perm (fun k => eU k (σ⁻¹ k)) σ
    rw [← this]
    congr 1
    funext k
    simp
  simp only [cay, hperm]
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
  simp only [Equiv.inv_apply, inv_inv, Equiv.Perm.sign_inv]
  have hI : ∀ σ : Equiv.Perm (Fin n), iteratedFDeriv ℂ n (fQ s z m Q) x (fun k => eU k (σ k)) =
      fQ s z m (opsSeq s m n (fun k => (k, σ k)) Q) x := fun σ => iter_fQ s hs z m n (fun k => (k, σ k)) Q x hx
  simp only [hI, opsSeq_eq]
  rw [cayF, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  rw [fQ_linear]

theorem fQ_one (s z : ℂ) (m : ℕ) (B : MC n) : fQ s z m 1 B = clsC s z m 0 1 B := by
  simp [fQ, evQ]

theorem bridge : Bridge := by
  intro n s hs m N z B hB
  have key : ∀ N : ℕ, ∀ B : MC n, B ∈ OmS s → (cay^[N] (clsC s z m 0 1)) B = fQ s z m ((cayF s m)^[N] 1) B := by
    intro N
    induction N with
    | zero =>
      intro B _
      simp [fQ_one]
    | succ N ih =>
      intro B hB
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have heq : (cay^[N] (clsC s z m 0 1)) =ᶠ[𝓝 B] fQ s z m ((cayF s m)^[N] 1) := by
        filter_upwards [(isOpen_OmS s).mem_nhds hB] with y hy
        exact ih y hy
      have e : cay (cay^[N] (clsC s z m 0 1)) B = cay (fQ s z m ((cayF s m)^[N] 1)) B := by
        simp only [cay]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [(heq.iteratedFDeriv ℂ n).eq_of_nhds]
      rw [e, cay_fQ s hs z m _ B hB]
  rw [key N B hB]
  rfl

end PositivityTheory.Rg.Sw.SP
