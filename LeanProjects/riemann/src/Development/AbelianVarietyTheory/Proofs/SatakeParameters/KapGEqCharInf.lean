import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom

theorem lamC_qbar {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (q : TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (algebraMap TaylorLogMetric.Qbar ℂ q) = lam q := by
  unfold TaylorLogMetric.lamC
  rw [dif_pos (show algebraMap TaylorLogMetric.Qbar ℂ q ∈ TaylorLogMetric.Qbar from q.2)]
  rfl

theorem kapG_eq_char_inf : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (a : D.host.E), a * D.host.conj a = 1 → (∀ v, (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det = ρ v a) → letI := wittFractionAlgebraCp p; letI := algKfC E; kapG X ℂ_[p] j c γ = E.iK (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O)) * TaylorLogMetric.lamC lam (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) * (p : ℂ_[p]) ^ (-(∑ v : X.Pl, X.vm v (j + 1) * ordP (X.G.P.W v) p (ρ v a))) := by
  intro D p _ X E pos lam ρ hLP j c γ a ha hdet
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha
    exact zero_ne_one ha
  have hconj : D.host.conj a = a⁻¹ := eq_inv_of_mul_eq_one_right ha

  have hcA : cA X ℂ_[p] j (gamAt X j c γ) =
      TaylorLogMetric.lamC lam (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) := by
    let q : ∀ v : X.Pl, Fin (X.G.P.n' v) → TaylorLogMetric.Qbar := fun v s => ⟨TaylorLogMetric.embT D (pos ⟨v, s⟩) a, embT_mem_qbar D _ a⟩
    have h1 : (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) =
        algebraMap TaylorLogMetric.Qbar ℂ (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), q v s ^ X.w v (j + 1) s) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [map_zpow₀]
      rfl
    rw [h1, lamC_qbar, map_prod]
    unfold cA
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_zpow₀, hdet v]
    have h2 : lam (q v s) = twG X E v s (ρ v (if IsOddPos s then D.host.conj a else a)) := by
      rw [← hLP v s a, ← lamC_qbar lam (q v s)]
      rfl
    rw [h2, twG_eq_tw]
    by_cases hs : IsOddPos s
    · rw [if_pos hs, if_pos hs, hconj, map_inv₀, map_inv₀, inv_zpow', neg_one_mul]
    · rw [if_neg hs, if_neg hs, one_mul]
  have hP : (∏ v : X.Pl, (p : ℂ_[p]) ^ (-(X.vm v (j + 1) * ordP (X.G.P.W v) p
      (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det))) =
      (p : ℂ_[p]) ^ (-(∑ v : X.Pl, X.vm v (j + 1) * ordP (X.G.P.W v) p (ρ v a))) := by
    simp_rw [hdet]
    rw [← Finset.sum_neg_distrib]
    induction (Finset.univ : Finset X.Pl) using Finset.cons_induction with
    | empty => simp
    | cons b s hb ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hp, ih]
  unfold kapG
  rw [hcA, hP]
  rfl

end GlobalTheory.TwV.Xc

end
