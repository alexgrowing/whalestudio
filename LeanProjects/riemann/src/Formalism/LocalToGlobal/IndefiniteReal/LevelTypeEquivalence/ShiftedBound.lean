import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MdTendstoSeq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem shifted_bound {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {M : (Fin k → ℝ) →+ WO S T} {P : WO S T →+ (Fin k → ℝ)} (hM : IsRealFrame M)
    (hPc : Continuous P) (hMP : ∀ w, M (P w) = eInf D • w) (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B, ∀ y t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (Gf ψ M f y) t‖ ≤ B := by
  obtain ⟨Λ, hΛ, hψΛ⟩ := psi_real ψ hψ
  have hψu : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have hs : ∀ x, ContDiff ℝ ∞ (Gf ψ M f x) := Gf_smooth hΛ hψΛ hM hf
  have hbd : ∀ (m : ℕ) (l : Fin m → Fin k), ∃ C, ∀ x, ‖dH ψ M l f x‖ ≤ C := fun m l =>
    dH_bdd hψu hf hs l (cont_dH hψ hf hM hPc hMP l)
  choose Cb hCb using hbd
  set Bd : ℝ := ∑ m ∈ Finset.range (n + 1), ∑ l : Fin m → Fin k, Cb m l
  set b : Fin k → Fin k → ℂ := fun i j => Λ (symplOH S T (M (ev i)) (M (ev j))).1
  set Bb : ℝ := ∑ i, ∑ j, ‖b i j‖
  have hBb : 0 ≤ Bb := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Bb * R) ^ i * Bd, fun y t ht => ?_⟩

  let c : (Fin k → ℝ) →+ ℂ := AddMonoidHom.mk' (fun u => -Λ (symplOH S T (M t) (M u)).1) (fun a a' => by
    simp only [map_add, symplOH_add_right]; rw [show ∀ p q : AF D.host.F, (p + q).1 = p.1 + q.1 from fun _ _ => rfl,
      map_add]; ring)
  have hc : Continuous c := by
    have h1 : Continuous fun u => symplOH S T (M t) (M u) := (continuous_symplOH_right _).comp hM.1
    exact (hΛ.comp (continuous_fst.comp h1)).neg
  set ℓ := AddMonoidHom.toRealLinearMap c hc
  have hℓ : ‖ℓ‖ ≤ Bb * R := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    show ‖-Λ (symplOH S T (M t) (M u)).1‖ ≤ Bb * R * ‖u‖
    rw [norm_neg, beta_poly Λ hΛ M hM.1 t u]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖∑ j, (t i : ℂ) * (u j : ℂ) * b i j‖ ≤ ∑ i, ∑ j, ‖t‖ * ‖u‖ * ‖b i j‖ := by
          refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
          gcongr
          · exact norm_le_pi_norm t i
          · exact norm_le_pi_norm u j
      _ = ‖t‖ * ‖u‖ * Bb := by simp only [Bb, Finset.mul_sum]
      _ = ‖t‖ * (‖u‖ * Bb) := by ring
      _ ≤ R * (‖u‖ * Bb) := mul_le_mul_of_nonneg_right ht (mul_nonneg (norm_nonneg u) hBb)
      _ = Bb * R * ‖u‖ := by ring

  have hid : (fun u => Gf ψ M f y (u + t)) =
      fun u => ψ (symplOH S T y (M t)) • (Complex.exp (ℓ u) * Gf ψ M f (y + M t) u) := by
    funext u
    have hru : eInf D • M u = M u := (wo_real_iff _).mp (hM.2.1 u)
    have hneg : ψ (-(symplOH S T (M t) (M u))) = Complex.exp (ℓ u) := by
      rw [hψΛ _ (by show -(symplOH S T (M t) (M u)).2 = 0; rw [symplOH_snd _ _ hru, neg_zero])]
      rw [show (-(symplOH S T (M t) (M u))).1 = -(symplOH S T (M t) (M u)).1 from rfl, map_neg]
      rfl
    simp only [Gf, heisO, smul_eq_mul, map_add]
    rw [← hneg, symplOH_add_right, symplOH_add_left, show y + (M u + M t) = y + M t + M u by abel]
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    abel
  have e1 : iteratedFDeriv ℝ n (Gf ψ M f y) t = iteratedFDeriv ℝ n (fun u => Gf ψ M f y (u + t)) 0 := by
    rw [iteratedFDeriv_comp_add_right, zero_add]
  rw [e1, hid]
  have h2 : ContDiff ℝ ∞ fun u => Complex.exp (ℓ u) * Gf ψ M f (y + M t) u :=
    ((Complex.contDiff_exp (𝕜 := ℝ)).comp ℓ.contDiff).mul (hs _)
  have e2 : (fun u => ψ (symplOH S T y (M t)) • (Complex.exp (ℓ u) * Gf ψ M f (y + M t) u)) =
      ψ (symplOH S T y (M t)) • fun u => Complex.exp (ℓ u) * Gf ψ M f (y + M t) u := rfl
  have h2' : ContDiff ℝ n fun u => Complex.exp (ℓ u) * Gf ψ M f (y + M t) u := h2.of_le (natCast_lt_inf n).le
  rw [e2]
  first
    | rw [iteratedFDeriv_const_smul_apply h2']
    | rw [iteratedFDeriv_const_smul_apply h2'.contDiffAt]
  rw [norm_smul, hψu, one_mul]
  have h1 : ContDiff ℝ ∞ fun u => Complex.exp (ℓ u) := (Complex.contDiff_exp (𝕜 := ℝ)).comp ℓ.contDiff
  refine (norm_iteratedFDeriv_mul_le h1 (hs _) 0 (natCast_lt_inf n).le).trans (Finset.sum_le_sum fun i hi => ?_)
  have he : ‖iteratedFDeriv ℝ i (fun u => Complex.exp (ℓ u)) 0‖ ≤ (Bb * R) ^ i := by
    refine (norm_iter_exp ℓ i 0).trans ?_
    rw [map_zero, Complex.exp_zero, norm_one, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) hℓ i
  have hg : ‖iteratedFDeriv ℝ (n - i) (Gf ψ M f (y + M t)) 0‖ ≤ Bd := by
    refine (mlin_norm_le _).trans ?_
    have hmi : n - i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    calc ∑ l : Fin (n - i) → Fin k, ‖iteratedFDeriv ℝ (n - i) (Gf ψ M f (y + M t)) 0 (fun j => ev (l j))‖
        ≤ ∑ l : Fin (n - i) → Fin k, Cb (n - i) l := Finset.sum_le_sum fun l _ => hCb (n - i) l _
      _ ≤ Bd := Finset.single_le_sum (f := fun m => ∑ l : Fin m → Fin k, Cb m l)
          (fun m _ => Finset.sum_nonneg fun l _ => (norm_nonneg _).trans (hCb m l 0)) hmi
  have hc0 : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun u => Complex.exp (ℓ u)) 0‖ *
        ‖iteratedFDeriv ℝ (n - i) (Gf ψ M f (y + M t)) 0‖
      ≤ (n.choose i : ℝ) * (Bb * R) ^ i * Bd := by
        gcongr

end Formalism.IndefR.Eqv

end
