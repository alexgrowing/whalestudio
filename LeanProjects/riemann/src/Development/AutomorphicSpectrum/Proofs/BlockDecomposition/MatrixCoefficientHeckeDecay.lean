import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormPowLeOfEigenvaluesLt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactKm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorsCommuteOnFixed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCoweightAntitonePairingSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCoweightAdditiveFundamental

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CoeffBound

theorem exists_radius {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : Module.End ℂ W) (b : ℝ) (hb0 : 0 < b)
    (hb : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ < b) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < b ∧ ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ < ρ := by
  classical
  have hfin : Set.Finite (T.HasEigenvalue : Set ℂ) := Module.End.finite_hasEigenvalue T
  let s : Finset ℝ := insert 0 (hfin.toFinset.image fun μ => ‖μ‖)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  have hM : s.max' hs < b := by
    rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hb0
    · obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.1 hy
      exact hb μ (hfin.mem_toFinset.1 hμ)
  have h0 : 0 ≤ s.max' hs := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  refine ⟨(s.max' hs + b) / 2, by linarith, by linarith, fun μ hμ => ?_⟩
  have h1 : ‖μ‖ ≤ s.max' hs := Finset.le_max' _ _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hμ)))
  linarith

theorem exists_coordinates (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    ∃ (d : ℕ) (e : W ≃ₗ[ℂ] (Fin d → ℂ))
      (φ : Module.End ℂ W →ₐ[ℂ] ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))),
      (∀ (S : Module.End ℂ W) (x : W), φ S (e x) = e (S x)) ∧
      ∀ (S : Module.End ℂ W) (μ : ℂ),
        Module.End.HasEigenvalue ((φ S : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) : Module.End ℂ (Fin d → ℂ)) μ →
          S.HasEigenvalue μ := by
  let e : W ≃ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun
  let φ : Module.End ℂ W →ₐ[ℂ] ((Fin (Module.finrank ℂ W) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ W) → ℂ)) :=
    (Module.End.toContinuousLinearMap (𝕜 := ℂ) (Fin (Module.finrank ℂ W) → ℂ)).toAlgHom.comp
      (e.conjAlgEquiv ℂ).toAlgHom
  have hφ : ∀ (S : Module.End ℂ W) (x : Fin (Module.finrank ℂ W) → ℂ), φ S x = e (S (e.symm x)) := by
    intro S x
    simp [φ, LinearEquiv.conjAlgEquiv_apply]
    rfl
  refine ⟨_, e, φ, fun S x => by rw [hφ]; simp, fun S μ h => ?_⟩
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  have hx1 : φ S x = μ • x := Module.End.mem_eigenspace_iff.1 hx.1
  rw [hφ] at hx1
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := e.symm x)
    ⟨Module.End.mem_eigenspace_iff.2 ?_, fun h0 => hx.2 (by simpa using h0)⟩
  apply e.injective
  rw [hx1]
  simp

theorem diagPow_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) : Zls.diagPow k N 0 = 1 := by
  refine Units.ext ?_
  ext i j
  simp [Zls.diagPow, Matrix.one_apply, Matrix.diagonal_apply]

theorem lamOf_zero (N : ℕ) : Zls.lamOf (0 : Fin (N - 1) → ℕ) = 0 := by
  funext i
  simp [Zls.lamOf]

theorem hecke_pow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hsm : IsSmooth π) {m : ℕ} (hm : 1 ≤ m)
    (j : Fin (N - 1)) (T : Module.End ℂ (fixed π (Zls.Km k N m)))
    (hT : Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N ((j : ℕ) + 1))) T) (n : ℕ) :
    Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.lamOf (Pi.single j n : Fin (N - 1) → ℕ))) (T ^ n) := by
  induction n with
  | zero =>
    rw [Pi.single_zero, lamOf_zero, diagPow_zero, pow_zero]
    intro v l _
    simp
  | succ n ih =>
    have hs : (Pi.single j (n + 1) : Fin (N - 1) → ℕ) = Pi.single j n + Pi.single j 1 := by
      rw [← Pi.single_add]
    rw [hs, ((GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).1 _ _), pow_succ]
    refine GlobalTheory.CompanionTheory.HeckeOpMul.isHeckeOp_mul k N V π hsm m hm _ _ ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) _ _ ih ?_
    rw [(GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).2 j]
    exact hT

theorem radius_sq_lt {q ρ : ℝ} (hq : 0 < q) (a : ℕ) (h0 : 0 ≤ ρ)
    (h : ρ < q ^ (-((a : ℝ) / 2))) : q ^ a * ρ ^ 2 < 1 := by
  have h1 : ρ ^ 2 < (q ^ (-((a : ℝ) / 2))) ^ 2 := pow_lt_pow_left₀ h h0 (by norm_num)
  have h2 : (q ^ (-((a : ℝ) / 2))) ^ 2 = (q ^ a)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast q a, ← Real.rpow_neg hq.le]
    congr 1
    push_cast
    ring
  rw [h2] at h1
  have h3 : 0 < q ^ a := pow_pos hq a
  calc q ^ a * ρ ^ 2 < q ^ a * (q ^ a)⁻¹ := mul_lt_mul_of_pos_left h1 h3
    _ = 1 := mul_inv_cancel₀ h3.ne'

theorem coeff_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → IsAdmissible π → Zls.HeckeSpectral π → ∀ m : ℕ, 1 ≤ m → ∀ v ∈ fixed π (Zls.Km k N m), ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧ (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ 2 < 1) ∧ ∀ g : Fin (N - 1) → ℕ, ‖l (π (Zls.diagPow k N (Zls.lamOf g)) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
  intro k _ _ _ _ N V _ _ π hsm hadm hsp m hm v hv l hl
  have hfd : FiniteDimensional ℂ (fixed π (Zls.Km k N m)) :=
    hadm.2 _ (GlobalTheory.CompanionTheory.KmTop.isOpen_Km N m) (GlobalTheory.CompanionTheory.KmTop.isCompact_Km N m)
  have hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ) := by
    exact_mod_cast Nat.card_pos
  obtain ⟨d, e, φ, hφ, hev⟩ := exists_coordinates (fixed π (Zls.Km k N m))
  choose T hT using fun j : Fin (N - 1) =>
    GlobalTheory.CompanionTheory.HeckeKm.exists_isHeckeOp k N V π hsm m (Zls.diagPow k N (Zls.omegaVec N ((j : ℕ) + 1)))
  have hrad := fun j : Fin (N - 1) => exists_radius (T j) _ (Real.rpow_pos_of_pos hq
      (-(((((((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) : ℕ) : ℝ)) / 2)))
    (fun μ hμ => hsp m hm ((j : ℕ) + 1) (by omega) (by omega) (T j) (hT j) μ hμ)
  choose ρ hρ0 hρb hρe using hrad
  have hC := fun j : Fin (N - 1) => GlobalTheory.CompanionTheory.SpecBound.norm_pow_le_of_eigenvalues_lt (Fin d → ℂ) (φ (T j)) (ρ j)
    (fun μ hμ => hρe j μ (hev _ _ hμ))
  choose C hC using hC
  have hprod : ∀ (g : Fin (N - 1) → ℕ) (s : Finset (Fin (N - 1))),
      ∃ S : Module.End ℂ (fixed π (Zls.Km k N m)),
        Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.lamOf fun j => if j ∈ s then g j else 0)) S ∧
        ‖φ S‖ ≤ ∏ j ∈ s, C j * ρ j ^ g j := by
    classical
    intro g s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, ?_, ?_⟩
      · have h0 : (fun j : Fin (N - 1) => if j ∈ (∅ : Finset (Fin (N - 1))) then g j else 0) = 0 := by
          funext j; simp
        rw [h0, lamOf_zero, diagPow_zero]
        intro v l _
        simp
      · rw [map_one, Finset.prod_empty]
        exact ContinuousLinearMap.norm_id_le
    | insert a s ha ih =>
      obtain ⟨S, hS, hn⟩ := ih
      refine ⟨T a ^ g a * S, ?_, ?_⟩
      · have hsplit : (fun j : Fin (N - 1) => if j ∈ insert a s then g j else 0) =
            (Pi.single a (g a) : Fin (N - 1) → ℕ) + fun j => if j ∈ s then g j else 0 := by
          funext j
          by_cases hj : j = a
          · subst hj
            simp [ha]
          · simp [hj]
        rw [hsplit, (GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).1]
        exact GlobalTheory.CompanionTheory.HeckeOpMul.isHeckeOp_mul k N V π hsm m hm _ _ ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) _ _
          (hecke_pow π hsm hm a (T a) (hT a) (g a)) hS
      · rw [map_mul, map_pow, Finset.prod_insert ha]
        exact (norm_mul_le _ _).trans (mul_le_mul (hC a (g a)) hn (norm_nonneg _)
          ((norm_nonneg _).trans (hC a (g a))))
  let L : (Fin d → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (l ∘ₗ (fixed π (Zls.Km k N m)).subtype ∘ₗ (e.symm : (Fin d → ℂ) →ₗ[ℂ] _))
  let w : Fin d → ℂ := e ⟨v, hv⟩
  refine ⟨‖L‖ * ‖w‖ * ∏ j, C j, ρ, hρ0, fun j => ?_, fun g => ?_⟩
  · exact radius_sq_lt hq _ (hρ0 j) (hρb j)
  · obtain ⟨S, hS, hn⟩ := hprod g Finset.univ
    have hg : (fun j : Fin (N - 1) => if j ∈ (Finset.univ : Finset (Fin (N - 1))) then g j else 0) = g := by
      funext j; simp
    rw [hg] at hS
    have h1 : l (π (Zls.diagPow k N (Zls.lamOf g)) v) = L (φ S w) := by
      rw [show π (Zls.diagPow k N (Zls.lamOf g)) v = π (Zls.diagPow k N (Zls.lamOf g)) ((⟨v, hv⟩ : fixed π (Zls.Km k N m)) : V) from rfl,
        hS ⟨v, hv⟩ l hl, hφ]
      simp [L]
    rw [h1, Finset.prod_mul_distrib] at *
    calc ‖L (φ S w)‖ ≤ ‖L‖ * ‖φ S w‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖φ S‖ * ‖w‖) := by gcongr; exact (φ S).le_opNorm _
      _ ≤ ‖L‖ * ((∏ j, C j) * (∏ j, ρ j ^ g j) * ‖w‖) := by gcongr
      _ = ‖L‖ * ‖w‖ * (∏ j, C j) * ∏ j, ρ j ^ g j := by ring

end GlobalTheory.CompanionTheory.CoeffBound
