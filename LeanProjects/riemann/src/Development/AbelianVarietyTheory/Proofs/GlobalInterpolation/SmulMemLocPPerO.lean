import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerOComponents

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.PeriodTwist

open GlobalTheory.ThetaMove.PeriodComp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem smul_mem_locP_perO (AA : Submodule (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E a)} (hN : N.FG)
    {N' M' : Submodule (𝓞 E) (Sp E b)} (k : E) (h : ∀ y ∈ localization₂ Q.asIdeal N', k • y ∈ localization₂ Q.asIdeal M')
    {x : HomE E a b} (hx : x ∈ localization₂ Q.asIdeal (perO AA N N')) : k • x ∈ localization₂ Q.asIdeal (perO AA N M') := by
  have key : ∀ z ∈ perO AA N N', k • z ∈ localization₂ Q.asIdeal (perO AA N M') := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨r, hr, x, hx, rfl⟩ := hz
      obtain ⟨s, hs, hsx⟩ := exists_common Q.asIdeal.primeCompl hN M' (k • x) fun y hy =>
        h _ (mem_localization_of_mem Q (hx _ hy))
      refine ⟨s, hs, ?_⟩
      rw [smul_comm k r, smul_comm s r]
      exact smul_mem_perO hr hsx
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy
  obtain ⟨s, hs, hx⟩ := hx
  rw [← localization_localization₂]
  exact ⟨s, hs, by rw [smul_comm]; exact key _ hx⟩

theorem twO_perO : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), N.FG → 0 < c → (∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) → twist₂ (perO AA N N') c e = perO AA N (twist₂ N' c e) := by
  intro E _ _ _ a b AA N N' c e hN hc he
  have hk : ∀ Q, ((c : E) ^ e Q) ≠ 0 := fun Q => zpow_ne_zero _ (by exact_mod_cast hc.ne')
  apply le_antisymm
  · intro x hx
    refine mem_of_locP fun Q => ?_
    have h1 := (mem_localization_twist _ hc he Q x).1 (mem_localization_of_mem Q hx)
    have h2 := smul_mem_locP_perO AA Q hN (M' := twist₂ N' c e) ((c : E) ^ e Q) (fun y hy => by
      rw [mem_localization_twist _ hc he, inv_smul_smul₀ (hk Q)]; exact hy) h1
    rwa [smul_inv_smul₀ (hk Q)] at h2
  · intro x hx
    refine mem_of_locP fun Q => ?_
    rw [mem_localization_twist _ hc he]
    exact smul_mem_locP_perO AA Q hN _ (fun y hy => (mem_localization_twist _ hc he Q y).1 hy) (mem_localization_of_mem Q hx)

end GlobalTheory.ThetaMove.PeriodTwist
