import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType

noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

variable {n : ℕ}

theorem isLev_id (lam : Fin n → ℤ) : IsLev lam fun a => ((a : Fin n) : ℕ) := ⟨fun _ _ h => h, fun _ _ h => congrArg lam (Fin.ext h)⟩

theorem mem_harmSet {lam : Fin n → ℤ} {μ : Fin n → ℝ} (h : μ ∈ harmSet lam) :
    ∃ l : Fin n → Fin n, IsLev lam (fun a => (l a : ℕ)) ∧ μ = muQ lam fun a => (l a : ℕ) := by
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨l, hl, rfl⟩ := h
  exact ⟨l, hl, rfl⟩

theorem muQ_mem_harmSet {lam : Fin n → ℤ} (lev : Fin n → Fin n) (h : IsLev lam fun a => (lev a : ℕ)) :
    muQ lam (fun a => (lev a : ℕ)) ∈ harmSet lam := by
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨lev, h, rfl⟩

def Compress : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
    ∃ l : Fin n → Fin n, IsLev lam (fun a => (l a : ℕ)) ∧ muQ lam (fun a => (l a : ℕ)) = muQ lam lev

theorem multG_of (hCp : Compress) (hM : MultFor) (hA : AdmLeast) (h1 : N1) (hC : ConeWeightsNotSecondType) (hE : ModelEx) (h7 : KTypeGenerationHighest) : MultG := by
  intro n lam hl V _ _ E1 E2 σ A hc
  classical
  have hne_h : (harmSet lam).Nonempty := ⟨_, muQ_mem_harmSet (fun a => a) (isLev_id lam)⟩
  by_cases hex : ∃ μ ∈ harmSet lam, hwSp E1 E2 μ ≠ ⊥
  swap
  · push_neg at hex
    obtain ⟨μ₀, hμ₀⟩ := hne_h
    refine ⟨μ₀, hμ₀, fun μ hμ _ => hex μ hμ, ?_⟩
    intro v w hv _ hv0
    rw [hex μ₀ hμ₀, Submodule.mem_bot] at hv
    exact absurd hv hv0
  obtain ⟨μ₁, hμ₁, hne₁⟩ := hex
  let S := (harmSet lam).filter (fun μ => hwSp E1 E2 μ ≠ ⊥)
  have hSne : S.Nonempty := ⟨μ₁, Finset.mem_filter.mpr ⟨hμ₁, hne₁⟩⟩
  obtain ⟨μ₀, hμ₀S, hmin⟩ := S.exists_min_image (fun μ => nsq (μ + rhoV n)) hSne
  obtain ⟨hμ₀, hne₀⟩ := Finset.mem_filter.mp hμ₀S
  obtain ⟨l0, hl0, rfl⟩ := mem_harmSet hμ₀
  have hadm : AdmFor lam (fun a => (l0 a : ℕ)) E1 E2 := by
    refine hA n lam hl V E1 E2 σ A hc _ hl0 hne₀ ?_
    intro lev' hlev' hne'
    obtain ⟨l', hl', heq⟩ := hCp n lam lev' hlev'
    have hmem : muQ lam lev' ∈ S := by
      refine Finset.mem_filter.mpr ⟨?_, hne'⟩
      rw [← heq]
      exact muQ_mem_harmSet l' hl'
    exact hmin _ hmem
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne₀
  refine ⟨_, hμ₀, ?_, ?_⟩
  · intro μ hμ hμne
    by_contra hb
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨M⟩ := hE n lam hl _ hl0
    have hMn2 : ∀ ν, IsSecondTypeWeight lam (fun a => (l0 a : ℕ)) ν → hwSp M.F1 M.F2 ν = ⊥ := by
      intro ν hν
      letI := M.nacg
      letI := M.ips
      rw [Submodule.eq_bot_iff]
      intro y hy
      by_contra hy0
      exact hC n lam hl _ hl0 ν (M.cone ν y hy hy0) hν
    obtain ⟨a, ha, hav⟩ := hc.irr v x hv0
    have hcone := h7 hM n lam hl _ hl0 V E1 E2 hc.pair hadm M hMn2 v hv hv0 μ x hx hx0 ⟨a, ha, hav⟩
    obtain ⟨l', hl', rfl⟩ := mem_harmSet hμ
    exact hμne (h1 n lam hl _ _ hl0 hl' hcone)
  · intro v' w hv' hw hv'0
    obtain ⟨a, ha, hav⟩ := hc.irr v' w hv'0
    exact hM n lam hl _ hl0 V E1 E2 hadm v' w hv' hw hv'0 ⟨a, ha, hav⟩

end PositivityTheory.RgBcC.RealD
