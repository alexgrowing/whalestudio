import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Compact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigKfin

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

theorem stdGap_of_mir {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hlam : Formalism.QuantumDeterminants.IsHCParam lam)
    (hh : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hlt : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) : StdGap ε lam := ⟨hlam.1, h, hh, hlt⟩

theorem all_smooth_of_kType {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)
    {σ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hDS : Formalism.MainNotions.S.IsDS ε lam σ)
    (hK : ∀ k : S7.KG ε, σ (S7.toMK k) = T.op k) (v : T.V) : IsSmoothVecU ε σ v := by
  obtain ⟨-, -, hσ, hirr, -, ⟨S, hS⟩, -⟩ := hDS
  have hinv : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ w ∈ smD ε σ, σ g w ∈ smD ε σ := by
    intro g hg w hw
    rw [mem_smD_iff] at hw ⊢
    unfold IsSmoothVecU at hw ⊢
    let _ : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
    let _ : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
    intro g₀ hg₀
    obtain ⟨U, F, hU, hmem, hF, hEq⟩ := hw (g₀ * g) (pdA_inUJ_mul hg₀ hg)
    let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)
    have hL : ∀ x, L x = x * g := fun x => rfl
    refine ⟨L ⁻¹' U, F ∘ L, hU.preimage L.continuous, by simpa [hL] using hmem,
      hF.comp L.contDiff.contDiffOn (fun x hx => hx), ?_⟩
    intro x hx hxUJ
    have hx' : x * g ∈ U := by simpa [hL] using hx
    have hrep := hσ.1.2 x hxUJ g hg
    simp only [Function.comp_apply, hL]
    rw [← hEq (x * g) hx' (pdA_inUJ_mul hxUJ hg)]
    show σ x (σ g w) = σ (x * g) w
    rw [hrep]
    rfl
  have hne : smD ε σ ≠ ⊥ := by
    obtain ⟨V, -, hV0, -⟩ := exists_datum_of_isKTypeOf hσ hS
    intro hbot
    apply hV0
    have : Subsingleton (smD ε σ) := by
      rw [hbot]
      infer_instance
    exact Subsingleton.elim _ _
  have hcl : IsClosed ((smD ε σ : Submodule ℂ T.V) : Set T.V) := Submodule.closed_of_finiteDimensional _
  rcases hirr (smD ε σ) hcl hinv with h | h
  · exact absurd h hne
  · have hv : v ∈ smD ε σ := by
      rw [h]
      exact Submodule.mem_top
    exact (mem_smD_iff ε σ v).mp hv

theorem dsExistsG (hS7 : ∀ m : ℕ, S7.PsiExistsStatement m) :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
          (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) < h →
        ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
          (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
          Formalism.MainNotions.S.IsDS ε lam σ ∧ CasOnSmooth ε lam σ ∧
          (∀ S S' : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S →
            Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S') ∧
          (∀ μ : Fin n → ℝ, FiniteDimensional ℂ (sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} :
            Submodule ℂ H)) ∧
          (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε σ S →
            ∀ v ∈ S, IsSmoothVecU ε σ v) := by
  intro n ε lam hlam h hh hmax
  have h1 : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h := lt_of_le_of_lt (le_max_left _ _) hmax
  have h2 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) < h :=
    lt_of_le_of_lt (le_max_right _ _) hmax
  have hgap : StdGap ε lam := stdGap_of_mir hlam hh h1
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  rcases Nat.eq_zero_or_pos (S7.q0 ε) with hq | hq
  · have hm : min (pOf ε) (qOf ε) = 0 := hq
    have hpq : pOf ε = 0 ∨ qOf ε = 0 := by omega
    obtain ⟨σ, hDS, hcas, hK⟩ := isDS_compact hpq hlam T
    refine ⟨T.V, inferInstance, inferInstance, σ, hDS, hcas, ?_, ?_, ?_⟩
    · intro S S' hS hS'
      exact lowKMultOne_of_cas hDS hgap hcas S S' hS hS'
    · intro μ
      infer_instance
    · intro S _ _ v _
      exact all_smooth_of_kType T hDS hK v
  · have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
      have hs : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
      have hn : 0 ≤ (n : ℝ) * S7.q0 ε := by positivity
      nlinarith
    obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor (hS7 n) T hlam hh hq h8
    have hv₀ : T.w ≠ 0 := by
      intro h0
      have h1' := T.w_norm
      rw [h0, norm_zero] at h1'
      exact zero_ne_one h1'
    refine ⟨Hlam ε Ψ T.w, inferInstance, inferInstance, sigLam ε Ψ T.w, ?_, ?_, ?_, ?_, ?_⟩
    · exact isDS_sigLam hgap hP hv₀
    · exact sigLam_casOnSmooth hgap hP hv₀
    · intro S S' hS hS'
      obtain ⟨-, huniq⟩ := sigLam_lowK hgap hP hv₀
      rw [huniq S hS, huniq S' hS']
    · exact sigLam_admissible hgap hP hv₀
    · intro S hSf hSK v hv
      exact sigLam_kfin_smooth hgap hP hv₀ v (sigLam_kfin hgap hP hv₀ S hSf hSK hv)

theorem lowKMultOneG_of_cas :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h →
      CasOnSmooth ε lam σ →
      ∀ S S' : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S →
        Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S' := by
  intro n ε lam H _ _ σ hlam hDS h hh hlt hcas S S' hS hS'
  have : CompleteSpace H := hDS.1
  exact lowKMultOne_of_cas hDS (stdGap_of_mir hlam hh hlt) hcas S S' hS hS'

end ReciprocityTheory.ChartRestriction.DS
