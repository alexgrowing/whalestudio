import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatReindexRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormFullRankBoxVanishesStatement
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv

noncomputable section
namespace GlobalTheory.RankStrata

theorem pairing_eq_zero_of_kills_lowRank : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n l d : ℕ) (ν : kˣ →* ℂˣ) (ϖ : kˣ), n < d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Bf : fullRk k n d →ₗ[ℂ] SB (Matrix (Fin l) (Fin d) k) →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' : fullRk k n d) (Ψ₂ : SB (Matrix (Fin l) (Fin d) k)), Ψ₁'.1 = lact ν g Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ (Ψ₁ Ψ₁' : fullRk k n d) (Ψ₂ Ψ₂' : SB (Matrix (Fin l) (Fin d) k)),
        Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      (∀ (Ψ₁ : fullRk k n d) (Ψ₂ : SB (Matrix (Fin l) (Fin d) k)),
        (∀ Y : Matrix (Fin l) (Fin d) k, Y.rank < n → Ψ₂.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0) →
      ∀ Ψ₁ Ψ₂, Bf Ψ₁ Ψ₂ = 0 := by
  intro hKP k _ _ _ _ n l d ν ϖ hnd hsm hun hν Bf hGLn hGLd hlow
  classical

  have piece : ∀ ρ < n, (∀ (Ψ₁ : fullRk k n d) (Ψ₂ : SB (Matrix (Fin l) (Fin d) k)),
        (∀ Y : Matrix (Fin l) (Fin d) k, Y.rank < ρ + 1 → Ψ₂.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0) →
      ∀ (Ψ₁ : fullRk k n d) (f : Matrix (Fin l) (Fin d) k → ℂ) (hf : f ∈ SB (Matrix (Fin l) (Fin d) k))
        (S : Fin ρ → Fin l) (τ : Fin ρ → Fin d), (∀ Y, f Y ≠ 0 → (Y.submatrix S τ).det ≠ 0) →
        Bf Ψ₁ ⟨f, hf⟩ = 0 := by
    intro ρ hρ ih Ψ₁ f hf S τ hS
    by_cases h0 : ∀ Y, f Y = 0
    · have : (⟨f, hf⟩ : SB (Matrix (Fin l) (Fin d) k)) = 0 := Subtype.ext (funext h0)
      rw [this, map_zero]
    push_neg at h0
    obtain ⟨Y0, hY0⟩ := h0
    have hinj : Function.Injective S := by
      intro i j hij
      by_contra hne
      exact hS Y0 hY0 (Matrix.det_zero_of_row_eq hne (by ext m; simp [hij]))
    let e' : Fin ρ ⊕ ↥(Set.range S)ᶜ ≃ Fin l :=
      (Equiv.sumCongr (Equiv.ofInjective S hinj) (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
    have he' : ∀ i, e'.symm (S i) = Sum.inl i := fun i => by
      rw [Equiv.symm_apply_eq]; simp [e']
    have hTo := (GlobalTheory.T.schwartzBruhat_reindex_rows k (Fin l) (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin d) ν e'.symm).1
    have hBack := (GlobalTheory.T.schwartzBruhat_reindex_rows k (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin l) (Fin d) ν e').1
    let L : SB (Matrix (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin d) k) →ₗ[ℂ] SB (Matrix (Fin l) (Fin d) k) :=
      { toFun := fun g => ⟨fun Y => g.1 (Y.submatrix e' id), by simpa using hTo g.1 g.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hL : ∀ g Y, (L g).1 Y = g.1 (Y.submatrix e' id) := fun _ _ => rfl
    let Bf' : fullRk k n d →ₗ[ℂ] SB (Matrix (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin d) k) →ₗ⋆[ℂ] ℂ := Bf.compl₂ L
    have hBf' : ∀ Ψ g, Bf' Ψ g = Bf Ψ (L g) := fun _ _ => rfl
    have hchart := GlobalTheory.T.invariant_form_full_rank_box_vanishes hKP k n ρ d (↥(Set.range S)ᶜ) ν ϖ hnd hρ hsm hun hν Bf'
      (fun g Ψ₁ Ψ₁' Ψ₂ h => by rw [hBf', hBf']; exact hGLn g Ψ₁ Ψ₁' (L Ψ₂) h)
      (fun h => by
        obtain ⟨m, hm, H⟩ := hGLd h
        refine ⟨m, hm, fun Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2 => ?_⟩
        rw [hBf', hBf']
        refine H Ψ₁ Ψ₁' (L Ψ₂) (L Ψ₂') h1 ?_
        funext Y
        rw [hL, hL, h2]
        congr 1)
      (fun Ψ₁ Ψ₂ hv => by
        rw [hBf']
        refine ih Ψ₁ (L Ψ₂) (fun Y hY => ?_)
        rw [hL]
        apply hv
        rw [show (id : Fin d → Fin d) = ⇑(Equiv.refl (Fin d)) from rfl, Matrix.rank_submatrix]
        omega)
      τ Ψ₁ ⟨fun Z => f (Z.submatrix e'.symm id), hBack f hf⟩
      (fun Z hZ => by
        have := hS _ hZ
        rwa [Matrix.submatrix_submatrix, show (e'.symm ∘ S) = Sum.inl from funext he'] at this)
    rw [hBf'] at hchart
    convert hchart using 2
    apply Subtype.ext
    funext Y
    rw [hL]
    simp [Matrix.submatrix_submatrix]
  have step : ∀ ρ < n, (∀ (Ψ₁ : fullRk k n d) (Ψ₂ : SB (Matrix (Fin l) (Fin d) k)),
        (∀ Y : Matrix (Fin l) (Fin d) k, Y.rank < ρ + 1 → Ψ₂.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0) →
      ∀ (Ψ₁ : fullRk k n d) (Ψ₂ : SB (Matrix (Fin l) (Fin d) k)),
        (∀ Y : Matrix (Fin l) (Fin d) k, Y.rank < ρ → Ψ₂.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0 := by
    intro ρ hρ ih Ψ₁ Ψ₂ hv
    haveI : T2Space k := by
      letI := IsTopologicalAddGroup.rightUniformSpace k
      haveI := isUniformAddGroup_of_addCommGroup (G := k)
      infer_instance
    have hsp := GlobalTheory.T.schwartzBruhat_partition_of_unity k (Fin l) (Fin d) ((Fin ρ → Fin l) × (Fin ρ → Fin d))
      (fun i => {Y : Matrix (Fin l) (Fin d) k | (Y.submatrix i.1 i.2).det ≠ 0})
      (fun i => isOpen_ne_fun ((continuous_id.matrix_submatrix i.1 i.2).matrix_det) continuous_const) Ψ₂.1 Ψ₂.2
      (fun Y hY => by
        have : ρ ≤ Y.rank := by
          by_contra h
          exact hY (hv Y (by omega))
        obtain ⟨S, τ, h⟩ := GlobalTheory.T.exists_nonzero_minor_of_rank k _ _ ρ Y this
        exact ⟨(S, τ), h⟩)
    have key := Submodule.span_induction
      (p := fun g _ => ∀ hg : g ∈ SB (Matrix (Fin l) (Fin d) k), Bf Ψ₁ ⟨g, hg⟩ = 0)
      (fun f hf hg => by
        obtain ⟨_, i, hi⟩ := hf
        exact piece ρ hρ ih Ψ₁ f hg i.1 i.2 hi)
      (fun hg => by
        have : (⟨0, hg⟩ : SB (Matrix (Fin l) (Fin d) k)) = 0 := rfl
        rw [this, map_zero])
      (fun x y hx hy px py hg => by
        have hxS : x ∈ SB (Matrix (Fin l) (Fin d) k) :=
          Submodule.span_le.mpr (fun g hg => hg.1) hx
        have hyS : y ∈ SB (Matrix (Fin l) (Fin d) k) :=
          Submodule.span_le.mpr (fun g hg => hg.1) hy
        have : (⟨x + y, hg⟩ : SB (Matrix (Fin l) (Fin d) k)) = ⟨x, hxS⟩ + ⟨y, hyS⟩ := rfl
        rw [this, map_add, px hxS, py hyS, add_zero])
      (fun c x hx px hg => by
        have hxS : x ∈ SB (Matrix (Fin l) (Fin d) k) :=
          Submodule.span_le.mpr (fun g hg => hg.1) hx
        have : (⟨c • x, hg⟩ : SB (Matrix (Fin l) (Fin d) k)) = c • ⟨x, hxS⟩ := rfl
        rw [this, map_smulₛₗ, px hxS, smul_zero])
      hsp
    exact key Ψ₂.2
  have ind : ∀ j ρ, ρ + j = n → ∀ (Ψ₁ : fullRk k n d) (Ψ₂ : SB (Matrix (Fin l) (Fin d) k)),
      (∀ Y : Matrix (Fin l) (Fin d) k, Y.rank < ρ → Ψ₂.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0 := by
    intro j
    induction j with
    | zero => intro ρ hρ; simp at hρ; subst hρ; exact hlow
    | succ j ihj =>
      intro ρ hρ
      exact step ρ (by omega) (ihj (ρ + 1) (by omega))
  intro Ψ₁ Ψ₂
  exact ind n 0 (by simp) Ψ₁ Ψ₂ (fun Y h => absurd h (Nat.not_lt_zero _))

end GlobalTheory.RankStrata
