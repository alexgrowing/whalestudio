import Mathlib

open scoped InnerProductSpace

namespace Formalism.IndefR.EigenDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem exists_onb_of_parts {I : Type*} [Finite I] (P : I → Submodule ℂ H)
    (horth : ∀ i j, i ≠ j → P i ⟂ P j) (htop : ⨆ i, P i = ⊤) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H) (lab : Fin n → I), ∀ k, b k ∈ P (lab k) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  have hV : OrthogonalFamily ℂ (fun i => P i) (fun i => (P i).subtypeₗᵢ) :=
    fun i j hij v w => (horth i j hij).inner_eq v.2 w.2
  have hint : DirectSum.IsInternal (fun i => P i) := by
    rw [hV.isInternal_iff, htop, Submodule.top_orthogonal_eq_bot]
  let b := hint.collectedOrthonormalBasis hV (fun i => stdOrthonormalBasis ℂ (P i))
  let e := Fintype.equivFin (Σ i, Fin (Module.finrank ℂ (P i)))
  refine ⟨_, b.reindex e, fun k => (e.symm k).1, fun k => ?_⟩
  rw [OrthonormalBasis.reindex_apply]
  exact hint.collectedOrthonormalBasis_mem hV _ _

theorem exists_onb_of_parts_set {L : Type*} (S : Set L) (hS : S.Finite) (P : L → Submodule ℂ H)
    (horth : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → P c ⟂ P d) (htop : ⨆ c ∈ S, P c = ⊤) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H) (lab : Fin n → L),
      (∀ k, lab k ∈ S) ∧ ∀ k, b k ∈ P (lab k) := by
  classical
  have hfin : Finite S := hS.to_subtype
  obtain ⟨n, b, lab, hb⟩ := exists_onb_of_parts (fun c : S => P c.1)
    (fun c d hcd => horth c.1 c.2 d.1 d.2 (fun h => hcd (Subtype.ext h)))
    (by rw [← htop, iSup_subtype'])
  exact ⟨n, b, fun k => (lab k).1, fun k => (lab k).2, hb⟩

noncomputable def reIm (T : H →ₗ[ℂ] H) (b : Bool) : H →ₗ[ℂ] H :=
  if b then T + LinearMap.adjoint T else Complex.I • (T - LinearMap.adjoint T)

theorem reIm_isSymmetric (T : H →ₗ[ℂ] H) (b : Bool) : (reIm T b).IsSymmetric := by
  intro x y
  cases b <;>
    simp [reIm, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right] <;> ring

theorem exists_onb_of_commuting (A : Set (H →ₗ[ℂ] H))
    (hcomm : ∀ S ∈ A, ∀ T ∈ A, Commute S T)
    (hadj : ∀ T ∈ A, LinearMap.adjoint T ∈ A) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H), ∀ k, ∀ T ∈ A, ∃ μ : ℂ, T (b k) = μ • b k := by
  classical
  obtain ⟨B, hBA, hspan, hli⟩ := exists_linearIndependent ℂ A
  have hBfin : B.Finite := hli.setFinite
  have : Fintype B := hBfin.fintype
  have r1 : ∀ S : H →ₗ[ℂ] H, reIm S true = S + LinearMap.adjoint S := fun S => by simp [reIm]
  have r2 : ∀ S : H →ₗ[ℂ] H, reIm S false = Complex.I • (S - LinearMap.adjoint S) :=
    fun S => by simp [reIm]

  have cl : ∀ (S X : H →ₗ[ℂ] H) (β : Bool), Commute S X → Commute (LinearMap.adjoint S) X →
      Commute (reIm S β) X := by
    intro S X β h1 h2
    cases β
    · rw [r2]; exact (h1.sub_left h2).smul_left _
    · rw [r1]; exact h1.add_left h2
  have cr : ∀ (S X : H →ₗ[ℂ] H) (β : Bool), Commute X S → Commute X (LinearMap.adjoint S) →
      Commute X (reIm S β) := fun S X β h1 h2 => (cl S X β h1.symm h2.symm).symm
  have hc : ∀ S ∈ A, ∀ S' ∈ A, ∀ β β', Commute (reIm S β) (reIm S' β') := by
    intro S hS S' hS' β β'
    exact cl _ _ _ (cr _ _ _ (hcomm S hS S' hS') (hcomm S hS _ (hadj S' hS')))
      (cr _ _ _ (hcomm _ (hadj S hS) S' hS') (hcomm _ (hadj S hS) _ (hadj S' hS')))
  let F : B × Bool → Module.End ℂ H := fun p => reIm p.1.1 p.2
  have hsym : ∀ p, (F p).IsSymmetric := fun p => reIm_isSymmetric _ _
  have hpair : Pairwise (Function.onFun Commute F) := fun p q _ =>
    hc _ (hBA p.1.2) _ (hBA q.1.2) p.2 q.2
  have hint := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hsym hpair
  have hV := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hsym
  let E : (B × Bool → ℂ) → Submodule ℂ H := fun α => ⨅ j, (F j).eigenspace (α j)
  have hfinS : ({α | E α ≠ ⊥} : Set (B × Bool → ℂ)).Finite := by
    have : Fintype {α // E α ≠ ⊥} := hint.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
    exact Set.finite_coe_iff.mp (Finite.of_fintype {α // E α ≠ ⊥})
  have hortho : ∀ c ∈ {α | E α ≠ ⊥}, ∀ d ∈ {α | E α ≠ ⊥}, c ≠ d → E c ⟂ E d :=
    fun c _ d _ hcd => hV.isOrtho hcd
  have htop' : ⨆ c ∈ {α | E α ≠ ⊥}, E c = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hint.submodule_iSup_eq_top]
    refine iSup_le fun α => ?_
    by_cases h : E α = ⊥
    · show E α ≤ _
      rw [h]; exact bot_le
    · exact le_biSup E (show α ∈ {α | E α ≠ ⊥} from h)
  obtain ⟨n, b, lab, -, hb⟩ := exists_onb_of_parts_set _ hfinS E hortho htop'
  refine ⟨n, b, fun k => ?_⟩
  have hv : ∀ p, F p (b k) = lab k p • b k := fun p =>
    Module.End.mem_eigenspace_iff.1 (Submodule.mem_iInf _ |>.1 (hb k) p)

  have hB : ∀ S (hS : S ∈ B), ∃ μ : ℂ, S (b k) = μ • b k := by
    intro S hS
    have e1 : S (b k) + LinearMap.adjoint S (b k) = lab k (⟨S, hS⟩, true) • b k := by
      have := hv (⟨S, hS⟩, true)
      simpa [F, r1] using this
    have e2 : Complex.I • (S (b k) - LinearMap.adjoint S (b k)) = lab k (⟨S, hS⟩, false) • b k := by
      have := hv (⟨S, hS⟩, false)
      simpa [F, r2] using this
    have e2' : S (b k) - LinearMap.adjoint S (b k) = (-Complex.I * lab k (⟨S, hS⟩, false)) • b k := by
      rw [mul_smul, ← e2, smul_smul]
      simp
    have e3 : (2 : ℂ) • S (b k) =
        (lab k (⟨S, hS⟩, true) + -Complex.I * lab k (⟨S, hS⟩, false)) • b k := by
      rw [two_smul, add_smul, ← e1, ← e2']
      abel
    refine ⟨(1 / 2 : ℂ) * (lab k (⟨S, hS⟩, true) + -Complex.I * lab k (⟨S, hS⟩, false)), ?_⟩
    calc S (b k) = (1 / 2 : ℂ) • ((2 : ℂ) • S (b k)) := by rw [smul_smul]; norm_num
      _ = _ := by rw [e3, smul_smul]
  intro T hT
  have hT' : T ∈ Submodule.span ℂ B := hspan ▸ Submodule.subset_span hT
  clear hT
  induction hT' using Submodule.span_induction with
  | mem x hx => exact hB x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨μ₁, h₁⟩ := hx
    obtain ⟨μ₂, h₂⟩ := hy
    exact ⟨μ₁ + μ₂, by rw [LinearMap.add_apply, h₁, h₂, add_smul]⟩
  | smul a x _ hx =>
    obtain ⟨μ, h⟩ := hx
    exact ⟨a * μ, by rw [LinearMap.smul_apply, h, smul_smul]⟩

end Formalism.IndefR.EigenDecomposition
