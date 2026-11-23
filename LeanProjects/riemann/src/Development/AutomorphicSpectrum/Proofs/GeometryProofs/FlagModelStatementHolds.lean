import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlagModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelCommonRefinementStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSubQuotientSplitStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagModel

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem pull_map (L : Lat ξ E) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (φ : E →ₗ[Ω] E') :
    (L.map φ).pull ξ' f (AddMonoidHom.id E') = (L.pull ξ' f (AddMonoidHom.id E)).map φ := by
  funext p'
  simp only [Lat.pull, Lat.map, Submodule.map_span]
  congr 1
  ext e'
  constructor
  · rintro ⟨h, e, he, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 he
    exact ⟨u, ⟨h, u, hu, rfl⟩, rfl⟩
  · rintro ⟨u, ⟨h, v, hv, huv⟩, rfl⟩
    exact ⟨h, φ v, Submodule.mem_map.2 ⟨v, hv, rfl⟩, congrArg φ huv⟩

theorem pull_vb {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {f : X' ⟶ X} (hd : Dominates ξ' ξ f (RingHom.id Ω)) : (L.pull ξ' f (AddMonoidHom.id E)).IsVB g W := by
  intro p' _
  obtain ⟨h, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ _ _ hd p'
  obtain ⟨U, hU, b, hW, hb⟩ := hL ⟨f p'.1, h⟩ (Set.mem_univ _)
  refine ⟨f ⁻¹ᵁ U, hU, b, hW, fun q' _ hq' => ?_⟩
  obtain ⟨hq, hreg, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ _ _ hd q'
  obtain ⟨hli, hsp⟩ := hb ⟨f q'.1, hq⟩ (Set.mem_univ _) hq'
  refine ⟨hli, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro e' ⟨h', e, he, he'⟩
    have he2 : e ∈ Submodule.span (regAt ξ ⟨f q'.1, hq⟩) (Set.range b) := hsp ▸ he
    have hee : e' = e := he'
    rw [hee]
    clear he he' hee
    induction he2 using Submodule.span_induction with
    | mem u hu => exact Submodule.subset_span hu
    | zero => exact Submodule.zero_mem _
    | add u v _ _ hu hv => exact Submodule.add_mem _ hu hv
    | smul c u _ hu => exact Submodule.smul_mem _ (⟨c.1, hreg c.1 c.2⟩ : regAt ξ' q') hu
  · refine Submodule.span_mono ?_
    intro e he
    exact ⟨hq, e, hsp ▸ Submodule.subset_span he, rfl⟩

theorem coh_map {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) (φ : E →ₗ[Ω] E') :
    (L.map φ).IsCohOn Set.univ := by
  intro p hp
  obtain ⟨U, hU, b, -, hb⟩ := hL p hp
  refine ⟨U, hU, g, φ ∘ b, fun q hq hqU => ?_⟩
  simp only [Lat.map]
  rw [(hb q hq hqU).2, Submodule.map_span, Set.range_comp]
  rfl

theorem span_map {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) (φ : E →ₗ[Ω] E') (p : Cpt ξ) :
    Submodule.span Ω ((L.map φ) p : Set E') = W.map φ := by
  obtain ⟨U, hU, b, hW, hb⟩ := hL p (Set.mem_univ p)
  simp only [Lat.map]
  rw [(hb p (Set.mem_univ p) hU).2, Submodule.map_span, Submodule.span_span_of_tower, ← hW, Submodule.map_span]
  rfl

theorem flagStep_min {r : ℕ} (b₀ : Fin r → E) (n : ℕ) : flagStep Ω b₀ (min n r) = flagStep Ω b₀ n := by
  unfold flagStep
  congr 2
  ext k
  have := k.2
  simp only [Set.mem_setOf_eq]
  omega

theorem flagStep_le {r : ℕ} {b₀ : Fin r → E} {W : Submodule Ω E} (h : ∀ k, b₀ k ∈ W) (n : ℕ) :
    flagStep Ω b₀ n ≤ W := by
  unfold flagStep
  rw [Submodule.span_le]
  rintro _ ⟨k, -, rfl⟩
  exact h k

theorem flagModel : FlagModelStatement := by
  intro o _ _ Ω _ _ κ _ x M A _ κa _ w S _ E _ _ L g r W b₀ hw hL hb hbW
  obtain ⟨p₀⟩ : Nonempty (Cpt M.ξ) := ⟨⟨genPt M.ξ, specializes_rfl⟩⟩
  haveI hfin : ∀ σ, FiniteDimensional Ω (W σ) := fun σ => by
    obtain ⟨U, -, b, hW, -⟩ := hL σ p₀ (Set.mem_univ _)
    rw [← hW]
    exact FiniteDimensional.span_of_finite Ω (Set.finite_range b)
  obtain ⟨κ', hκ', y, M', f, hdom, hnorm, hchart, hvb, hat⟩ :=
    GlobalTheory.T.flag_model_common_refinement o Ω κ x M A κa w (Σ σ, Fin (r σ + 1))
      (fun q => E ⧸ flagStep Ω (b₀ q.1) q.2)
      (fun q => (L q.1).map (flagStep Ω (b₀ q.1) q.2).mkQ)
      (fun q => (W q.1).map (flagStep Ω (b₀ q.1) q.2).mkQ) hw
      (fun q => coh_map (hL q.1) _) (fun q p => span_map (hL q.1) _ p)
  have hpull : ∀ σ, ((L σ).pull M'.ξ f (AddMonoidHom.id E)).IsVBOn Set.univ (g σ) (W σ) :=
    fun σ => pull_vb (hL σ) hdom
  have hquot : ∀ σ (n : ℕ), ∃ s W', (((L σ).pull M'.ξ f (AddMonoidHom.id E)).map
      (flagStep Ω (b₀ σ) n).mkQ).IsVBOn Set.univ s W' := fun σ n => by
    rw [← flagStep_min]
    have h := hvb ⟨σ, ⟨min n (r σ), Nat.lt_succ_of_le (min_le_right _ _)⟩⟩
    rw [pull_map] at h
    exact ⟨_, _, h⟩
  refine ⟨κ', hκ', y, M', f, hdom, hnorm, hchart, fun σ => ?_, fun σ n p' => ?_, fun p hp hfr => ?_⟩
  · exact GlobalTheory.T.lattice_flag_vector_bundle _ _ _ _ _ _ _ _ _ _ (hb σ) (hbW σ) (hpull σ) (hquot σ)
  · obtain ⟨s, W', h⟩ := hquot σ n
    exact (GlobalTheory.T.lattice_sub_quotient_split _ _ _ _ _ _ _ _ _ _ _ (flagStep_le (hbW σ) n) (hpull σ) h).2 p' (Set.mem_univ _)
  · exact hat p hp fun q => hfr q.1 q.2

end GlobalTheory.CompanionTheory.Ar.FlagModel
