import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenExhaustionStabilizes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedUnipotentCompactExhaustion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellHeightLocalReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnipotentInCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.OpenSupp

theorem isLocallyConstant_ind {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ) :
    IsLocallyConstant (fun g => f.1.1 g) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hT := f.2
  refine Filter.mem_of_superset
    ((IsOpen.preimage (f := fun y => g⁻¹ * y) (continuous_const.mul continuous_id) hT).mem_nhds ?_) ?_
  · show _ = _
    simp
  · intro y hy
    have h1 := congrFun (congrArg Subtype.val hy) g
    have h2 : f.1.1 (g * (g⁻¹ * y)) = f.1.1 g := h1
    simpa using h2

theorem support_stable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ)
    (p : GL (Fin N) k) (hp : p ∈ parab k (stdBlocks d hd)) (g : GL (Fin N) k) (hg : f.1.1 g ≠ 0) :
    f.1.1 (p * g) ≠ 0 := by
  intro h0
  apply hg
  have := parInd_law (stdBlocks d hd) ρ f (⟨p, hp⟩⁻¹) (p * g)
  rw [h0, map_zero, smul_zero] at this
  simpa using this

theorem cell_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : GL (Fin N) k)
    (hg : g ∈ cell k d hd (wOpen d hd)) :
    ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ unipU k d hd, g = p * pm k (wOpen d hd) * u := by
  obtain ⟨p, hp, n, hn, rfl⟩ := hg
  obtain ⟨a, ha, u, hu, rfl⟩ := (GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad k h N d hd).1 n hn
  obtain ⟨m, hm⟩ : (MulAut.conj (pm k (wOpen d hd))).toMonoidHom a ∈ (leviEmb k (stdBlocks d hd)).range := ha.2
  have hc : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m := by
    rw [hm]; rfl
  refine ⟨p * leviEmb k (stdBlocks d hd) m, mul_mem hp (leviEmb_mem_parab k _ m), u, hu, ?_⟩
  rw [← hc]; group

theorem exists_open_of_le {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (U L L₀ : Subgroup G)
    (hL : L ≤ U) (h0 : L₀ ≤ L) (O₀ : Set G) (hO : IsOpen O₀) (hOU : O₀ ∩ (U : Set G) = L₀) :
    ∃ O : Set G, IsOpen O ∧ O ∩ (U : Set G) = L := by
  refine ⟨⋃ l ∈ (L : Set G), (fun x => l⁻¹ * x) ⁻¹' O₀, isOpen_biUnion fun l _ =>
    hO.preimage (continuous_const.mul continuous_id), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨⟨l, hl, hx⟩, hxU⟩
    have : l⁻¹ * x ∈ (L₀ : Set G) := by
      rw [← hOU]
      exact ⟨hx, mul_mem (inv_mem (hL hl)) hxU⟩
    have h2 := mul_mem hl (h0 this)
    simpa using h2
  · intro hx
    have h1 : (1 : G) ∈ (L₀ : Set G) := one_mem L₀
    rw [← hOU] at h1
    exact ⟨⟨x, hx, by simpa using h1.1⟩, hL hx⟩

end GlobalTheory.CompanionTheory.Rodier.OpenSupp

open GlobalTheory.CompanionTheory.Rodier.OpenSupp in

theorem GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ f ∈ openFns d hd ρ, ∃ L : Subgroup (GL (Fin N) k), L ≤ unipU k d hd ∧ IsCompact (L : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L) ∧ ∀ g, f.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
  intro k _ _ _ _ h N d hd W _ _ ρ hρ f hf
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : LocallyCompactSpace (GL (Fin N) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  set w := pm k (wOpen d hd) with hw
  set U := unipU k d hd with hU
  set P := parab k (stdBlocks d hd) with hP
  have hUB : U ≤ unipB k (Fin N) := inf_le_left
  have hUc : IsClosed (U : Set (GL (Fin N) k)) := (GlobalTheory.CompanionTheory.Rodier.unipU_open_cell k h N d hd).2.2
  obtain ⟨Lj, hmono, hcpt, hle, hexh⟩ := GlobalTheory.CompanionTheory.UnipExhaust.exists_monotone_compact_exhaustion k N U hUB hUc
  have hlc := isLocallyConstant_ind d hd ρ f
  let S : Set (GL (Fin N) k) := {g | f.1.1 g ≠ 0}
  have hSo : IsOpen S := hlc ({0}ᶜ)
  have hSc : IsClosed S := by
    rw [← isOpen_compl_iff]
    have : Sᶜ = (fun g => f.1.1 g) ⁻¹' {0} := by
      ext g; simp [S]
    rw [this]; exact hlc {0}
  have hcov : ∀ g ∈ S, ∃ p ∈ P, ∃ j, ∃ n ∈ Lj j, g = p * w * n := by
    intro g hg
    obtain ⟨p, hp, u, hu, rfl⟩ := cell_eq d hd g (hf g hg)
    obtain ⟨j, hj⟩ := hexh u hu
    exact ⟨p, hp, j, u, hj, rfl⟩
  have hSeq : S ∩ {g | ∃ p ∈ P, ∃ j, ∃ n ∈ Lj j, g = p * w * n} = S :=
    Set.inter_eq_left.2 hcov
  obtain ⟨j, hj⟩ := GlobalTheory.CompanionTheory.BaireCoset.baire_double_coset P (GlobalTheory.WhitHered.CellLoc.isClosed_parab _) (GlobalTheory.SplitWeil.KO k (Fin N) : Set (GL (Fin N) k))
    GlobalTheory.SplitFlip.isCompact_KO (fun g => by
      obtain ⟨p, c, hc, e⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (stdBlocks d hd) g
      exact ⟨p, p.2, c, hc, e⟩) Lj hmono hcpt w S hSo
    (fun p hp g hg => support_stable d hd ρ f p hp g hg) (by rw [hSeq]; exact hSc)
  obtain ⟨L₀, hL₀U, hL₀c, ⟨O₀, hO₀, hO₀U⟩, -⟩ :=
    GlobalTheory.T.exists_bump_section_on_compact_unipotent k (1 : AddChar k Circle) (by simpa using (continuous_one : Continuous (1 : k → Circle))) h N d hd ρ hρ 0
  obtain ⟨U₀, hU₀c, hU₀⟩ := GlobalTheory.UnipCptSub.exists_compact_subgroup_of_isCompact
    ((L₀ : Set (GL (Fin N) k)) ∪ (Lj j : Set (GL (Fin N) k))) (hL₀c.union (hcpt j)) (by
      rintro x (hx | hx)
      · exact hUB (hL₀U hx)
      · exact hUB (hle j hx))
  refine ⟨U₀ ⊓ U, inf_le_right, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact hU₀c.inter_right hUc
  · exact exists_open_of_le U (U₀ ⊓ U) L₀ inf_le_right
      (fun x hx => ⟨hU₀ (Or.inl hx), hL₀U hx⟩) O₀ hO₀ hO₀U
  · intro g hg
    obtain ⟨p, hp, n, hn, e⟩ := hj g hg (hcov g hg)
    exact ⟨p, hp, n, ⟨hU₀ (Or.inr hn), hle j hn⟩, e⟩
