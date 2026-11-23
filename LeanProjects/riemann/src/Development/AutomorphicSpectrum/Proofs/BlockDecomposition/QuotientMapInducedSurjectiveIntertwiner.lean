import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

private theorem cIndSpace_apply_mem_mul {G W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] {H : Subgroup G}
    {σ : Representation ℂ H W} (f : GlobalTheory.PRep.cIndSpace H σ) (h : G) (hh : h ∈ H)
    (g : G) : f.1.1.1 (h * g) = σ ⟨h, hh⟩ (f.1.1.1 g) := by
  exact f.1.1.2 ⟨h, hh⟩ g

private theorem isHK_empty {G : Type} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H ∅ := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK
  exact ⟨fun _ _ _ => Iff.rfl, ⊤, by simp, fun _ _ _ => Iff.rfl⟩

private theorem isHK_union {G : Type} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {A B : Set G} (hA : GlobalTheory.CompanionTheory.LeibPhi.IsHK H A)
    (hB : GlobalTheory.CompanionTheory.LeibPhi.IsHK H B) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H (A ∪ B) := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at *
  obtain ⟨hA₁, KA, hKA, hA₂⟩ := hA
  obtain ⟨hB₁, KB, hKB, hB₂⟩ := hB
  refine ⟨fun h hh g => ?_, KA ⊓ KB, ?_, fun g x hx => ?_⟩
  · simp only [Set.mem_union, hA₁ h hh g, hB₁ h hh g]
  · rw [Subgroup.coe_inf]
    exact hKA.inter hKB
  · rw [Subgroup.mem_inf] at hx
    simp only [Set.mem_union, hA₂ g x hx.1, hB₂ g x hx.2]

private theorem isHK_diff {G : Type} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {A B : Set G} (hA : GlobalTheory.CompanionTheory.LeibPhi.IsHK H A)
    (hB : GlobalTheory.CompanionTheory.LeibPhi.IsHK H B) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H (A \ B) := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at *
  obtain ⟨hA₁, KA, hKA, hA₂⟩ := hA
  obtain ⟨hB₁, KB, hKB, hB₂⟩ := hB
  refine ⟨fun h hh g => ?_, KA ⊓ KB, ?_, fun g x hx => ?_⟩
  · simp only [Set.mem_diff, hA₁ h hh g, hB₁ h hh g]
  · rw [Subgroup.coe_inf]
    exact hKA.inter hKB
  · rw [Subgroup.mem_inf] at hx
    simp only [Set.mem_diff, hA₂ g x hx.1, hB₂ g x hx.2]

theorem exists_cInd_restrict_eq {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W') (hι : Continuous ι) (hσ : IsSmooth σ) (hsurj : Function.Surjective q)
    (hH : ∀ x, x ∈ H' ↔ ι x ∈ H)
    (hq : ∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w))
    (hemb : ∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ')
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (F : cIndSpace H' σ') : ∃ f : cIndSpace H σ, ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  classical
  obtain ⟨C, hC, hsupp⟩ : ∃ C : Set G', IsCompact C ∧
      ∀ g, F.1.1.1 g ≠ 0 → ∃ h ∈ H', ∃ c ∈ C, g = h * c := F.2
  have hloc : ∀ c : G', ∃ T : Set G, ∃ U ∈ 𝓝 c, GlobalTheory.CompanionTheory.LeibPhi.IsHK H T ∧
      (∀ y ∈ U, ι y ∈ T) ∧ ∃ e : GlobalTheory.PRep.cIndSpace H σ,
        ∀ x, ι x ∈ T → q (e.1.1.1 (ι x)) = F.1.1.1 x := by
    intro c
    obtain ⟨K', hK'o, hK'⟩ := GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H' σ' F
    obtain ⟨w, hw⟩ := hsurj (F.1.1.1 c)
    obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_value H σ hσ hbase (ι c) w
    obtain ⟨Ke, hKeo, hKe⟩ := GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H σ e
    have hS : {y : G' | c⁻¹ * y * c ∈ K' ∧ ι (c⁻¹ * y * c) ∈ Ke} ∈ 𝓝 (1 : G') := by
      have hcont : Continuous (fun y : G' => c⁻¹ * y * c) := by fun_prop
      have hopen : IsOpen {z : G' | z ∈ K' ∧ ι z ∈ Ke} := hK'o.inter (hKeo.preimage hι)
      exact (hopen.preimage hcont).mem_nhds (by simp [one_mem])
    obtain ⟨K, hK, hKemb⟩ := hemb _ hS
    have hconj : (fun μ : G => ι c * μ * (ι c)⁻¹) ⁻¹' K ∈ 𝓝 (1 : G) := by
      have hcont : Continuous (fun μ : G => ι c * μ * (ι c)⁻¹) := by fun_prop
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hK)
    obtain ⟨M, hMo, -, hMsub⟩ := hbase _ hconj
    refine ⟨{g | ∃ a ∈ H, ∃ x ∈ M, g = a * ι c * x}, {y | ι (c⁻¹ * y) ∈ M}, ?_,
      GlobalTheory.CompanionTheory.LeibPhi.isHK_doubleCoset H M hMo (ι c), ?_, e, ?_⟩
    · have hcont : Continuous (fun y : G' => ι (c⁻¹ * y)) := hι.comp (continuous_mul_left c⁻¹)
      exact (hMo.preimage hcont).mem_nhds (by simp [one_mem])
    · intro y hy
      exact ⟨1, one_mem _, ι (c⁻¹ * y), hy, by simp⟩
    · rintro x ⟨a, ha, μ, hμ, hx⟩
      have hκ : ι c * μ * (ι c)⁻¹ ∈ K := hMsub hμ
      obtain ⟨h', hh', κ', hκ', hxeq⟩ := hKemb (x * c⁻¹) a ha (ι c * μ * (ι c)⁻¹) hκ
        (by rw [map_mul, hx, map_inv]; group)
      have hx' : x = h' * (c * (c⁻¹ * κ' * c)) := by
        have h0 : x = x * c⁻¹ * c := by group
        rw [h0, hxeq]
        group
      have hι' : ι h' ∈ H := (hH h').1 hh'
      have hFx : F.1.1.1 x = σ' ⟨h', hh'⟩ (q w) := by
        rw [hx', cIndSpace_apply_mem_mul F h' hh', hK' c _ hκ'.1, hw]
      rw [hFx, hx', map_mul, map_mul, cIndSpace_apply_mem_mul e _ hι',
        hKe _ _ hκ'.2, he]
      exact hq ⟨h', hh'⟩ hι' w
  choose T U hU hT hUT e he using hloc
  obtain ⟨t, -, hCt⟩ := hC.elim_nhds_subcover U (fun c _ => hU c)
  have hglue : ∀ s : Finset G', ∃ V : Set G, GlobalTheory.CompanionTheory.LeibPhi.IsHK H V ∧
      (∀ c ∈ s, T c ⊆ V) ∧ ∃ f : GlobalTheory.PRep.cIndSpace H σ,
        (∀ g ∉ V, f.1.1.1 g = 0) ∧ ∀ x, ι x ∈ V → q (f.1.1.1 (ι x)) = F.1.1.1 x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨∅, isHK_empty H, by simp, 0, fun g _ => ?_, fun x hx => ?_⟩
      · rfl
      · simp at hx
    | @insert c s hcs ih =>
      obtain ⟨V, hV, hsV, f, hf0, hf⟩ := ih
      obtain ⟨f', hf'in, hf'out⟩ := GlobalTheory.CompanionTheory.LeibPhi.exists_indicator H σ
        (isHK_diff (hT c) hV) (e c)
      have hadd : ∀ g, (f + f').1.1.1 g = f.1.1.1 g + f'.1.1.1 g := fun _ => rfl
      refine ⟨V ∪ T c, isHK_union hV (hT c), ?_, f + f', ?_, ?_⟩
      · intro d hd
        rcases Finset.mem_insert.1 hd with rfl | hd
        · exact Set.subset_union_right
        · exact (hsV d hd).trans Set.subset_union_left
      · intro g hg
        rw [Set.mem_union, not_or] at hg
        rw [hadd, hf0 g hg.1, hf'out g (fun h => hg.2 h.1), add_zero]
      · intro x hx
        by_cases hxV : ι x ∈ V
        · rw [hadd, hf'out _ (fun h => h.2 hxV), add_zero]
          exact hf x hxV
        · rcases hx with hx | hx
          · exact absurd hx hxV
          · rw [hadd, hf0 _ hxV, hf'in _ ⟨hx, hxV⟩, zero_add]
            exact he c x hx
  obtain ⟨V, hV, htV, f, hf0, hf⟩ := hglue t
  refine ⟨f, fun x => ?_⟩
  by_cases hx : ι x ∈ V
  · exact (hf x hx).symm
  · rw [hf0 _ hx, map_zero]
    by_contra hne
    obtain ⟨h', hh', c', hc', rfl⟩ := hsupp x hne
    obtain ⟨d, hd, hc'U⟩ := Set.mem_iUnion₂.1 (hCt hc')
    have hmem : ι c' ∈ V := htV d hd (hUT d c' hc'U)
    unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at hV
    apply hx
    rw [map_mul]
    exact (hV.1 _ ((hH h').1 hh') _).2 hmem

end GlobalTheory.CompanionTheory.LeibPhi
