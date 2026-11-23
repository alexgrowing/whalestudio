import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Kernel

section Abstract

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem cInd_ext {H : Subgroup G} {σ : Representation ℂ H W} {a b : cIndSpace H σ}
    (h : ∀ g, a.1.1.1 g = b.1.1.1 g) : a = b :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem cInd_left {H : Subgroup G} {σ : Representation ℂ H W} (a : cIndSpace H σ) {h : G}
    (hh : h ∈ H) (g : G) : a.1.1.1 (h * g) = σ ⟨h, hh⟩ (a.1.1.1 g) :=
  a.1.1.2 ⟨h, hh⟩ g

theorem indicator_mem (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ)
    (σ : Representation ℂ H W) {E : Set G} (hE : IsHK H E) (a : cIndSpace H σ)
    (ha : a ∈ twKer (cInd H σ) U θ) :
    ∀ a' : cIndSpace H σ, (∀ g ∈ E, a'.1.1.1 g = a.1.1.1 g) → (∀ g, g ∉ E → a'.1.1.1 g = 0) →
      a' ∈ twKer (cInd H σ) U θ := by
  have hR : ∀ (g : G) (u : U), g * (u : G) ∈ E ↔ g ∈ E := by
    intro g u
    have e : g * (u : G) = (g * (u : G) * g⁻¹) * g := by group
    rw [e]
    exact hE.1 _ (hUH (hU.conj_mem _ u.2 g)) g
  unfold twKer at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, v, rfl⟩ := hx
    intro a' h1 h2
    obtain ⟨v', hv1, hv2⟩ := exists_indicator H σ hE v
    have e : a' = cInd H σ (u : G) v' - (θ u : ℂ) • v' := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · rw [h1 g hg]
        show v.1.1.1 (g * u) - (θ u : ℂ) • v.1.1.1 g = v'.1.1.1 (g * u) - (θ u : ℂ) • v'.1.1.1 g
        rw [hv1 g hg, hv1 _ ((hR g u).2 hg)]
      · rw [h2 g hg]
        show (0 : W) = v'.1.1.1 (g * u) - (θ u : ℂ) • v'.1.1.1 g
        rw [hv2 g hg, hv2 _ (fun c => hg ((hR g u).1 c))]
        simp
    rw [e]
    exact Submodule.subset_span ⟨u, v', rfl⟩
  | zero =>
    intro a' h1 h2
    have e : a' = 0 := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · exact h1 g hg
      · exact h2 g hg
    rw [e]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    intro a' h1 h2
    obtain ⟨x', hx1, hx2⟩ := exists_indicator H σ hE x
    obtain ⟨y', hy1, hy2⟩ := exists_indicator H σ hE y
    have e : a' = x' + y' := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · rw [h1 g hg]
        show x.1.1.1 g + y.1.1.1 g = x'.1.1.1 g + y'.1.1.1 g
        rw [hx1 g hg, hy1 g hg]
      · rw [h2 g hg]
        show (0 : W) = x'.1.1.1 g + y'.1.1.1 g
        rw [hx2 g hg, hy2 g hg, add_zero]
    rw [e]
    exact Submodule.add_mem _ (hx x' hx1 hx2) (hy y' hy1 hy2)
  | smul c x _ hx =>
    intro a' h1 h2
    obtain ⟨x', hx1, hx2⟩ := exists_indicator H σ hE x
    have e : a' = c • x' := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · rw [h1 g hg]
        show c • x.1.1.1 g = c • x'.1.1.1 g
        rw [hx1 g hg]
      · rw [h2 g hg]
        show (0 : W) = c • x'.1.1.1 g
        rw [hx2 g hg, smul_zero]
    rw [e]
    exact Submodule.smul_mem _ c (hx x' hx1 hx2)

theorem exists_local (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ)
    (σ : Representation ℂ H W) (f f' : cIndSpace H σ) (hf' : f' ∈ twKer (cInd H σ) U θ) (g₀ : G)
    (he : f'.1.1.1 g₀ = f.1.1.1 g₀) :
    ∃ E : Set G, g₀ ∈ E ∧ IsHK H E ∧ ∃ b ∈ twKer (cInd H σ) U θ,
      (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0) := by
  obtain ⟨K, hK, hKi⟩ := cInd_right_inv H σ (f - f')
  have hE := isHK_doubleCoset H K hK g₀
  refine ⟨{g | ∃ a ∈ H, ∃ x ∈ K, g = a * g₀ * x}, ⟨1, one_mem H, 1, one_mem K, by simp⟩, hE, ?_⟩
  obtain ⟨b, hb1, hb2⟩ := exists_indicator H σ hE f'
  refine ⟨b, indicator_mem H U hUH hU θ σ hE f' hf' b hb1 hb2, ?_, hb2⟩
  rintro g ⟨a, ha, x, hx, rfl⟩
  rw [hb1 _ ⟨a, ha, x, hx, rfl⟩]
  have h0 : (f - f').1.1.1 g₀ = 0 := by
    show f.1.1.1 g₀ - f'.1.1.1 g₀ = 0
    rw [he, sub_self]
  have h1 : (f - f').1.1.1 (a * g₀ * x) = 0 := by
    rw [hKi _ x hx, cInd_left (f - f') ha, h0, map_zero]
  have h2 : f.1.1.1 (a * g₀ * x) - f'.1.1.1 (a * g₀ * x) = 0 := h1
  exact (sub_eq_zero.1 h2).symm

theorem mem_of_local (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ)
    (σ : Representation ℂ H W) (f : cIndSpace H σ)
    (hloc : ∀ g₀ : G, ∃ E : Set G, g₀ ∈ E ∧ IsHK H E ∧ ∃ b ∈ twKer (cInd H σ) U θ,
      (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0)) :
    f ∈ twKer (cInd H σ) U θ := by
  obtain ⟨C, hC, hf⟩ := f.2
  have key : ∃ E : Set G, C ⊆ E ∧ IsHK H E ∧ ∃ b ∈ twKer (cInd H σ) U θ,
      (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0) := by
    refine hC.induction_on (p := fun S => ∃ E : Set G, S ⊆ E ∧ IsHK H E ∧
      ∃ b ∈ twKer (cInd H σ) U θ,
        (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0)) ?_ ?_ ?_ ?_
    · refine ⟨∅, subset_rfl, ⟨by simp, ⊤, isOpen_univ, by simp⟩, 0, Submodule.zero_mem _, by simp,
        fun g _ => rfl⟩
    · rintro S T hST ⟨E, hTE, r⟩
      exact ⟨E, hST.trans hTE, r⟩
    · rintro S T ⟨E, hSE, hE, b, hb, hb1, hb2⟩ ⟨E', hTE, hE', b', hb', hb1', hb2'⟩
      obtain ⟨c, hc1, hc2⟩ := exists_indicator H σ hE.compl b'
      refine ⟨E ∪ E', Set.union_subset_union hSE hTE, hE.union hE', b + c,
        Submodule.add_mem _ hb (indicator_mem H U hUH hU θ σ hE.compl b' hb' c hc1 hc2), ?_, ?_⟩
      · intro g hg
        show b.1.1.1 g + c.1.1.1 g = f.1.1.1 g
        by_cases h : g ∈ E
        · rw [hb1 g h, hc2 g (fun c => c h), add_zero]
        · rw [hb2 g h, hc1 g h, zero_add]
          exact hb1' g (hg.resolve_left h)
      · intro g hg
        show b.1.1.1 g + c.1.1.1 g = 0
        have h : g ∉ E := fun c => hg (Or.inl c)
        have h' : g ∉ E' := fun c => hg (Or.inr c)
        rw [hb2 g h, hc1 g h, hb2' g h', add_zero]
    · intro x _
      obtain ⟨E, hx, hE, r⟩ := hloc x
      exact ⟨E, mem_nhdsWithin_of_mem_nhds (hE.isOpen.mem_nhds hx), E, subset_rfl, hE, r⟩
  obtain ⟨E, hCE, hE, b, hb, hb1, hb2⟩ := key
  have e : f = b := by
    apply cInd_ext
    intro g
    by_cases hg : g ∈ E
    · exact (hb1 g hg).symm
    · rw [hb2 g hg]
      by_contra h0
      obtain ⟨h, hh, c, hc, rfl⟩ := hf g h0
      exact hg ((hE.1 h hh c).2 (hCE hc))
  rw [e]
  exact hb

end Abstract

theorem mem_twKer_of_restrict_zero {G G' W W' : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group G']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ) (ι : G' →* G)
    (hst : ∀ (m : G') (n : U), ∃ h : ι m * (n : G) * (ι m)⁻¹ ∈ U, θ ⟨_, h⟩ = θ n)
    (σ : Representation ℂ H W) (q : W →ₗ[ℂ] W') (hσ : IsSmooth σ)
    (hq : ∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v})
    (hdich : ∀ g : G, (∃ h ∈ H, ∃ x : G', g = h * ι x) ∨
      ∃ u : U, ∃ hx : g * (u : G) * g⁻¹ ∈ H, (∀ w, σ ⟨_, hx⟩ w = w) ∧ θ u ≠ 1)
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (f : cIndSpace H σ) (hf : ∀ x, q (f.1.1.1 (ι x)) = 0) : f ∈ twKer (cInd H σ) U θ := by
  refine mem_of_local H U hUH hU θ σ f fun g₀ => ?_
  suffices hp : ∃ f' ∈ twKer (cInd H σ) U θ, f'.1.1.1 g₀ = f.1.1.1 g₀ by
    obtain ⟨f', hf', he⟩ := hp
    exact exists_local H U hUH hU θ σ f f' hf' g₀ he
  rcases hdich g₀ with ⟨h, hh, x, rfl⟩ | ⟨u, hx, hfix, hθ⟩
  · have hval : ∀ y ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v},
        ∃ f' ∈ twKer (cInd H σ) U θ, f'.1.1.1 (ι x) = y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, w, rfl⟩ := hy
        obtain ⟨hm, hθ⟩ := hst x⁻¹ v
        obtain ⟨e, he⟩ := exists_cInd_value H σ hσ hbase (ι x) w
        refine ⟨cInd H σ _ e - (θ ⟨_, hm⟩ : ℂ) • e, Submodule.subset_span ⟨⟨_, hm⟩, e, rfl⟩, ?_⟩
        have e1 : ι x * (ι x⁻¹ * (v : G) * (ι x⁻¹)⁻¹) = (v : G) * ι x := by
          simp only [map_inv]
          group
        show e.1.1.1 (ι x * (ι x⁻¹ * (v : G) * (ι x⁻¹)⁻¹)) - (θ ⟨_, hm⟩ : ℂ) • e.1.1.1 (ι x) = _
        rw [e1, cInd_left e (hUH v.2), he, hθ]
      | zero => exact ⟨0, Submodule.zero_mem _, rfl⟩
      | add a b _ _ ha hb =>
        obtain ⟨a', ha', ea⟩ := ha
        obtain ⟨b', hb', eb⟩ := hb
        refine ⟨a' + b', Submodule.add_mem _ ha' hb', ?_⟩
        show a'.1.1.1 (ι x) + b'.1.1.1 (ι x) = _
        rw [ea, eb]
      | smul c a _ ha =>
        obtain ⟨a', ha', ea⟩ := ha
        refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
        show c • a'.1.1.1 (ι x) = _
        rw [ea]
    obtain ⟨f', hf', he⟩ := hval _ ((hq _).1 (hf x))
    exact ⟨f', hf', by rw [cInd_left f' hh, cInd_left f hh, he]⟩
  · have hne : (1 : ℂ) - (θ u : ℂ) ≠ 0 := by
      intro h0
      apply hθ
      apply Units.ext
      simpa using (sub_eq_zero.1 h0).symm
    obtain ⟨e, he⟩ := exists_cInd_value H σ hσ hbase g₀ (((1 : ℂ) - (θ u : ℂ))⁻¹ • f.1.1.1 g₀)
    refine ⟨cInd H σ (u : G) e - (θ u : ℂ) • e, Submodule.subset_span ⟨u, e, rfl⟩, ?_⟩
    have e1 : g₀ * (u : G) = (g₀ * (u : G) * g₀⁻¹) * g₀ := by group
    show e.1.1.1 (g₀ * u) - (θ u : ℂ) • e.1.1.1 g₀ = _
    rw [e1, cInd_left e hx, hfix, he]
    have e2 : ∀ y : W, y - (θ u : ℂ) • y = ((1 : ℂ) - (θ u : ℂ)) • y := fun y => by
      rw [sub_smul, one_smul]
    rw [e2, smul_smul, mul_inv_cancel₀ hne, one_smul]

end GlobalTheory.CompanionTheory.LeibPhi.Kernel

end
