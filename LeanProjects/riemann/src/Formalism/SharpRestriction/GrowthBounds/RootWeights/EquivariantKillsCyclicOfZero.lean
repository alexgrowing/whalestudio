import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionRangeTrivial

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def weightHeightRootWeights (nu : Fin n → ℤ) : ℤ := ∑ c : Fin n, ((c : ℕ) : ℤ) * nu c

theorem weight_height_root_weights_add_root (nu : Fin n → ℤ) (a b : Fin n) :
    weightHeightRootWeights (nu + rootW a b) = weightHeightRootWeights nu + (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  unfold weightHeightRootWeights rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
  simp [Pi.single_apply]

theorem lowering_monomial_raises_height {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) {mu : Fin n → ℤ} {v : V}
    (hv : v ∈ weightSp E mu) {u : Module.End K V} (hu : u ∈ loweringWordMonoid E) :
    ∃ nu, u v ∈ weightSp E nu ∧ ((u v = v ∧ nu = mu) ∨ weightHeightRootWeights mu < weightHeightRootWeights nu) := by
  induction hu using Submonoid.closure_induction generalizing mu v with
  | mem x hx =>
    obtain ⟨a, b, hba, rfl⟩ := hx
    refine ⟨mu + rootW a b, hs a b mu v hv, Or.inr ?_⟩
    rw [weight_height_root_weights_add_root]
    have : (b : ℕ) < (a : ℕ) := hba
    omega
  | one => exact ⟨mu, by simpa using hv, Or.inl ⟨by simp, rfl⟩⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨nu2, h2, hc2⟩ := ihy hv
    obtain ⟨nu1, h1, hc1⟩ := ihx h2
    refine ⟨nu1, by simpa [Module.End.mul_apply] using h1, ?_⟩
    rcases hc2 with ⟨e2, rfl⟩ | lt2
    · rcases hc1 with ⟨e1, rfl⟩ | lt1
      · left; exact ⟨by rw [Module.End.mul_apply, e1, e2], rfl⟩
      · right; exact lt1
    · right
      rcases hc1 with ⟨_, rfl⟩ | lt1
      · exact lt2
      · exact lt2.trans lt1

theorem self_mem_cyclicSubmodule (E : GLOps n K V) (v : V) : v ∈ cyclicSubmodule E v := Submodule.subset_span ⟨1, (Umon E).one_mem, by simp⟩

theorem cyclic_highest_weightSpace_line [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (v : V)
    (hv : IsHWV E mu v) (x : V) (hx : x ∈ cyclicSubmodule E v) (hxw : x ∈ weightSp E mu) : ∃ c : K, x = c • v := by
  classical
  have hs : OperatorsShiftWeightsByRoots E := gl_rep_shifts_weights hE

  set Hh : Module.End K V := ∑ c : Fin n, (((c : ℕ) : ℤ) : K) • E c c with hHh
  have hH : ∀ nu (w : V), w ∈ weightSp E nu → Hh w = ((weightHeightRootWeights nu : ℤ) : K) • w := by
    intro nu w hw
    rw [mem_weightSpace_iff_diag_eigen] at hw
    rw [hHh, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hw, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp [weightHeightRootWeights]

  have hvY : v ∈ loweringWordSpan E v := Submodule.subset_span ⟨1, (loweringWordMonoid E).one_mem, by simp⟩
  have hcY : cyclicSubmodule E v ≤ loweringWordSpan E v := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    exact lowering_word_span_enveloping_stable hE hv hu v hvY
  set S : Submodule K V := Submodule.span K
    {y | ∃ nu, y ∈ weightSp E nu ∧ weightHeightRootWeights mu < weightHeightRootWeights nu} with hS
  have hYS : loweringWordSpan E v ≤ K ∙ v ⊔ S := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨nu, hnu, hc⟩ := lowering_monomial_raises_height hs hv.2.1 hu
    rcases hc with ⟨he, -⟩ | hlt
    · rw [he]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨nu, hnu, hlt⟩)
  obtain ⟨y, hy, s, hsS, hys⟩ := Submodule.mem_sup.1 (hYS (hcY hx))
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨c, ?_⟩
  have hsx : s = x - c • v := by rw [← hys]; abel
  have hs1 : s ∈ Hh.eigenspace ((weightHeightRootWeights mu : ℤ) : K) := by
    rw [Module.End.mem_eigenspace_iff, hsx, map_sub, map_smul, hH mu x hxw, hH mu v hv.2.1, smul_sub,
      smul_comm]
  have hs2 : s ∈ ⨆ (l : K) (_ : l ≠ ((weightHeightRootWeights mu : ℤ) : K)), Hh.eigenspace l := by
    refine (Submodule.span_le.2 ?_) hsS
    rintro w ⟨nu, hnu, hlt⟩
    have hne : ((weightHeightRootWeights nu : ℤ) : K) ≠ ((weightHeightRootWeights mu : ℤ) : K) := by
      exact_mod_cast hlt.ne'
    refine Submodule.mem_iSup_of_mem ((weightHeightRootWeights nu : ℤ) : K) (Submodule.mem_iSup_of_mem hne ?_)
    rw [Module.End.mem_eigenspace_iff]
    exact hH nu w hnu
  have h0 : s = 0 :=
    (Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep Hh ((weightHeightRootWeights mu : ℤ) : K))) s hs1 hs2
  rw [← hys, h0, add_zero]

theorem equivariant_kills_cyclic_of_zero (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T) (v : V)
    (h0 : T v = 0) : ∀ x ∈ cyclicSubmodule E v, T x = 0 := by
  intro x hx
  have hle : cyclicSubmodule E v ≤ LinearMap.ker T := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨u', -, hu'⟩ := equivariant_intertwines_monoid E E' T hT hu
    show T (u v) = 0
    rw [hu' v, h0, map_zero]
  exact hle hx

theorem envelopingMonoid_restrict (E : GLOps n K V) (L : Submodule K V) (hL : IsSubrepresentation E L) {u : Module.End K V} (hu : u ∈ Umon E) :
    ∃ uL ∈ Umon (restrictRepresentation E L hL), ∀ y : L, ((uL y : L) : V) = u (y : V) := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨restrictRepresentation E L hL a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => rfl⟩
  | one => exact ⟨1, (Umon _).one_mem, fun y => rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨ux, hux, hx⟩ := ihx
    obtain ⟨uy, huy, hy⟩ := ihy
    refine ⟨ux * uy, (Umon _).mul_mem hux huy, fun z => ?_⟩
    simp only [Module.End.mul_apply, hx, hy]

theorem cyclicSubmodule_restrict_eq_top (E : GLOps n K V) (v : V) (hL : IsSubrepresentation E (cyclicSubmodule E v)) :
    cyclicSubmodule (restrictRepresentation E _ hL) (⟨v, self_mem_cyclicSubmodule E v⟩ : cyclicSubmodule E v) = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro ⟨x, hx⟩ -
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨uL, huL, hL'⟩ := envelopingMonoid_restrict E _ hL hu
    have heq : (⟨u v, Submodule.subset_span ⟨u, hu, rfl⟩⟩ : cyclicSubmodule E v) = uL ⟨v, self_mem_cyclicSubmodule E v⟩ :=
      Subtype.ext (hL' ⟨v, self_mem_cyclicSubmodule E v⟩).symm
    rw [heq]
    exact Submodule.subset_span ⟨uL, huL, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add y z hy hz ihy ihz =>
    have := Submodule.add_mem _ ihy ihz
    exact this
  | smul c y hy ihy =>
    have := Submodule.smul_mem _ c ihy
    exact this

theorem highest_vector_restrict (E : GLOps n K V) (L : Submodule K V) (hL : IsSubrepresentation E L) (mu : Fin n → ℤ) (v : V) (hvL : v ∈ L)
    (hv : IsHWV E mu v) : IsHWV (restrictRepresentation E L hL) mu ⟨v, hvL⟩ := by
  obtain ⟨h0, hw, hl⟩ := hv
  refine ⟨fun h => h0 (congrArg Subtype.val h), ?_, fun a b hab => Subtype.ext (hl a b hab)⟩
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hw ⊢
  intro a
  apply Subtype.ext
  have := hw a
  simpa using this

end

end Formalism.MainNotions.G.GLWeightTheory
