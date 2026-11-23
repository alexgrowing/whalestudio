import Mathlib
import GroundTheory.AutomorphicForms.WhittakerLSpace
import GroundTheory.AutomorphicForms.SmoothRep
import GroundTheory.AutomorphicForms.LocallyProfinite

namespace GroundTheory.Automorphic

namespace Whittaker

open Set Topology MulAction
open scoped Pointwise

section Translation

variable {X : Type*} {H : Type*} [Group H] [MulAction H X]

def transl (h : H) (f : X → ℂ) : X → ℂ := fun x => f (h⁻¹ • x)

@[simp]
theorem transl_apply (h : H) (f : X → ℂ) (x : X) : transl h f x = f (h⁻¹ • x) := rfl

theorem transl_mul (h k : H) (f : X → ℂ) : transl (h * k) f = transl h (transl k f) := by
  funext x
  simp [transl, mul_inv_rev, mul_smul]

theorem transl_one (f : X → ℂ) : transl (1 : H) f = f := by
  funext x
  simp [transl]

theorem transl_add (h : H) (f g : X → ℂ) : transl h (f + g) = transl h f + transl h g := rfl

theorem transl_sub (h : H) (f g : X → ℂ) : transl h (f - g) = transl h f - transl h g := rfl

theorem transl_smul (h : H) (c : ℂ) (f : X → ℂ) : transl h (c • f) = c • transl h f := rfl

theorem transl_sum {ι : Type*} (h : H) (s : Finset ι) (f : ι → X → ℂ) :
    transl h (∑ i ∈ s, f i) = ∑ i ∈ s, transl h (f i) := by
  funext x
  simp [transl, Finset.sum_apply]

theorem transl_indicator (h : H) (A : Set X) : transl h (A.indicator 1) = (h • A).indicator 1 := by
  funext x
  simp only [transl_apply]
  by_cases hx : h⁻¹ • x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 hx)]
    rfl
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h' => hx (Set.mem_smul_set_iff_inv_smul_mem.1 h'))]

end Translation

section Relations

variable {X : Type*} [TopologicalSpace X] {H : Type*} [Group H] [TopologicalSpace H]
  [MulAction H X] [ContinuousSMul H X]

theorem transl_mem_supportedIn {U : Set X} (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (h : H)
    {f : X → ℂ} (hf : f ∈ supportedIn U) : transl h f ∈ supportedIn U := by
  refine ⟨⟨hf.1.1.comp_continuous (continuous_const_smul h⁻¹), ?_⟩, ?_⟩
  · exact hf.1.2.comp_homeomorph (Homeomorph.smul h⁻¹)
  · intro x hx
    have := hUinv h _ (hf.2 hx)
    simpa using this

def relSpan (χ : H →* ℂ) (U : Set X) : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ {g | ∃ h : H, ∃ f ∈ supportedIn U, g = transl h f - χ h • f}

omit [TopologicalSpace H] [ContinuousSMul H X] in
theorem sub_mem_relSpan (χ : H →* ℂ) {U : Set X} (h : H) {f : X → ℂ} (hf : f ∈ supportedIn U) :
    transl h f - χ h • f ∈ relSpan χ U :=
  Submodule.subset_span ⟨h, f, hf, rfl⟩

theorem relSpan_le_supportedIn (χ : H →* ℂ) {U : Set X}
    (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) : relSpan χ U ≤ supportedIn U := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, f, hf, rfl⟩
  exact (supportedIn U).sub_mem (transl_mem_supportedIn hUinv h hf)
    ((supportedIn U).smul_mem _ hf)

end Relations

section Orbit

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]

def orbitPiece (L : Subgroup H) (y : X) : Set X := (fun l : H => l • y) '' (L : Set H)

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [ContinuousSMul H X] in
theorem mem_orbitPiece {L : Subgroup H} {y x : X} : x ∈ orbitPiece L y ↔ ∃ l ∈ L, l • y = x :=
  Iff.rfl

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [ContinuousSMul H X] in
theorem self_mem_orbitPiece (L : Subgroup H) (y : X) : y ∈ orbitPiece L y :=
  ⟨1, L.one_mem, one_smul _ _⟩

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [ContinuousSMul H X] in
theorem orbitPiece_subset_orbit {L : Subgroup H} {x₀ y : X} (hy : y ∈ orbit H x₀) :
    orbitPiece L y ⊆ orbit H x₀ := by
  rintro _ ⟨l, -, rfl⟩
  exact mem_orbit_of_mem_orbit l hy

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [ContinuousSMul H X] in

theorem orbitPiece_eq_of_mem {L : Subgroup H} {y z : X} (hz : z ∈ orbitPiece L y) :
    orbitPiece L z = orbitPiece L y := by
  obtain ⟨l, hl, rfl⟩ := hz
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m * l, L.mul_mem hm hl, mul_smul m l y⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m * l⁻¹, L.mul_mem hm (L.inv_mem hl), ?_⟩
    simp [mul_smul]

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [ContinuousSMul H X] in

theorem orbitPiece_eq_or_disjoint (L : Subgroup H) (y z : X) :
    orbitPiece L y = orbitPiece L z ∨ Disjoint (orbitPiece L y) (orbitPiece L z) := by
  by_cases h : Disjoint (orbitPiece L y) (orbitPiece L z)
  · exact Or.inr h
  · obtain ⟨x, hxy, hxz⟩ := Set.not_disjoint_iff.1 h
    exact Or.inl ((orbitPiece_eq_of_mem hxy).symm.trans (orbitPiece_eq_of_mem hxz))

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [ContinuousSMul H X] in

theorem smul_orbitPiece {A : Subgroup H} {j : H} (hj : ∀ a ∈ A, j * a * j⁻¹ ∈ A)
    (hj' : ∀ a ∈ A, j⁻¹ * a * j ∈ A) (y : X) : j • orbitPiece A y = orbitPiece A (j • y) := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨j * a * j⁻¹, hj a ha, ?_⟩
    simp [mul_smul]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(j⁻¹ * a * j) • y, ⟨j⁻¹ * a * j, hj' a ha, rfl⟩, ?_⟩
    simp [mul_smul]

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [ContinuousSMul H X] in

theorem orbitPiece_smul (L : Subgroup H) (h : H) (y : X) :
    orbitPiece L (h • y) = h • orbitPiece (L.map (MulAut.conj h⁻¹).toMonoidHom) y := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨(h⁻¹ * l * h) • y, ⟨h⁻¹ * l * h, ⟨l, hl, by simp⟩, rfl⟩, ?_⟩
    simp [mul_smul]
  · rintro ⟨_, ⟨_, ⟨l, hl, rfl⟩, rfl⟩, rfl⟩
    refine ⟨l, hl, ?_⟩
    simp [mul_smul]

omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H] in
theorem isCompact_orbitPiece {L : Subgroup H} (hL : IsCompact (L : Set H)) (y : X) :
    IsCompact (orbitPiece L y) :=
  hL.image (continuous_id.smul continuous_const)

omit [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [T2Space X]
  [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [ContinuousSMul H X] in

theorem isCompact_isOpen_map_conj {L : Subgroup H} (hLc : IsCompact (L : Set H))
    (hLo : IsOpen (L : Set H)) (h : H) :
    IsCompact ((L.map (MulAut.conj h).toMonoidHom : Subgroup H) : Set H) ∧
      IsOpen ((L.map (MulAut.conj h).toMonoidHom : Subgroup H) : Set H) := by
  have e : ((L.map (MulAut.conj h).toMonoidHom : Subgroup H) : Set H) =
      ((Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹)) '' (L : Set H) := by
    ext x
    simp [Subgroup.coe_map, MulAut.conj_apply]
  rw [e]
  exact ⟨hLc.image (Homeomorph.continuous _), (Homeomorph.isOpenMap _) _ hLo⟩

omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H] in
theorem continuousSMul_orbit (x₀ : X) : ContinuousSMul H (orbit H x₀) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  have : ((Subtype.val : orbit H x₀ → X) ∘ fun p : H × orbit H x₀ => p.1 • p.2) =
      fun p : H × orbit H x₀ => p.1 • (p.2 : X) := by
    funext p
    rfl
  rw [this]
  exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

omit [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [TotallyDisconnectedSpace X] in

theorem isOpen_orbitPiece {x₀ : X} (hO : IsLocallyClosed (orbit H x₀)) {L : Subgroup H}
    (hLo : IsOpen (L : Set H)) {y : X} (hy : y ∈ orbit H x₀) :
    IsOpen ((Subtype.val : orbit H x₀ → X) ⁻¹' orbitPiece L y) := by
  have : LocallyCompactSpace (orbit H x₀) := hO.locallyCompactSpace
  have := continuousSMul_orbit (H := H) x₀
  have hmap := isOpenMap_smul_of_sigmaCompact (G := H) (X := orbit H x₀) ⟨y, hy⟩ _ hLo
  convert hmap using 1
  ext ⟨x, hx⟩
  simp only [mem_preimage, mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, Subtype.ext rfl⟩
  · rintro ⟨l, hl, e⟩
    exact ⟨l, hl, congrArg Subtype.val e⟩

omit [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] in

theorem exists_lift_orbit_piece {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) {L : Subgroup H} (hLc : IsCompact (L : Set H))
    (hLo : IsOpen (L : Set H)) {y : X} (hy : y ∈ orbit H x₀) :
    ∃ f ∈ supportedIn U, ∀ x ∈ orbit H x₀, f x = (orbitPiece L y).indicator 1 x := by
  have hOl : IsLocallyClosed (orbit H x₀) := ⟨U, C, hU, hC, hO.symm⟩
  exact exists_lift_indicator hU (hO ▸ inter_subset_left) (orbitPiece_subset_orbit hy)
    (isCompact_orbitPiece hLc y) (isOpen_orbitPiece hOl hLo hy)

section Base

variable {U C : Set X} {x₀ : X}

omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [ContinuousSMul H X] [T2Space X] [TopologicalSpace H] in

theorem sub_mem_of_eqOn_orbit (hO : U ∩ C = orbit H x₀) {f g : X → ℂ} (hf : f ∈ supportedIn U)
    (hg : g ∈ supportedIn U) (heq : ∀ x ∈ orbit H x₀, f x = g x) :
    f - g ∈ supportedIn U ⊓ vanishingOn C := by
  refine ⟨(supportedIn U).sub_mem hf hg, fun x hxC => ?_⟩
  by_cases hxU : x ∈ U
  · have hx : x ∈ orbit H x₀ := hO ▸ ⟨hxU, hxC⟩
    simp [heq x hx]
  · have h1 : f x = 0 := Function.notMem_support.1 fun h => hxU (hf.2 h)
    have h2 : g x = 0 := Function.notMem_support.1 fun h => hxU (hg.2 h)
    simp [h1, h2]

omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [ContinuousSMul H X] [T2Space X] [TopologicalSpace H] in

theorem mem_of_eqOn_orbit (hO : U ∩ C = orbit H x₀) {W : Submodule ℂ (X → ℂ)}
    (hWU : W ≤ supportedIn U) {f g : X → ℂ} (hg : g ∈ supportedIn U)
    (hf : f ∈ W ⊔ (supportedIn U ⊓ vanishingOn C)) (heq : ∀ x ∈ orbit H x₀, g x = f x) :
    g ∈ W ⊔ (supportedIn U ⊓ vanishingOn C) := by
  have hfU : f ∈ supportedIn U := (sup_le hWU inf_le_left) hf
  have := (W ⊔ (supportedIn U ⊓ vanishingOn C)).add_mem hf
    (le_sup_right (a := W) (sub_mem_of_eqOn_orbit hO hg hfU heq))
  simpa using this

omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [T2Space X]
  [TopologicalSpace H] [ContinuousSMul H X] in

theorem transl_mem_of_mem (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hWU : W ≤ supportedIn U) (hW : relSpan χ U ≤ W) (h : H)
    {f : X → ℂ} (hf : f ∈ W ⊔ (supportedIn U ⊓ vanishingOn C)) :
    transl h f ∈ W ⊔ (supportedIn U ⊓ vanishingOn C) := by
  have hfU : f ∈ supportedIn U := (sup_le hWU inf_le_left) hf
  have e : transl h f = (transl h f - χ h • f) + χ h • f := by abel
  rw [e]
  exact add_mem (le_sup_left (b := supportedIn U ⊓ vanishingOn C)
    (hW (sub_mem_relSpan χ h hfU))) (Submodule.smul_mem _ _ hf)

def GoodPiece (U C : Set X) (x₀ : X) (W : Submodule ℂ (X → ℂ)) (A : Set X) : Prop :=
  ∀ g ∈ supportedIn U, (∀ x ∈ orbit H x₀, g x = A.indicator 1 x) →
    g ∈ W ⊔ (supportedIn U ⊓ vanishingOn C)

omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [T2Space X] in
theorem GoodPiece.smul (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hWU : W ≤ supportedIn U) (hW : relSpan χ U ≤ W) {A : Set X}
    (hA : GoodPiece (H := H) U C x₀ W A) (h : H) : GoodPiece (H := H) U C x₀ W (h • A) := by
  intro g hg hgA
  have h1 : transl h⁻¹ g ∈ W ⊔ (supportedIn U ⊓ vanishingOn C) := by
    refine hA _ (transl_mem_supportedIn hUinv _ hg) fun x hx => ?_
    rw [transl_apply, inv_inv, hgA _ (mem_orbit_of_mem_orbit h hx)]
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem (Set.smul_mem_smul_set hxA)]
      rfl
    · rw [Set.indicator_of_notMem hxA,
        Set.indicator_of_notMem (fun h' => hxA ((Set.smul_mem_smul_set_iff).1 h'))]
  have := transl_mem_of_mem χ hWU hW h h1
  rwa [← transl_mul, mul_inv_cancel, transl_one] at this

omit [TotallyDisconnectedSpace X] [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] in

theorem exists_finset_orbitPiece (hOl : IsLocallyClosed (orbit H x₀)) {J A : Subgroup H}
    (hJc : IsCompact (J : Set H)) (hAo : IsOpen (A : Set H)) (hAJ : A ≤ J)
    (hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) {y : X} (hy : y ∈ orbit H x₀) :
    ∃ 𝒮 : Finset (Set X), 𝒮.Nonempty ∧ (∀ S ∈ 𝒮, ∃ j ∈ J, S = j • orbitPiece A y) ∧
      ∀ x, (orbitPiece J y).indicator (1 : X → ℂ) x = ∑ S ∈ 𝒮, S.indicator 1 x := by
  classical
  have hsm : ∀ j ∈ J, j • orbitPiece A y = orbitPiece A (j • y) := fun j hj =>
    smul_orbitPiece (hAn j hj) (fun a ha => by simpa using hAn j⁻¹ (J.inv_mem hj) a ha) y
  have hsub : ∀ j ∈ J, orbitPiece A (j • y) ⊆ orbitPiece J y := by
    rintro j hj _ ⟨a, ha, rfl⟩
    exact ⟨a * j, J.mul_mem (hAJ ha) hj, mul_smul a j y⟩

  let K' : Set (orbit H x₀) := (fun j : H => j • (⟨y, hy⟩ : orbit H x₀)) '' (J : Set H)
  have := continuousSMul_orbit (H := H) x₀
  have hK' : IsCompact K' := hJc.image (continuous_id.smul continuous_const)
  obtain ⟨t, htJ, htfin, hcov⟩ := hK'.elim_finite_subcover_image (b := (J : Set H))
    (c := fun j => (Subtype.val : orbit H x₀ → X) ⁻¹' orbitPiece A (j • y))
    (fun j _ => isOpen_orbitPiece hOl hAo (mem_orbit_of_mem_orbit j hy))
    (by
      rintro _ ⟨j, hj, rfl⟩
      exact mem_iUnion₂.2 ⟨j, hj, self_mem_orbitPiece A _⟩)
  have hcov' : ∀ x ∈ orbitPiece J y, ∃ j ∈ t, x ∈ orbitPiece A (j • y) := by
    rintro _ ⟨j, hj, rfl⟩
    have hx : (j • (⟨y, hy⟩ : orbit H x₀)) ∈ K' := ⟨j, hj, rfl⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hcov hx)
    exact ⟨i, hi, hxi⟩
  refine ⟨htfin.toFinset.image fun j => orbitPiece A (j • y), ?_, ?_, ?_⟩
  · obtain ⟨j, hj, -⟩ := hcov' y (self_mem_orbitPiece J y)
    exact ⟨_, Finset.mem_image_of_mem _ (htfin.mem_toFinset.2 hj)⟩
  · intro S hS
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hS
    have hjJ := htJ (htfin.mem_toFinset.1 hj)
    exact ⟨j, hjJ, (hsm j hjJ).symm⟩
  · intro x
    by_cases hx : x ∈ orbitPiece J y
    · obtain ⟨j, hj, hxj⟩ := hcov' x hx
      rw [Set.indicator_of_mem hx, Finset.sum_eq_single (orbitPiece A (j • y))]
      · rw [Set.indicator_of_mem hxj]
      · intro S hS hSne
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hS
        refine Set.indicator_of_notMem (fun hxi => hSne ?_) _
        rcases orbitPiece_eq_or_disjoint A (i • y) (j • y) with e | e
        · exact e
        · exact absurd hxj (Set.disjoint_left.1 e hxi)
      · intro h
        exact absurd (Finset.mem_image_of_mem _ (htfin.mem_toFinset.2 hj)) h
    · rw [Set.indicator_of_notMem hx]
      refine (Finset.sum_eq_zero fun S hS => ?_).symm
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hS
      exact Set.indicator_of_notMem (fun hxi => hx (hsub i (htJ (htfin.mem_toFinset.1 hi)) hxi)) _

omit [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] in

theorem GoodPiece.up {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hWU : W ≤ supportedIn U) (hW : relSpan χ U ≤ W)
    {J A : Subgroup H} (hJc : IsCompact (J : Set H)) (hAo : IsOpen (A : Set H)) (hAJ : A ≤ J)
    (hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) {y : X} (hy : y ∈ orbit H x₀)
    (hA : GoodPiece (H := H) U C x₀ W (orbitPiece A y)) :
    GoodPiece (H := H) U C x₀ W (orbitPiece J y) := by
  classical
  have hOl : IsLocallyClosed (orbit H x₀) := ⟨U, C, hU, hC, hO.symm⟩
  obtain ⟨𝒮, -, h𝒮, hsum⟩ := exists_finset_orbitPiece hOl hJc hAo hAJ hAn hy
  have hAc : IsCompact (A : Set H) := hJc.of_isClosed_subset (A.isClosed_of_isOpen hAo) hAJ
  obtain ⟨gA, hgA, hgAO⟩ := exists_lift_orbit_piece hU hC hO hAc hAo hy
  have hgAT := hA gA hgA hgAO
  choose! j hjJ hjS using h𝒮
  intro g hg hgJ
  refine mem_of_eqOn_orbit hO hWU hg (f := ∑ S ∈ 𝒮, transl (j S) gA)
    (Submodule.sum_mem _ fun S _ => transl_mem_of_mem χ hWU hW _ hgAT) fun x hx => ?_
  rw [hgJ x hx, hsum x, Finset.sum_apply]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [transl_apply, hgAO _ (mem_orbit_of_mem_orbit _ hx)]
  conv_lhs => rw [hjS S hS]
  by_cases hxS : (j S)⁻¹ • x ∈ orbitPiece A y
  · simp only [Set.indicator_of_mem hxS,
      Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 hxS), Pi.one_apply]
  · rw [Set.indicator_of_notMem hxS,
      Set.indicator_of_notMem (fun h' => hxS (Set.mem_smul_set_iff_inv_smul_mem.1 h'))]

omit [TotallyDisconnectedSpace X] [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] in

theorem GoodPiece.down {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hW : relSpan χ U ≤ W)
    {J A : Subgroup H} (hJc : IsCompact (J : Set H)) (hχJ : ∀ j ∈ J, χ j = 1)
    (hAo : IsOpen (A : Set H)) (hAJ : A ≤ J)
    (hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) {y : X} (hy : y ∈ orbit H x₀)
    (hJ : GoodPiece (H := H) U C x₀ W (orbitPiece J y)) :
    GoodPiece (H := H) U C x₀ W (orbitPiece A y) := by
  classical
  have hOl : IsLocallyClosed (orbit H x₀) := ⟨U, C, hU, hC, hO.symm⟩
  obtain ⟨𝒮, hne, h𝒮, hsum⟩ := exists_finset_orbitPiece hOl hJc hAo hAJ hAn hy
  choose! j hjJ hjS using h𝒮
  intro gA hgA hgAO
  set T := W ⊔ (supportedIn U ⊓ vanishingOn C)
  have hG : ∑ S ∈ 𝒮, transl (j S) gA ∈ T := by
    refine hJ _ (Submodule.sum_mem _ fun S _ => transl_mem_supportedIn hUinv _ hgA)
      fun x hx => ?_
    rw [hsum x, Finset.sum_apply]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [transl_apply, hgAO _ (mem_orbit_of_mem_orbit _ hx)]
    conv_rhs => rw [hjS S hS]
    by_cases hxS : (j S)⁻¹ • x ∈ orbitPiece A y
    · simp only [Set.indicator_of_mem hxS,
        Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 hxS), Pi.one_apply]
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem (fun h' => hxS (Set.mem_smul_set_iff_inv_smul_mem.1 h'))]
  have hR : ∑ S ∈ 𝒮, (transl (j S) gA - χ (j S) • gA) ∈ T :=
    le_sup_left (b := supportedIn U ⊓ vanishingOn C)
      (hW (Submodule.sum_mem _ fun S _ => sub_mem_relSpan χ _ hgA))
  have hcard : (𝒮.card : ℂ) • gA ∈ T := by
    have e : (𝒮.card : ℂ) • gA =
        ∑ S ∈ 𝒮, transl (j S) gA - ∑ S ∈ 𝒮, (transl (j S) gA - χ (j S) • gA) := by
      rw [Finset.sum_sub_distrib, sub_sub_cancel, Finset.sum_congr rfl fun S hS => by
        rw [hχJ _ (hjJ S hS), one_smul], Finset.sum_const, Nat.cast_smul_eq_nsmul]
    rw [e]
    exact T.sub_mem hG hR
  have hc : (𝒮.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hne)
  have := T.smul_mem (𝒮.card : ℂ)⁻¹ hcard
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

omit [TotallyDisconnectedSpace X] [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace H] in

theorem exists_forall_smul_eq {U C : Set X} (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) {f : X → ℂ} (hf : f ∈ supportedIn U) :
    ∃ L : Subgroup H, IsCompact (L : Set H) ∧ IsOpen (L : Set H) ∧
      ∀ l ∈ L, ∀ x ∈ orbit H x₀, f (l • x) = f x := by
  have hOC : orbit H x₀ ⊆ C := hO ▸ inter_subset_right
  let K := C ∩ Function.support f
  have hK : IsCompact K := (isCompact_support hf.1).inter_left hC
  let Wset : Set (H × X) := {p | f (p.1 • p.2) = f p.2}
  have hWo : IsOpen Wset := by
    have hF : IsLocallyConstant fun p : H × X => (f (p.1 • p.2), f p.2) :=
      (hf.1.1.comp_continuous continuous_smul).prodMk (hf.1.1.comp_continuous continuous_snd)
    exact hF {q | q.1 = q.2}
  have hsub : ({1} : Set H) ×ˢ K ⊆ Wset := by
    rintro ⟨h, x⟩ ⟨hh, -⟩
    simp only [mem_singleton_iff] at hh
    simp [Wset, hh]
  obtain ⟨u, v, hu, -, h1u, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hWo hsub
  obtain ⟨L, hLc, hLu⟩ := exists_openSubgroup_isCompact_subset (hu.mem_nhds (h1u rfl))
  refine ⟨L, hLc, L.isOpen, fun l hl x hx => ?_⟩
  by_cases hxK : x ∈ K
  · exact huv (show (l, x) ∈ u ×ˢ v from ⟨hLu hl, hKv hxK⟩)
  · have hfx : f x = 0 := by
      by_contra h
      exact hxK ⟨hOC hx, h⟩
    rw [hfx]
    by_contra h
    have hlx : l • x ∈ K := ⟨hOC (mem_orbit_of_mem_orbit l hx), h⟩
    have := huv (show (l⁻¹, l • x) ∈ u ×ˢ v from ⟨hLu (L.inv_mem hl), hKv hlx⟩)
    simp only [Wset, Set.mem_ofPred_eq, inv_smul_smul] at this
    exact h (by rw [← this, hfx])

theorem supportedIn_le_of_base {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hWU : W ≤ supportedIn U) (hW : relSpan χ U ≤ W)
    (L₀ : Subgroup H) (hL₀c : IsCompact (L₀ : Set H)) (hL₀o : IsOpen (L₀ : Set H))
    (hχL₀ : ∀ l ∈ L₀, χ l = 1) (f₀ : X → ℂ)
    (hf₀O : ∀ x ∈ orbit H x₀, f₀ x = (orbitPiece L₀ x₀).indicator 1 x)
    (hbase : f₀ ∈ W ⊔ (supportedIn U ⊓ vanishingOn C)) :
    supportedIn U ≤ W ⊔ (supportedIn U ⊓ vanishingOn C) := by
  classical
  have hx₀ : x₀ ∈ orbit H x₀ := mem_orbit_self x₀
  set T := W ⊔ (supportedIn U ⊓ vanishingOn C)
  have hOU : orbit H x₀ ⊆ U := hO ▸ inter_subset_left
  have hOl : IsLocallyClosed (orbit H x₀) := ⟨U, C, hU, hC, hO.symm⟩

  have hgood0 : GoodPiece (H := H) U C x₀ W (orbitPiece L₀ x₀) := fun g hg hgO =>
    mem_of_eqOn_orbit hO hWU hg hbase fun x hx => by rw [hgO x hx, hf₀O x hx]

  have hA : ∀ M : Subgroup H, IsOpen (M : Set H) → M ≤ L₀ →
      (∀ k ∈ L₀, ∀ m ∈ M, k * m * k⁻¹ ∈ M) → GoodPiece (H := H) U C x₀ W (orbitPiece M x₀) :=
    fun M hMo hML hMn => GoodPiece.down hU hC hO hUinv χ hW hL₀c hχL₀ hMo hML hMn hx₀ hgood0

  have hB : ∀ M : Subgroup H, IsOpen (M : Set H) → M ≤ L₀ →
      GoodPiece (H := H) U C x₀ W (orbitPiece M x₀) := by
    intro M hMo hML
    obtain ⟨N₀, hN₀o, hN₀L, hN₀M, hN₀n, -⟩ :=
      exists_normal_subgroup hL₀c hL₀o (hMo.mem_nhds M.one_mem)
    have hMc : IsCompact (M : Set H) := hL₀c.of_isClosed_subset (M.isClosed_of_isOpen hMo) hML
    exact GoodPiece.up hU hC hO χ hWU hW hMc hN₀o (fun x hx => hN₀M hx)
      (fun j hj a ha => hN₀n j (hML hj) a ha) hx₀ (hA N₀ hN₀o hN₀L hN₀n)

  have hC' : ∀ J : Subgroup H, IsCompact (J : Set H) → IsOpen (J : Set H) →
      GoodPiece (H := H) U C x₀ W (orbitPiece J x₀) := by
    intro J hJc hJo
    obtain ⟨A, hAo, hAJ, hAJL, hAn, -⟩ :=
      exists_normal_subgroup hJc hJo (U := (J : Set H) ∩ L₀)
        (Filter.inter_mem (hJo.mem_nhds J.one_mem) (hL₀o.mem_nhds L₀.one_mem))
    exact GoodPiece.up hU hC hO χ hWU hW hJc hAo hAJ hAn hx₀
      (hB A hAo fun x hx => (hAJL hx).2)

  have hall : ∀ J : Subgroup H, IsCompact (J : Set H) → IsOpen (J : Set H) →
      ∀ y ∈ orbit H x₀, GoodPiece (H := H) U C x₀ W (orbitPiece J y) := by
    intro J hJc hJo y hy
    obtain ⟨h, rfl⟩ := mem_orbit_iff.1 hy
    rw [orbitPiece_smul]
    have hc := isCompact_isOpen_map_conj hJc hJo h⁻¹
    exact GoodPiece.smul hUinv χ hWU hW (hC' _ hc.1 hc.2) h

  intro f hf
  obtain ⟨L, hLc, hLo, hLf⟩ := exists_forall_smul_eq hC hO hf
  have key : ∀ t : Finset X, (↑t : Set X) ⊆ orbit H x₀ → ∀ g ∈ supportedIn U,
      (∀ l ∈ L, ∀ x ∈ orbit H x₀, g (l • x) = g x) →
      (∀ x ∈ orbit H x₀, g x ≠ 0 → x ∈ ⋃ y ∈ t, orbitPiece L y) → g ∈ T := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ g hg _ hg0
      refine le_sup_right (a := W) ⟨hg, fun x hxC => ?_⟩
      by_contra h
      by_cases hxU : x ∈ U
      · have := hg0 x (hO ▸ ⟨hxU, hxC⟩) h
        simp at this
      · exact hxU (hg.2 h)
    | insert y t hyt ih =>
      intro htO g hg hgL hg0
      have hy : y ∈ orbit H x₀ := htO (by simp)
      obtain ⟨gy, hgy, hgyO⟩ := exists_lift_orbit_piece hU hC hO hLc hLo hy
      have hgyT : gy ∈ T := hall L hLc hLo y hy gy hgy hgyO
      have e : g = (g - g y • gy) + g y • gy := by abel
      rw [e]
      refine T.add_mem (ih (fun x hx => htO (by simp [hx])) _
        ((supportedIn U).sub_mem hg ((supportedIn U).smul_mem _ hgy)) ?_ ?_) (T.smul_mem _ hgyT)
      · intro l hl x hx
        have hlx := mem_orbit_of_mem_orbit l hx
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hgL l hl x hx, hgyO _ hlx, hgyO _ hx]
        by_cases hxy : x ∈ orbitPiece L y
        · have hlxy : l • x ∈ orbitPiece L y := by
            obtain ⟨m, hm, rfl⟩ := hxy
            exact ⟨l * m, L.mul_mem hl hm, mul_smul l m y⟩
          simp only [Set.indicator_of_mem hxy, Set.indicator_of_mem hlxy, Pi.one_apply]
        · have hlxy : l • x ∉ orbitPiece L y := by
            rintro ⟨m, hm, hmy⟩
            refine hxy ⟨l⁻¹ * m, L.mul_mem (L.inv_mem hl) hm, ?_⟩
            show (l⁻¹ * m) • y = x
            rw [mul_smul, show m • y = l • x from hmy, inv_smul_smul]
          simp only [Set.indicator_of_notMem hxy, Set.indicator_of_notMem hlxy]
      · intro x hx hx0
        have hxy : x ∉ orbitPiece L y := by
          intro hxy
          apply hx0
          obtain ⟨m, hm, rfl⟩ := hxy
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [hgL m hm y hy, hgyO _ (mem_orbit_of_mem_orbit m hy),
            Set.indicator_of_mem (show m • y ∈ orbitPiece L y from ⟨m, hm, rfl⟩)]
          simp
        have hgx : g x ≠ 0 := by
          intro h
          apply hx0
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [h, hgyO _ hx, Set.indicator_of_notMem hxy]
          simp
        have := hg0 x hx hgx
        rw [Finset.set_biUnion_insert] at this
        exact this.resolve_left hxy

  have hK : IsCompact (C ∩ Function.support f) := (isCompact_support hf.1).inter_left hC
  have hopen : ∀ y ∈ C ∩ Function.support f, ∃ V : Set X, IsOpen V ∧
      V ∩ orbit H x₀ = orbitPiece L y := by
    intro y hy
    have hyO : y ∈ orbit H x₀ := hO ▸ ⟨hf.2 hy.2, hy.1⟩
    obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 (isOpen_orbitPiece hOl hLo hyO)
    refine ⟨V, hVo, ?_⟩
    ext x
    constructor
    · rintro ⟨hxV, hxO⟩
      have : (⟨x, hxO⟩ : orbit H x₀) ∈ (Subtype.val : orbit H x₀ → X) ⁻¹' V := hxV
      rw [hV] at this
      exact this
    · intro hx
      have hxO := orbitPiece_subset_orbit hyO hx
      have : (⟨x, hxO⟩ : orbit H x₀) ∈ (Subtype.val : orbit H x₀ → X) ⁻¹' orbitPiece L y := hx
      rw [← hV] at this
      exact ⟨this, hxO⟩
  choose! V hVo hVO using hopen
  obtain ⟨t, htK, htfin, hcov⟩ := hK.elim_finite_subcover_image hVo
    (fun y hy => mem_iUnion₂.2 ⟨y, hy, by
      have : y ∈ V y ∩ orbit H x₀ := by
        rw [hVO y hy]
        exact self_mem_orbitPiece L y
      exact this.1⟩)
  refine key htfin.toFinset (fun x hx => ?_) f hf hLf fun x hx hfx => ?_
  · have := htK (htfin.mem_toFinset.1 hx)
    exact hO ▸ ⟨hf.2 this.2, this.1⟩
  · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov ⟨(hO ▸ hx : x ∈ U ∩ C).2, hfx⟩)
    refine mem_iUnion₂.2 ⟨y, htfin.mem_toFinset.2 hy, ?_⟩
    rw [← hVO y (htK hy)]
    exact ⟨hxy, hx⟩

theorem supportedIn_le_of_stabilizer {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    (hχ : ∃ L : Subgroup H, IsOpen (L : Set H) ∧ ∀ l ∈ L, χ l = 1)
    {S₀ : Subgroup H} (hS₀ : IsCompact (S₀ : Set H)) {s : H} (hs : s ∈ S₀) (hsx : s • x₀ = x₀)
    (hχs : χ s ≠ 1) :
    supportedIn U ≤ relSpan χ U ⊔ (supportedIn U ⊓ vanishingOn C) := by
  obtain ⟨L, hLo, hχL⟩ := hχ
  obtain ⟨L₀, hL₀c, hL₀L, hL₀n⟩ := exists_compactOpenSubgroup_normalized hS₀ (hLo.mem_nhds L.one_mem)
  have hx₀ : x₀ ∈ orbit H x₀ := mem_orbit_self x₀
  have hWU := relSpan_le_supportedIn χ hUinv
  obtain ⟨f₀, hf₀, hf₀O⟩ := exists_lift_orbit_piece hU hC hO hL₀c L₀.isOpen hx₀
  set T := relSpan χ U ⊔ (supportedIn U ⊓ vanishingOn C)

  have hspiece : s • orbitPiece (L₀ : Subgroup H) x₀ = orbitPiece (L₀ : Subgroup H) x₀ := by
    rw [smul_orbitPiece (fun a ha => hL₀n s hs a ha)
      (fun a ha => by simpa using hL₀n s⁻¹ (S₀.inv_mem hs) a ha), hsx]
  have h1 : transl s f₀ - f₀ ∈ T := by
    refine le_sup_right (a := relSpan χ U) (sub_mem_of_eqOn_orbit hO
      (transl_mem_supportedIn hUinv s hf₀) hf₀ fun x hx => ?_)
    rw [transl_apply, hf₀O _ (mem_orbit_of_mem_orbit _ hx), hf₀O x hx]
    conv_rhs => rw [← hspiece]
    by_cases hxS : s⁻¹ • x ∈ orbitPiece (L₀ : Subgroup H) x₀
    · simp only [Set.indicator_of_mem hxS,
        Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 hxS), Pi.one_apply]
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem (fun h' => hxS (Set.mem_smul_set_iff_inv_smul_mem.1 h'))]
  have h2 : transl s f₀ - χ s • f₀ ∈ T :=
    le_sup_left (b := supportedIn U ⊓ vanishingOn C) (sub_mem_relSpan χ s hf₀)
  have h3 : (χ s - 1) • f₀ ∈ T := by
    have e : (χ s - 1) • f₀ = (transl s f₀ - f₀) - (transl s f₀ - χ s • f₀) := by
      rw [sub_smul, one_smul]
      abel
    rw [e]
    exact T.sub_mem h1 h2
  have hbase : f₀ ∈ T := by
    have := T.smul_mem (χ s - 1)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hχs), one_smul] at this
  exact supportedIn_le_of_base hU hC hO hUinv χ hWU le_rfl (L₀ : Subgroup H) hL₀c L₀.isOpen
    (fun l hl => hχL l (hL₀L hl)) f₀ hf₀O hbase

end Base

end Orbit

end Whittaker

end GroundTheory.Automorphic
