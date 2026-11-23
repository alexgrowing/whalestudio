import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaCells
import GroundTheory.AutomorphicForms.InductionParabolic
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa Topology Set DoubleCoset

section Enumeration

variable {X : Type*} {k : ℕ} (C : Fin k → Set X)

def cellUnion (j : ℕ) : Set X := ⋃ l : Fin k, ⋃ (_ : (l : ℕ) < j), C l

theorem mem_cellUnion {j : ℕ} {x : X} : x ∈ cellUnion C j ↔ ∃ l : Fin k, (l : ℕ) < j ∧ x ∈ C l := by
  simp [cellUnion]

variable {C}

theorem cellUnion_zero : cellUnion C 0 = ∅ := by
  ext x
  simp [mem_cellUnion]

theorem cellUnion_mono {i j : ℕ} (h : i ≤ j) : cellUnion C i ⊆ cellUnion C j := fun x hx => by
  obtain ⟨l, hl, hx⟩ := (mem_cellUnion C).1 hx
  exact (mem_cellUnion C).2 ⟨l, lt_of_lt_of_le hl h, hx⟩

theorem cellUnion_succ (j : Fin k) : cellUnion C ((j : ℕ) + 1) = cellUnion C j ∪ C j := by
  ext x
  simp only [mem_cellUnion, mem_union]
  constructor
  · rintro ⟨l, hl, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | hl
    · exact Or.inl ⟨l, hl, hx⟩
    · exact Or.inr (Fin.ext hl ▸ hx)
  · rintro (⟨l, hl, hx⟩ | hx)
    · exact ⟨l, by omega, hx⟩
    · exact ⟨j, by omega, hx⟩

theorem cellUnion_of_cover (hcov : ∀ x, ∃ l, x ∈ C l) : cellUnion C k = univ := by
  ext x
  obtain ⟨l, hl⟩ := hcov x
  simp only [mem_univ, iff_true]
  exact (mem_cellUnion C).2 ⟨l, l.2, hl⟩

variable [TopologicalSpace X]
variable (hdisj : Pairwise fun i j => Disjoint (C i) (C j)) (hcov : ∀ x, ∃ l, x ∈ C l)
  (hcl : ∀ j, closure (C j) ⊆ ⋃ l : Fin k, ⋃ (_ : j ≤ l), C l)
include hdisj hcov hcl

theorem isOpen_cellUnion (j : ℕ) : IsOpen (cellUnion C j) := by
  have hc : (cellUnion C j)ᶜ = ⋃ l : Fin k, ⋃ (_ : j ≤ (l : ℕ)), closure (C l) := by
    ext x
    simp only [mem_compl_iff, mem_cellUnion, mem_iUnion, not_exists, not_and, exists_prop]
    constructor
    · intro h
      obtain ⟨l, hl⟩ := hcov x
      exact ⟨l, not_lt.1 fun h' => h l h' hl, subset_closure hl⟩
    · rintro ⟨l, hjl, hx⟩ l' hl' hx'
      obtain ⟨l'', hll'', hx''⟩ := mem_iUnion₂.1 (hcl l hx)
      have : l'' = l' := by
        by_contra hne
        exact Set.disjoint_left.1 (hdisj hne) hx'' hx'
      subst this
      have : (l : ℕ) ≤ l'' := hll''
      omega
  have hc' : (⋃ l : Fin k, ⋃ (_ : j ≤ (l : ℕ)), closure (C l)) =
      ⋃ l ∈ Finset.univ.filter (fun l : Fin k => j ≤ (l : ℕ)), closure (C l) := by
    ext x
    simp
  rw [← isClosed_compl_iff, hc, hc']
  exact isClosed_biUnion_finset fun l _ => isClosed_closure

omit hcov in

theorem closure_inter_cellUnion_succ (j : Fin k) :
    closure (C j) ∩ cellUnion C ((j : ℕ) + 1) = C j := by
  apply subset_antisymm
  · rintro x ⟨hx, hxu⟩
    obtain ⟨l, hl, hxl⟩ := (mem_cellUnion C).1 hxu
    obtain ⟨l', hjl', hx'⟩ := mem_iUnion₂.1 (hcl j hx)
    have : l' = l := by
      by_contra hne
      exact Set.disjoint_left.1 (hdisj hne) hx' hxl
    subst this
    have : j = l' := Fin.ext (by have : (j : ℕ) ≤ l' := hjl'; omega)
    subst this
    exact hx'
  · intro x hx
    refine ⟨subset_closure hx, ?_⟩
    rw [cellUnion_succ (C := C) j]
    exact Or.inr hx

omit [TopologicalSpace X] hcov hcl in
theorem disjoint_cellUnion (j : Fin k) : Disjoint (C j) (cellUnion C j) := by
  rw [Set.disjoint_left]
  intro x hx hxu
  obtain ⟨l, hl, hxl⟩ := (mem_cellUnion C).1 hxu
  have hne : l ≠ j := fun h => by rw [h] at hl; exact lt_irrefl _ hl
  exact Set.disjoint_left.1 (hdisj hne) hxl hx

end Enumeration

section Cells

variable {F : Type*} [Field F] {n : ℕ} (β γ : Fin n → ℕ)

theorem exists_cellEnumeration :
    ∃ (k : ℕ) (w : Fin k → Equiv.Perm (Fin n)),
      (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧
      Antitone fun j => cellHeight β γ (permGL F (w j)) := by
  classical
  let rk : Equiv.Perm (Fin n) → ℕ → ℕ → ℕ := fun w a b => cellRank β γ (permGL F w) a b
  let S : Finset (ℕ → ℕ → ℕ) := Finset.univ.image rk
  let e0 : Fin S.card ≃ S := S.equivFin.symm
  have hrep : ∀ r : S, ∃ w, rk w = r := fun r => by
    obtain ⟨w, -, hw⟩ := Finset.mem_image.1 r.2
    exact ⟨w, hw⟩
  choose rep hrep using hrep
  have hrep' : ∀ (r : S) (a b : ℕ), cellRank β γ (permGL F (rep r)) a b = (r : ℕ → ℕ → ℕ) a b :=
    fun r a b => congrFun (congrFun (hrep r) a) b
  let ht : Fin S.card → ℕ := fun i => cellHeight β γ (permGL F (rep (e0 i)))
  let s := Tuple.sort (fun i => OrderDual.toDual (ht i))
  have hs : Monotone ((fun i => OrderDual.toDual (ht i)) ∘ s) := Tuple.monotone_sort _
  refine ⟨S.card, fun j => rep (e0 (s j)), fun g => ?_, fun i j hij => ?_⟩
  · obtain ⟨w, hw⟩ := exists_permGL_mem_doubleCoset (β := β) (γ := γ) g
    have hmem : rk w ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ w)
    obtain ⟨j', hj⟩ := (s.trans e0).surjective ⟨rk w, hmem⟩
    have hj2 : e0 (s j') = ⟨rk w, hmem⟩ := hj
    have hg : g ∈ doubleCoset (permGL F (rep (e0 (s j')))) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ) := by
      apply mem_doubleCoset_of_cellRank_eq
      intro a b
      rw [hrep', cellRank_of_mem_doubleCoset hw, hj2]
    refine ⟨j', hg, fun j'' hj'' => ?_⟩
    apply s.injective
    apply e0.injective
    apply Subtype.ext
    funext a b
    have h1 := hrep' (e0 (s j'')) a b
    have h2 := hrep' (e0 (s j')) a b
    rw [← cellRank_of_mem_doubleCoset hj''] at h1
    rw [← cellRank_of_mem_doubleCoset hg] at h2
    rw [← h1, ← h2]
  · exact hs hij

end Cells

section CellsTopology

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T1Space F] {n : ℕ}
  {β γ : Fin n → ℕ}

theorem closure_doubleCoset_subset_of_antitone {k : ℕ} {w : Fin k → Equiv.Perm (Fin n)}
    (hcov : ∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
      (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ))
    (hanti : Antitone fun j => cellHeight β γ (permGL F (w j))) (j : Fin k) :
    closure (doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ)) ⊆
      ⋃ l : Fin k, ⋃ (_ : j ≤ l), doubleCoset (permGL F (w l))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) := by
  intro x hx
  obtain ⟨l, hl, -⟩ := hcov x
  refine mem_iUnion₂.2 ⟨l, ?_, hl⟩
  rcases closure_doubleCoset_subset _ hx with h | h
  · obtain ⟨j', -, hu⟩ := hcov x
    have h1 := hu j h
    have h2 := hu l hl
    rw [h1, h2]
  · by_contra hjl
    have := hanti (le_of_lt (not_le.1 hjl))
    rw [Set.mem_ofPred_eq, cellHeight_of_mem_doubleCoset hl] at h
    exact absurd this (not_le.2 h)

end CellsTopology

section Support

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β : Fin n → ℕ} (γ : Fin n → ℕ)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)

def supportedIn (Y : Set (GL (Fin n) F)) : Submodule ℂ (parabolicIndSpace F n β σ) where
  carrier := {f | ∀ g ∉ Y, (f : GL (Fin n) F → W) g = 0}
  add_mem' {f f'} hf hf' g hg := by
    simp [hf g hg, hf' g hg]
  zero_mem' g _ := rfl
  smul_mem' c f hf g hg := by
    simp [hf g hg]

variable {σ}

theorem mem_supportedIn {Y : Set (GL (Fin n) F)} {f : parabolicIndSpace F n β σ} :
    f ∈ supportedIn σ Y ↔ ∀ g ∉ Y, (f : GL (Fin n) F → W) g = 0 :=
  Iff.rfl

theorem supportedIn_mono {Y Y' : Set (GL (Fin n) F)} (h : Y ⊆ Y') :
    supportedIn σ Y ≤ supportedIn σ Y' :=
  fun f hf g hg => hf g fun hgY => hg (h hgY)

theorem supportedIn_empty : supportedIn σ (∅ : Set (GL (Fin n) F)) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  apply Subtype.ext
  funext g
  exact hf g (Set.notMem_empty g)

theorem supportedIn_univ : supportedIn σ (univ : Set (GL (Fin n) F)) = ⊤ := by
  rw [eq_top_iff]
  intro _ _ g hg
  exact absurd (mem_univ g) hg

theorem supportedIn_le_comap {Y : Set (GL (Fin n) F)}
    (hY : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y) {q : GL (Fin n) F}
    (hq : q ∈ blockUpper F n γ) :
    supportedIn σ Y ≤ (supportedIn σ Y).comap (parabolicInd F n β σ q) := by
  intro f hf g hg
  show ((parabolicInd F n β σ q f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) g = 0
  rw [coe_indRep_apply]
  apply hf
  intro hgq
  apply hg
  simpa using hY _ hgq _ ((blockUpper F n γ).inv_mem hq)

def jacquetFiltration (Y : Set (GL (Fin n) F)) :
    Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)) :=
  (supportedIn σ Y).map (Representation.Coinvariants.mk _)

theorem jacquetFiltration_mono {Y Y' : Set (GL (Fin n) F)} (h : Y ⊆ Y') :
    jacquetFiltration γ (σ := σ) Y ≤ jacquetFiltration γ Y' :=
  Submodule.map_mono (supportedIn_mono h)

theorem jacquetFiltration_empty : jacquetFiltration γ (σ := σ) ∅ = ⊥ := by
  rw [jacquetFiltration, supportedIn_empty, Submodule.map_bot]

theorem jacquetFiltration_univ : jacquetFiltration γ (σ := σ) univ = ⊤ := by
  rw [jacquetFiltration, supportedIn_univ, Submodule.map_top, LinearMap.range_eq_top]
  exact Representation.Coinvariants.mk_surjective _

theorem jacquetFiltration_le_comap {Y : Set (GL (Fin n) F)}
    (hY : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y) (m : levi F n γ) :
    jacquetFiltration γ (σ := σ) Y ≤
      (jacquetFiltration γ Y).comap (jacquetRep F n γ (parabolicInd F n β σ) m) := by
  rintro _ ⟨f, hf, rfl⟩
  rw [Submodule.mem_comap, jacquetRep_mk]
  exact Submodule.smul_mem _ _ ⟨_, supportedIn_le_comap γ hY (levi_le_blockUpper m.2) hf, rfl⟩

end Support

end Parabolic

end GroundTheory.Automorphic
