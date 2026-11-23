import Development.EtaleCohomology.EtaleSheaves.ContPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.ContIndPf

section lists
variable {X : Scheme.{0}}

def lsup (l : List X.Opens) : X.Opens := l.foldr (· ⊔ ·) ⊥

lemma lsup_cons (a : X.Opens) (l : List X.Opens) : lsup (a :: l) = a ⊔ lsup l := rfl
lemma lsup_nil : lsup ([] : List X.Opens) = ⊥ := rfl

lemma le_lsup {l : List X.Opens} {B : X.Opens} (h : B ∈ l) : B ≤ lsup l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [lsup_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_sup_left
    · exact (ih h).trans le_sup_right

lemma lsup_le {l : List X.Opens} {W : X.Opens} (h : ∀ B ∈ l, B ≤ W) : lsup l ≤ W := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons]
    exact sup_le (h a (by simp)) (ih fun B hB => h B (by simp [hB]))

lemma isCompact_lsup (l : List X.Opens) (h : ∀ B ∈ l, IsCompact (B : Set X)) : IsCompact (lsup l : Set X) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons, TopologicalSpace.Opens.coe_sup]
    exact (h a (by simp)).union (ih fun B hB => h B (by simp [hB]))

lemma preimage_lsup {Y : Scheme.{0}} (f : Y ⟶ X) (l : List X.Opens) :
    f ⁻¹ᵁ lsup l = lsup (l.map (f ⁻¹ᵁ ·)) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons, List.map_cons, lsup_cons, ← ih]
    rfl

lemma lsup_inf (l : List X.Opens) (A : X.Opens) : lsup l ⊓ A = lsup (l.map (· ⊓ A)) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih => rw [List.map_cons, lsup_cons, lsup_cons, inf_sup_right, ih]

end lists

section opens
variable {X : Scheme.{0}}

lemma image_le_range {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (A : Y.Opens) : f ''ᵁ A ≤ f.opensRange := by
  rw [← Scheme.Hom.image_top_eq_opensRange]
  exact (f.image_le_image_iff _ _).2 le_top

lemma image_inf {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (A B : Y.Opens) :
    f ''ᵁ (A ⊓ B) = f ''ᵁ A ⊓ f ''ᵁ B := by
  apply le_antisymm
  · exact le_inf ((f.image_le_image_iff _ _).2 inf_le_left) ((f.image_le_image_iff _ _).2 inf_le_right)
  · have hC : f ''ᵁ A ⊓ f ''ᵁ B = f ''ᵁ (f ⁻¹ᵁ (f ''ᵁ A ⊓ f ''ᵁ B)) := by
      rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.2 (inf_le_left.trans (image_le_range f A))]
    rw [hC, f.image_le_image_iff]
    have : f ⁻¹ᵁ (f ''ᵁ A ⊓ f ''ᵁ B) = f ⁻¹ᵁ (f ''ᵁ A) ⊓ f ⁻¹ᵁ (f ''ᵁ B) := rfl
    rw [this, f.preimage_image_eq, f.preimage_image_eq]

lemma image_le (W : X.Opens) (A : W.toScheme.Opens) : W.ι ''ᵁ A ≤ W :=
  (image_le_range W.ι A).trans (Scheme.Opens.opensRange_ι W).le

lemma affine_preimage (W : X.Opens) {B : X.Opens} (h : B ≤ W) (hB : IsAffineOpen B) :
    IsAffineOpen (W.ι ⁻¹ᵁ B) := by
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι).mp
  rwa [W.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 h]

def Good (Y : Scheme.{0}) : Prop :=
  ∀ A B : Y.Opens, IsAffineOpen A → IsAffineOpen B → IsAffineOpen (A ⊓ B)

def Good2 (Y : Scheme.{0}) : Prop :=
  ∀ A B : Y.Opens, IsAffineOpen A → IsAffineOpen B → IsCompact ((A ⊓ B : Y.Opens) : Set Y)

lemma good_of (W : X.Opens)
    (h : ∀ C D : X.Opens, C ≤ W → D ≤ W → IsAffineOpen C → IsAffineOpen D → IsAffineOpen (C ⊓ D)) :
    Good W.toScheme := by
  intro A B hA hB
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι).mp
  rw [image_inf]
  exact h _ _ (image_le W A) (image_le W B) (hA.image_of_isOpenImmersion _) (hB.image_of_isOpenImmersion _)

lemma good_open (hX : Good X) (W : X.Opens) : Good W.toScheme :=
  good_of W (fun C D _ _ hC hD => hX C D hC hD)

lemma good_affine (A W : X.Opens) (hA : IsAffineOpen A) (hW : W ≤ A) : Good W.toScheme := by
  apply good_of W
  intro C D hC hD hC' hD'
  have : IsAffine A.toScheme := hA
  have h1 := (affine_preimage A (hC.trans hW) hC').inf (affine_preimage A (hD.trans hW) hD')
  have h2 := h1.image_of_isOpenImmersion A.ι
  rwa [image_inf, A.ι.image_preimage_eq_opensRange_inf, A.ι.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.2 (hC.trans hW), inf_eq_right.2 (hD.trans hW)] at h2

lemma hasCompactAffineIntersections_open_subscheme (hX : Good2 X) (W : X.Opens) : Good2 W.toScheme := by
  intro A B hA hB
  have h := hX _ _ (hA.image_of_isOpenImmersion W.ι) (hB.image_of_isOpenImmersion W.ι)
  rw [← image_inf] at h
  rw [W.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
  convert h using 1
  simp

lemma exists_cover (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ l : List X.Opens, (∀ B ∈ l, IsAffineOpen B ∧ B ≤ W) ∧ lsup l = W := by
  let ι := {B : X.Opens // IsAffineOpen B ∧ B ≤ W}
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun i : ι => ((i.1 : X.Opens) : Set X)) (fun i => i.1.isOpen)
    (by
      intro x hx
      have hb : ∀ {U : X.Opens} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)
      obtain ⟨B, hB, hxB, hBW⟩ := hb (U := W) hx
      exact Set.mem_iUnion.2 ⟨⟨B, hB, hBW⟩, hxB⟩)
  refine ⟨t.toList.map Subtype.val, ?_, ?_⟩
  · intro B hB
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hB
    exact i.2
  · apply le_antisymm
    · apply lsup_le
      intro B hB
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hB
      exact i.2.2
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact le_lsup (List.mem_map.2 ⟨i, Finset.mem_toList.2 hi, rfl⟩) hxi

end opens

section ind
variable (P : Scheme.{0} → Prop) (hA : ∀ (X : Scheme.{0}) [IsAffine X], P X)
  (hS : ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) → U ⊔ V = ⊤ →
    P U.toScheme → P V.toScheme → P (U ⊓ V).toScheme → P X)
include hA hS

omit hS in
lemma empty_case (Y : Scheme.{0}) (htop : lsup ([] : List Y.Opens) = ⊤) : P Y := by
  have : IsEmpty Y := by
    constructor
    intro x
    have hx : x ∈ (⊤ : Y.Opens) := trivial
    rw [← htop, lsup_nil] at hx
    exact hx
  exact hA Y

lemma stage1 (n : ℕ) : ∀ (Y : Scheme.{0}) (l : List Y.Opens), l.length = n → Good Y →
    (∀ B ∈ l, IsAffineOpen B) → lsup l = ⊤ → P Y := by
  induction n with
  | zero =>
    intro Y l hl _ _ htop
    rw [List.eq_nil_of_length_eq_zero hl] at htop
    exact empty_case P hA Y htop
  | succ n ih =>
    intro Y l hl hG hl' htop
    cases l with
    | nil => simp at hl
    | cons A l =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hAff : IsAffineOpen A := hl' A (by simp)
      have hlA : ∀ B ∈ l, IsAffineOpen B := fun B hB => hl' B (by simp [hB])
      have htop' : lsup l ⊔ A = ⊤ := by rw [sup_comm, ← lsup_cons]; exact htop
      apply hS Y (lsup l) A (isCompact_lsup l fun B hB => (hlA B hB).isCompact) hAff.isCompact htop'
      · apply ih (lsup l).toScheme (l.map ((lsup l).ι ⁻¹ᵁ ·)) (by simp [hl]) (good_open hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (le_lsup hC) (hlA C hC)
        · rw [← preimage_lsup, Scheme.Opens.ι_preimage_self]
      · have : IsAffine A.toScheme := hAff
        exact hA A.toScheme
      · apply ih (lsup l ⊓ A).toScheme ((l.map (· ⊓ A)).map ((lsup l ⊓ A).ι ⁻¹ᵁ ·)) (by simp [hl])
          (good_open hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC
          refine affine_preimage _ ?_ (hG D A (hlA D hD) hAff)
          rw [lsup_inf]
          exact le_lsup (List.mem_map.2 ⟨D, hD, rfl⟩)
        · rw [← preimage_lsup, ← lsup_inf, Scheme.Opens.ι_preimage_self]

lemma stage2 (n : ℕ) : ∀ (Y : Scheme.{0}) (l : List Y.Opens), l.length = n → Good2 Y →
    (∀ B ∈ l, IsAffineOpen B) → lsup l = ⊤ → P Y := by
  induction n with
  | zero =>
    intro Y l hl _ _ htop
    rw [List.eq_nil_of_length_eq_zero hl] at htop
    exact empty_case P hA Y htop
  | succ n ih =>
    intro Y l hl hG hl' htop
    cases l with
    | nil => simp at hl
    | cons A l =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hAff : IsAffineOpen A := hl' A (by simp)
      have hlA : ∀ B ∈ l, IsAffineOpen B := fun B hB => hl' B (by simp [hB])
      have htop' : lsup l ⊔ A = ⊤ := by rw [sup_comm, ← lsup_cons]; exact htop
      apply hS Y (lsup l) A (isCompact_lsup l fun B hB => (hlA B hB).isCompact) hAff.isCompact htop'
      · apply ih (lsup l).toScheme (l.map ((lsup l).ι ⁻¹ᵁ ·)) (by simp [hl]) (hasCompactAffineIntersections_open_subscheme hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (le_lsup hC) (hlA C hC)
        · rw [← preimage_lsup, Scheme.Opens.ι_preimage_self]
      · have : IsAffine A.toScheme := hAff
        exact hA A.toScheme
      · have hc : IsCompact ((lsup l ⊓ A : Y.Opens) : Set Y) := by
          rw [lsup_inf]
          apply isCompact_lsup
          intro B hB
          obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hB
          exact hG D A (hlA D hD) hAff
        obtain ⟨l2, hl2, hs2⟩ := exists_cover _ hc
        apply stage1 P hA hS l2.length (lsup l ⊓ A).toScheme (l2.map ((lsup l ⊓ A).ι ⁻¹ᵁ ·)) (by simp)
          (good_affine A _ hAff inf_le_right)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (hl2 C hC).2 (hl2 C hC).1
        · rw [← preimage_lsup, hs2, Scheme.Opens.ι_preimage_self]

end ind

theorem ContInd_of : LateralTheory.E.ContPf.ContInd := by
  intro P hA hS X _ _
  have hc : IsCompact ((⊤ : X.Opens) : Set X) := by simpa using isCompact_univ
  obtain ⟨l, hl, hs⟩ := exists_cover (⊤ : X.Opens) hc
  refine stage2 P hA hS l.length X l rfl ?_ (fun B hB => (hl B hB).1) hs
  intro A B hA' hB'
  rw [TopologicalSpace.Opens.coe_inf]
  exact QuasiSeparatedSpace.inter_isCompact _ _ A.isOpen hA'.isCompact B.isOpen hB'.isCompact

end LateralTheory.E.ContIndPf
