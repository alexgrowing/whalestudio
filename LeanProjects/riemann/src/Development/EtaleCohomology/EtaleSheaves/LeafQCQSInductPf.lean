import Development.EtaleCohomology.EtaleSheaves.LeafObjFPPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafQCQSInductPf

def Cov (X : Scheme.{0}) (L : List X.Opens) : Prop :=
  (∀ u ∈ L, IsAffineOpen u) ∧ ∀ x : X, ∃ u ∈ L, x ∈ u

lemma sep_of {X Y : Scheme.{0}} (g : Y ⟶ X) [IsOpenImmersion g] [X.IsSeparated] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from g]; infer_instance⟩

lemma fp_res {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) (hf : FP f) (W : X.Opens)
    (hW : IsCompact (W : Set X)) : FP (W.ι ≫ f) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨inferInstance, ?_, inferInstance⟩
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW
  exact quasiCompact_of_compactSpace _

lemma cov_pull {X : Scheme.{0}} (W : X.Opens) (L : List X.Opens) (hA : ∀ u ∈ L, IsAffineOpen u)
    (hle : ∀ u ∈ L, u ≤ W) (hc : ∀ x ∈ W, ∃ u ∈ L, x ∈ u) :
    Cov W.toScheme (L.map (W.ι ⁻¹ᵁ ·)) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact (hA u hu).preimage_of_isOpenImmersion W.ι (by simpa using hle u hu)
  · intro x
    obtain ⟨u, hu, hx⟩ := hc (W.ι x) (by
      have := Set.mem_range_self (f := W.ι) x
      rwa [Scheme.Opens.range_ι] at this)
    exact ⟨_, List.mem_map.mpr ⟨u, hu, rfl⟩, by simpa using hx⟩

lemma exists_list {X : Scheme.{0}} (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ L : List X.Opens, (∀ u ∈ L, IsAffineOpen u) ∧ (∀ u ∈ L, u ≤ W) ∧ ∀ x ∈ W, ∃ u ∈ L, x ∈ u := by
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
  refine ⟨hs.toFinset.toList.map (fun a : X.affineOpens => a.1), ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hu
    exact a.prop
  · intro u hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
    rw [e]
    exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ s) => (i : X.Opens)) a (by simpa using ha)
  · intro x hx
    rw [e] at hx
    simp only [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨a, List.mem_map.mpr ⟨a, by simpa using ha, rfl⟩, hxa⟩

lemma compact_of_cover {X : Scheme.{0}} (W : X.Opens) (L : List X.Opens) (hA : ∀ u ∈ L, IsAffineOpen u)
    (hle : ∀ u ∈ L, u ≤ W) (hc : ∀ x ∈ W, ∃ u ∈ L, x ∈ u) : IsCompact (W : Set X) := by
  have : (W : Set X) = ⋃ u ∈ L, (u : Set X) := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun hx => let ⟨u, hu, h⟩ := hc x hx; ⟨u, hu, h⟩, fun ⟨u, hu, h⟩ => hle u hu h⟩
  rw [this]
  exact L.finite_toSet.isCompact_biUnion fun u hu => (hA u hu).isCompact

lemma mem_V {X : Scheme.{0}} (L : List X.Opens) (x : X) :
    x ∈ (⨆ u ∈ L, u : X.Opens) ↔ ∃ u ∈ L, x ∈ u := by
  simp

section
variable {S : Scheme.{0}} [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop)
  (hA : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f)
  (hG : ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f)
include hA hG

lemma glue_step {X : Scheme.{0}} (f : X ⟶ S) (hf : FP f) (U : X.Opens) (L' : List X.Opens)
    (hc : Cov X (U :: L'))
    (hV : Cov (⨆ u ∈ L', u : X.Opens).toScheme
        (L'.map ((⨆ u ∈ L', u : X.Opens).ι ⁻¹ᵁ ·)) → P ((⨆ u ∈ L', u : X.Opens).ι ≫ f))
    (hW : P ((U ⊓ ⨆ u ∈ L', u : X.Opens).ι ≫ f)) :
    P f := by
  have hU : IsAffineOpen U := hc.1 U (by simp)
  have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
  have hUV : U ⊔ (⨆ u ∈ L', u : X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨u, hu, hx⟩ := hc.2 x
    rcases List.mem_cons.mp hu with rfl | hu
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hx)
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr ((mem_V L' x).mpr ⟨u, hu, hx⟩))
  refine hG f hf U _ hUV ?_ ?_ ?_
  · haveI : IsAffine U := hU
    exact hA _ inferInstance (fp_res f hf U hU.isCompact)
  · refine hV (cov_pull _ L' hL' (fun u hu => ?_) (fun x hx => (mem_V L' x).mp hx))
    exact le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu
  · exact hW

end

section
variable {S : Scheme.{0}} [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop)
  (hA : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f)
  (hG : ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f)
include hA hG

lemma empty_case {X : Scheme.{0}} (f : X ⟶ S) (hf : FP f) (hc : Cov X []) : P f := by
  have : IsEmpty X := ⟨fun x => by obtain ⟨u, hu, _⟩ := hc.2 x; simp at hu⟩
  exact hA f inferInstance hf

lemma stepA : ∀ (n : ℕ) {X : Scheme.{0}} (f : X ⟶ S) (L : List X.Opens), L.length = n → FP f →
    X.IsSeparated → Cov X L → P f := by
  intro n
  induction n with
  | zero =>
    intro X f L hl hf _ hc
    rw [List.eq_nil_of_length_eq_zero hl] at hc
    exact empty_case P hA hG f hf hc
  | succ n ih =>
    intro X f L hl hf hs hc
    obtain ⟨U, L', rfl⟩ : ∃ U L', L = U :: L' := by
      cases L with
      | nil => simp at hl
      | cons U L' => exact ⟨U, L', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hU : IsAffineOpen U := hc.1 U (by simp)
    have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
    refine glue_step P hA hG f hf U L' hc ?_ ?_
    · intro hcV
      have : (⨆ u ∈ L', u : X.Opens).toScheme.IsSeparated := sep_of (⨆ u ∈ L', u : X.Opens).ι
      refine ih _ _ (by simp [hl]) (fp_res f hf _ ?_) this hcV
      exact compact_of_cover _ L' hL' (fun u hu => le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
        (fun x hx => (mem_V L' x).mp hx)
    · set W : X.Opens := U ⊓ ⨆ u ∈ L', u
      have hA' : ∀ v ∈ L'.map (U ⊓ ·), IsAffineOpen v := by
        intro v hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact hU.inf (hL' u hu)
      have hle : ∀ v ∈ L'.map (U ⊓ ·), v ≤ W := by
        intro v hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact inf_le_inf_left U (le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
      have hcW : ∀ x ∈ W, ∃ v ∈ L'.map (U ⊓ ·), x ∈ v := by
        intro x hx
        obtain ⟨hxU, hxV⟩ := hx
        obtain ⟨u, hu, h⟩ := (mem_V L' x).mp hxV
        exact ⟨U ⊓ u, List.mem_map.mpr ⟨u, hu, rfl⟩, ⟨hxU, h⟩⟩
      have : W.toScheme.IsSeparated := sep_of W.ι
      exact ih _ ((L'.map (U ⊓ ·)).map (W.ι ⁻¹ᵁ ·)) (by simp [hl])
        (fp_res f hf W (compact_of_cover W _ hA' hle hcW)) this (cov_pull W _ hA' hle hcW)

lemma stepB : ∀ (n : ℕ) {X : Scheme.{0}} (f : X ⟶ S) (L : List X.Opens), L.length = n → FP f →
    Cov X L → P f := by
  intro n
  induction n with
  | zero =>
    intro X f L hl hf hc
    rw [List.eq_nil_of_length_eq_zero hl] at hc
    exact empty_case P hA hG f hf hc
  | succ n ih =>
    intro X f L hl hf hc
    obtain ⟨U, L', rfl⟩ : ∃ U L', L = U :: L' := by
      cases L with
      | nil => simp at hl
      | cons U L' => exact ⟨U, L', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hU : IsAffineOpen U := hc.1 U (by simp)
    have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
    have hVc : IsCompact ((⨆ u ∈ L', u : X.Opens) : Set X) :=
      compact_of_cover _ L' hL' (fun u hu => le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
        (fun x hx => (mem_V L' x).mp hx)
    refine glue_step P hA hG f hf U L' hc ?_ ?_
    · intro hcV
      exact ih _ _ (by simp [hl]) (fp_res f hf _ hVc) hcV
    · set W : X.Opens := U ⊓ ⨆ u ∈ L', u
      have : QuasiSeparated f := hf.2.2
      have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      have hWc : IsCompact (W : Set X) :=
        QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU.isCompact (⨆ u ∈ L', u : X.Opens).2 hVc
      obtain ⟨L2, h1, h2, h3⟩ := exists_list W hWc
      haveI : IsAffine U := hU
      have : W.toScheme.IsSeparated := sep_of (X.homOfLE (inf_le_left : W ≤ U))
      exact stepA P hA hG _ (W.ι ≫ f) (L2.map (W.ι ⁻¹ᵁ ·)) rfl (fp_res f hf W hWc) this
        (cov_pull W L2 h1 h2 h3)

end

theorem LeafQCQSInduct_of : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct := by
  intro S _ P hA hG X f hf
  have : QuasiCompact f := hf.2.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨L, h1, -, h3⟩ := exists_list (⊤ : X.Opens) (by simpa using isCompact_univ)
  exact stepB P hA hG _ f L rfl hf ⟨h1, fun x => h3 x trivial⟩

end LateralTheory.E.LeafQCQSInductPf
