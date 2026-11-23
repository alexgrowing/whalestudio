import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluingExistence

theorem mul_pow_mem {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (C : Subalgebra Ω L) (v : L)
    (hv : v ∈ C) (hv0 : v ≠ 0) (x : L) (hx : x ∈ Algebra.adjoin Ω ((C : Set L) ∪ {v⁻¹})) :
    ∃ n : ℕ, x * v ^ n ∈ C := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hv0]; exact C.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using C.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * v ^ (n + m) = (x * v ^ n) * v ^ m + (y * v ^ m) * v ^ n := by ring
    rw [this]; exact C.add_mem (C.mul_mem hn (C.pow_mem hv _)) (C.mul_mem hm (C.pow_mem hv _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x * y) * v ^ (n + m) = (x * v ^ n) * (y * v ^ m) := by ring
    rw [this]; exact C.mul_mem hn hm

theorem away {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (C E : Subalgebra Ω L) (v : L)
    (hv : v ∈ C) (hv0 : v ≠ 0) (hCE : C ≤ E) (hE : E = Algebra.adjoin Ω ((C : Set L) ∪ {v⁻¹})) :
    letI := (Subalgebra.inclusion hCE).toRingHom.toAlgebra
    IsLocalization.Away (⟨v, hv⟩ : C) E := by
  letI := (Subalgebra.inclusion hCE).toRingHom.toAlgebra
  have hvi : v⁻¹ ∈ E := hE ▸ Algebra.subset_adjoin (Set.mem_union_right _ rfl)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨v⁻¹, hvi⟩ ^ n, Subtype.ext ?_⟩
    show (v ^ n) * (v⁻¹) ^ n = 1
    rw [← mul_pow, mul_inv_cancel₀ hv0, one_pow]
  · rintro ⟨z, hz⟩
    obtain ⟨n, hn⟩ := mul_pow_mem C v hv hv0 z (hE ▸ hz)
    exact ⟨(⟨z * v ^ n, hn⟩, ⟨⟨v, hv⟩ ^ n, n, rfl⟩), Subtype.ext rfl⟩
  · intro x y h
    refine ⟨1, ?_⟩
    have : (x : L) = y := congrArg (fun w : E => (w : L)) h
    simp [Subtype.ext this]

theorem LeafGlueExists_of : LeafGlueExists := by
  intro Ω L _ _ _ A B u h
  obtain ⟨hu, huA, huB, -, -, -, -, -, -, -, -, hadj, -⟩ := h
  set D := Dr Ω A u
  have hAD : A ≤ D := le_Dr_A A u
  have hBD : B ≤ D := le_Dr_B A B u hadj
  letI iAD : Algebra A D := (Subalgebra.inclusion hAD).toRingHom.toAlgebra
  letI iBD : Algebra B D := (Subalgebra.inclusion hBD).toRingHom.toAlgebra
  haveI : IsLocalization.Away (⟨u, huA⟩ : A) D := away A D u huA hu hAD rfl
  haveI : IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D :=
    away B D u⁻¹ huB (inv_ne_zero hu) hBD (by rw [inv_inv]; exact hadj)
  let fA : Sp D ⟶ Sp A := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom)
  let fB : Sp D ⟶ Sp B := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBD).toRingHom)
  haveI hfA : IsOpenImmersion fA := IsOpenImmersion.of_isLocalization (S := D) (⟨u, huA⟩ : A)
  haveI hfB : IsOpenImmersion fB := IsOpenImmersion.of_isLocalization (S := D) (⟨u⁻¹, huB⟩ : B)
  haveI : ∀ {i j : WalkingSpan} (f : i ⟶ j), IsOpenImmersion ((span fA fB).map f) := by
    intro i j f
    rcases f with _ | j
    · exact inferInstanceAs (IsOpenImmersion (𝟙 _))
    · rcases j with _ | _
      · exact hfA
      · exact hfB
  have hc : fA ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω A)) =
      fB ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
    simp only [fA, fB, ← Spec.map_comp]; rfl
  refine ⟨{
    C0 := pushout fA fB
    c0 := pushout.desc _ _ hc
    iA := pushout.inl fA fB
    iB := pushout.inr fA fB
    hiA := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _))
    hiB := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _))
    hcA := pushout.inl_desc _ _ _
    hcB := pushout.inr_desc _ _ _
    agree := pushout.condition
    cover := ?_
    inter := ?_ }⟩
  · ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, xi, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span fA fB) x
    rcases i with _ | j
    · left; refine ⟨fA xi, ?_⟩
      rw [← colimit.w (span fA fB) (WidePushoutShape.Hom.init WalkingPair.left)]; rfl
    · rcases j with _ | _
      · left; exact ⟨xi, rfl⟩
      · right; exact ⟨xi, rfl⟩
  · ext x
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
      have hab : colimit.ι (span fA fB) (some WalkingPair.left) a =
          colimit.ι (span fA fB) (some WalkingPair.right) b := hb.symm
      obtain ⟨k, fi, fj, y, hy1, hy2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span fA fB)).mp hab
      rcases k with _ | k
      · refine ⟨y, ?_⟩
        rw [← hy1, Subsingleton.elim fi (WidePushoutShape.Hom.init WalkingPair.left)]; rfl
      · rcases k with _ | _
        · cases (show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.left) (some WalkingPair.right) from fj)
        · cases (show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.right) (some WalkingPair.left) from fi)
    · rintro ⟨y, rfl⟩
      refine ⟨⟨fA y, rfl⟩, ⟨fB y, ?_⟩⟩
      show (fB ≫ pushout.inr fA fB).base y = (fA ≫ pushout.inl fA fB).base y
      rw [pushout.condition]

end LateralTheory.E.GluingExistence
