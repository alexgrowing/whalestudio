import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd

section Pf
variable {R : Type} [CommRing R] {A B D : Cx R} {i : A ⟶ B} {l r : B ⟶ D} {I : Cx R}

theorem pb_δ (f : A ⟶ B) {n m : ℤ} (c : Cochain B I n) : pb f (δ n m c) = δ n m (pb f c) := by
  simp [pb]

theorem pb_sub (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c - c') = pb f c - pb f c' := by
  simp [pb]

theorem pb_zero (f : A ⟶ B) {n : ℤ} : pb f (0 : Cochain B I n) = 0 := by
  simp [pb]

theorem pb_add (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c + c') = pb f c + pb f c' := by
  simp [pb]

theorem Tri.sub {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n} {b b' : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (h' : Tri i l r a' c' b') : Tri i l r (a - a') (c - c') (b - b') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [pb_sub, h1, h1', Cocycle.coe_sub]
  · rw [Cocycle.coe_sub, pb_sub, h2, h2', δ_sub]
  · rw [Cocycle.coe_sub, pb_sub, h3, h3', sub_zero]

theorem Tri.add {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n} {b b' : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (h' : Tri i l r a' c' b') : Tri i l r (a + a') (c + c') (b + b') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [pb_add, h1, h1', Cocycle.coe_add]
  · rw [Cocycle.coe_add, pb_add, h2, h2', δ_add]
  · rw [Cocycle.coe_add, pb_add, h3, h3', add_zero]

theorem Good.mk_zero (hG : Good i l r I) {n : ℤ} {a : Cocycle A I n} {c : Cochain B I n} {b : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (ha : a ∈ coboundaries A I n) : CohomologyClass.mk b = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨f, hf⟩ := (mem_coboundaries_iff a (n - 1) (by omega)).1 ha
  obtain ⟨g, hg⟩ := hG.surj (n - 1) f
  obtain ⟨e, he1, he2⟩ := hG.glue n (c - δ (n - 1) n g) 0 (by
    rw [pb_sub, pb_δ, hg, hf, h1, sub_self, pb_zero])
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff b n rfl]
  refine ⟨e, hG.ext (n + 1) _ _ ?_ ?_⟩
  · rw [pb_δ, he1, h2, δ_sub, δ_δ, sub_zero]
  · rw [pb_δ, he2, h3, δ_zero]

theorem Good.mk_eq (hG : Good i l r I) {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n}
    {b b' : Cocycle D I (n + 1)} (h : Tri i l r a c b) (h' : Tri i l r a' c' b')
    (ha : a - a' ∈ coboundaries A I n) : CohomologyClass.mk b = CohomologyClass.mk b' := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub]
  exact hG.mk_zero (h.sub h') ha

theorem tri_zero {n : ℤ} : Tri i l r (0 : Cocycle A I n) 0 (0 : Cocycle D I (n + 1)) :=
  ⟨by rw [pb_zero, Cocycle.coe_zero], by rw [Cocycle.coe_zero, pb_zero, δ_zero], by rw [Cocycle.coe_zero, pb_zero]⟩

theorem Tri.ker {n : ℤ} {a : Cocycle A I n} {c : Cochain B I n} {b : Cocycle D I (n + 1)} (h : Tri i l r a c b) :
    CohomologyClass.mk b ∈ (hpb r I (n + 1)).ker := by
  rw [AddMonoidHom.mem_ker, hpb, cpre_mk, CohomologyClass.mk_eq_zero_iff]
  have : zcomp (Cocycle.ofHom r) b (zero_add (n + 1)) = 0 := Cocycle.ext (by
    change pb r b.1 = _
    rw [h.2.2, Cocycle.coe_zero])
  rw [this]
  exact zero_mem _

theorem LeafDelta_of : LeafDelta := by
  intro R _ A B D i l r I hG n
  choose c b hcb using fun a : Cocycle A I n => hG.tri a
  let F : Cocycle A I n →+ (hpb r I (n + 1)).ker :=
    AddMonoidHom.mk' (fun a => ⟨CohomologyClass.mk (b a), (hcb a).ker⟩) (fun a a' => by
      apply Subtype.ext
      change CohomologyClass.mk (b (a + a')) = CohomologyClass.mk (b a) + CohomologyClass.mk (b a')
      rw [← CohomologyClass.mk_add]
      exact hG.mk_eq (hcb _) ((hcb a).add (hcb a')) (by rw [sub_self]; exact zero_mem _))
  refine ⟨CohomologyClass.descAddMonoidHom F ?_, ?_⟩
  · intro a ha
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    change CohomologyClass.mk (b a) = 0
    rw [← CohomologyClass.mk_zero D I (n + 1)]
    exact hG.mk_eq (hcb a) tri_zero (by rw [sub_zero]; exact ha)
  · intro a c' b' h
    change CohomologyClass.mk (b a) = _
    exact hG.mk_eq (hcb a) h (by rw [sub_self]; exact zero_mem _)

end Pf
end LateralTheory.CohomologicalPurity.Bd
