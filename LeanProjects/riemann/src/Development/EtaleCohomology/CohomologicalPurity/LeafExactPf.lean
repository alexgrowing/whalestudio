import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd.ExactPf

variable {R : Type} [CommRing R] {A B D I : Cx R}

theorem pb_δ (f : A ⟶ B) {n m : ℤ} (c : Cochain B I n) : δ n m (pb f c) = pb f (δ n m c) :=
  δ_ofHom_comp _ _ _

theorem pb_sub (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c - c') = pb f c - pb f c' :=
  Cochain.comp_sub _ _ _ _

theorem pb_add (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c + c') = pb f c + pb f c' :=
  Cochain.comp_add _ _ _ _

theorem pb_zero (f : A ⟶ B) {n : ℤ} : pb f (0 : Cochain B I n) = 0 :=
  Cochain.comp_zero _ _

theorem pb_w {i : A ⟶ B} {l r : B ⟶ D} (w : i ≫ l = i ≫ r) {n : ℤ} (c : Cochain D I n) :
    pb i (pb l c) = pb i (pb r c) := by
  rw [pb_pb, pb_pb, w]

abbrev zpb (f : A ⟶ B) {n : ℤ} (b : Cocycle B I n) : Cocycle A I n := zcomp (Cocycle.ofHom f) b (zero_add n)

theorem zpb_coe (f : A ⟶ B) {n : ℤ} (b : Cocycle B I n) : (zpb f b).1 = pb f b.1 := rfl

theorem hpb_mk (f : A ⟶ B) {n : ℤ} (b : Cocycle B I n) :
    hpb f I n (CohomologyClass.mk b) = CohomologyClass.mk (zpb f b) := rfl

theorem zero_iff {K L : Cx R} {n : ℤ} (m : ℤ) (hm : m + 1 = n) (x : Cocycle K L n) :
    CohomologyClass.mk x = 0 ↔ ∃ e : Cochain K L m, δ m n e = x.1 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff x m hm]

theorem mk_eq_of {K L : Cx R} {n : ℤ} (m : ℤ) (hm : m + 1 = n) (x y : Cocycle K L n) (e : Cochain K L m)
    (he : x.1 - y.1 = δ m n e) : CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, zero_iff m hm]
  exact ⟨e, by rw [Cocycle.coe_sub, he]⟩

theorem glue_cocycle {i : A ⟶ B} {l r : B ⟶ D} (h : Good i l r I) {k : ℤ} (c c' : Cochain B I k)
    (hc : δ k (k + 1) c = 0) (hc' : δ k (k + 1) c' = 0) (he : pb i c = pb i c') :
    ∃ b : Cocycle D I k, pb l b.1 = c ∧ pb r b.1 = c' := by
  obtain ⟨b, hl, hr⟩ := h.glue k c c' he
  refine ⟨Cocycle.mk b (k + 1) rfl (h.ext _ _ _ ?_ ?_), hl, hr⟩
  · rw [← pb_δ, hl, hc, pb_zero]
  · rw [← pb_δ, hr, hc', pb_zero]

theorem exact1 {i : A ⟶ B} {l r : B ⟶ D} (h : Good i l r I) (n : ℤ) :
    Function.Exact ((hpb l I n).comp (hpb r I n).ker.subtype) (hpb i I n) := by
  intro y
  obtain ⟨β, rfl⟩ := y.mk_surjective
  constructor
  · intro hy
    rw [hpb_mk, zero_iff (n - 1) (by omega)] at hy
    obtain ⟨α, hα⟩ := hy
    obtain ⟨c, hc⟩ := h.surj (n - 1) α
    obtain ⟨b, hl, hr⟩ := glue_cocycle h (β.1 - δ (n - 1) n c) 0
      (by rw [δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero]) (δ_zero _ _)
      (by rw [pb_sub, ← pb_δ, hc, hα, zpb_coe, sub_self, pb_zero])
    refine ⟨⟨CohomologyClass.mk b, ?_⟩, ?_⟩
    · rw [AddMonoidHom.mem_ker, hpb_mk]
      have : zpb r b = 0 := Cocycle.ext (by rw [zpb_coe, hr]; rfl)
      rw [this, CohomologyClass.mk_zero]
    · change hpb l I n (CohomologyClass.mk b) = _
      rw [hpb_mk]
      exact mk_eq_of (n - 1) (by omega) _ _ (-c) (by rw [zpb_coe, hl, δ_neg]; abel)
  · rintro ⟨⟨x, hx⟩, hxy⟩
    rw [← hxy]
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [AddMonoidHom.mem_ker, hpb_mk] at hx
    change hpb i I n (hpb l I n (CohomologyClass.mk b)) = 0
    rw [hpb_mk, hpb_mk]
    have : zpb i (zpb l b) = zpb i (zpb r b) := Cocycle.ext (by simp only [zpb_coe]; exact pb_w h.w _)
    rw [this, ← hpb_mk, hx, map_zero]

theorem exact2 {i : A ⟶ B} {l r : B ⟶ D} (h : Good i l r I) (n : ℤ) (d) (hd : IsDelta i l r I n d) :
    Function.Exact (hpb i I n) d := by
  intro y
  obtain ⟨a, rfl⟩ := y.mk_surjective
  constructor
  · intro h0
    obtain ⟨c, b, ht⟩ := h.tri a
    have hb : CohomologyClass.mk b = 0 := by rw [← hd a c b ht, h0]; rfl
    rw [zero_iff n rfl] at hb
    obtain ⟨e, he⟩ := hb
    obtain ⟨h1, h2, h3⟩ := ht
    let c' : Cocycle B I n := Cocycle.mk (c - pb l e + pb r e) (n + 1) rfl (by
      rw [δ_add, δ_sub, pb_δ, pb_δ, he, h2, h3]; abel)
    refine ⟨CohomologyClass.mk c', ?_⟩
    rw [hpb_mk]
    congr 1
    apply Cocycle.ext
    rw [zpb_coe]
    change pb i (c - pb l e + pb r e) = a.1
    rw [pb_add, pb_sub, pb_w h.w, h1]; abel
  · rintro ⟨y, hy⟩
    obtain ⟨β, rfl⟩ := y.mk_surjective
    rw [← hy]
    have := hd (zpb i β) β.1 0 ⟨rfl, by rw [Cocycle.δ_eq_zero]; exact pb_zero l, pb_zero r⟩
    exact Subtype.ext (this.trans (CohomologyClass.mk_zero _ _ _))

theorem exact3 {i : A ⟶ B} {l r : B ⟶ D} (h : Good i l r I) (n : ℤ) (d) (hd : IsDelta i l r I n d) :
    Function.Exact d ((hpb l I (n + 1)).comp (hpb r I (n + 1)).ker.subtype) := by
  rintro ⟨x, hx⟩
  obtain ⟨b, rfl⟩ := x.mk_surjective
  show hpb l I (n + 1) (CohomologyClass.mk b) = 0 ↔ _
  constructor
  · intro hl
    rw [AddMonoidHom.mem_ker, hpb_mk, zero_iff n rfl] at hx
    rw [hpb_mk, zero_iff n rfl] at hl
    obtain ⟨e₁, he₁⟩ := hl
    obtain ⟨e₂, he₂⟩ := hx
    obtain ⟨g, hg₁, hg₂⟩ := h.glue n e₂ e₂ rfl
    let b' : Cocycle D I (n + 1) := Cocycle.mk (b.1 - δ n (n + 1) g) (n + 1 + 1) rfl (by
      rw [δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero])
    let a : Cocycle A I n := Cocycle.mk (pb i (e₁ - e₂)) (n + 1) rfl (by
      rw [pb_δ, δ_sub, he₁, he₂, zpb_coe, zpb_coe, pb_sub, pb_w h.w, sub_self])
    have ht : Tri i l r a (e₁ - e₂) b' := by
      refine ⟨rfl, ?_, ?_⟩
      · change pb l (b.1 - δ n (n + 1) g) = _
        rw [pb_sub, ← pb_δ, hg₁, δ_sub, he₁, zpb_coe]
      · change pb r (b.1 - δ n (n + 1) g) = _
        rw [pb_sub, ← pb_δ, hg₂, he₂, zpb_coe, sub_self]
    refine ⟨CohomologyClass.mk a, Subtype.ext ((hd a _ b' ht).trans ?_)⟩
    exact mk_eq_of n rfl _ _ (-g) (by change (b.1 - δ n (n + 1) g) - b.1 = _; rw [δ_neg]; abel)
  · rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := y.mk_surjective
    obtain ⟨c, b0, ht⟩ := h.tri a
    have hb : CohomologyClass.mk b = CohomologyClass.mk b0 := by
      rw [← hd a c b0 ht, hy]
    rw [hb, hpb_mk, zero_iff n rfl]
    exact ⟨c, ht.2.1.symm⟩

end ExactPf

theorem LeafExact_of : LeafExact := by
  intro R _ A B D i l r I h n d hd
  exact ⟨ExactPf.exact1 h n, ExactPf.exact2 h n d hd, ExactPf.exact3 h n d hd⟩

end LateralTheory.CohomologicalPurity.Bd
