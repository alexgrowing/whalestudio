import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRelPf

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {A B : CochainComplex C ℤ} (φ : A ⟶ B)
  [HomologicalComplex.HasHomotopyCofiber φ] (M : CochainComplex C ℤ)

lemma δ_desc' {m n : ℤ} (α : Cochain A M m) (β : Cochain B M n) (h : m + 1 = n) (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (mappingCone.descCochain φ α β h) = mappingCone.descCochain φ
      (δ m n α + n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (δ n n' β) (by omega) := by
  rw [mappingCone.δ_descCochain _ _ _ _ _ hn']; rfl

lemma desc_eq_iff {m n : ℤ} (h : m + 1 = n) (α α' : Cochain A M m) (β β' : Cochain B M n) :
    mappingCone.descCochain φ α β h = mappingCone.descCochain φ α' β' h ↔ α = α' ∧ β = β' := by
  constructor
  · intro e
    have h1 := congrArg (fun w => (mappingCone.inl φ).comp w (show -1 + n = m by omega)) e
    have h2 := congrArg (fun w => (Cochain.ofHom (mappingCone.inr φ)).comp w (zero_add n)) e
    simp only [mappingCone.inl_descCochain, mappingCone.inr_descCochain] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma desc_zero {m n : ℤ} (h : m + 1 = n) :
    mappingCone.descCochain φ (0 : Cochain A M m) (0 : Cochain B M n) h = 0 := by
  simp [mappingCone.descCochain]

lemma desc_eq_zero_iff {m n : ℤ} (h : m + 1 = n) (α : Cochain A M m) (β : Cochain B M n) :
    mappingCone.descCochain φ α β h = 0 ↔ α = 0 ∧ β = 0 := by
  rw [← desc_zero φ M h, desc_eq_iff]

lemma eq_desc {p d : ℤ} (hp : p + 1 = d) (y : Cochain (mappingCone φ) M d) :
    y = mappingCone.descCochain φ ((mappingCone.inl φ).comp y (show -1 + d = p by omega))
      ((Cochain.ofHom (mappingCone.inr φ)).comp y (zero_add d)) hp := by
  rw [mappingCone.ext_cochain_from_iff φ p d hp]
  simp

lemma core_inj (d p : ℤ) (hp : p + 1 = d)
    (hE : ∀ z : Cochain (mappingCone φ) M d, δ d (d + 1) z = 0 → ∃ y : Cochain (mappingCone φ) M p, δ p d y = z)
    (b : Cochain B M d) (hb : δ d (d + 1) b = 0) (g : Cochain A M p)
    (hg : δ p d g = (Cochain.ofHom φ).comp b (zero_add d)) : ∃ y : Cochain B M p, δ p d y = b := by
  obtain ⟨y, hy⟩ := hE (mappingCone.descCochain φ (-((d + 1).negOnePow • g)) b hp) (by
    rw [δ_desc' _ _ _ _ _ _ rfl]
    simp [hb, hg, desc_zero])
  refine ⟨(Cochain.ofHom (mappingCone.inr φ)).comp y (zero_add p), ?_⟩
  rw [δ_ofHom_comp, hy, mappingCone.inr_descCochain]

lemma core_surj (d p : ℤ) (hp : p + 1 = d)
    (hE : ∀ z : Cochain (mappingCone φ) M (d + 1), δ (d + 1) (d + 1 + 1) z = 0 →
      ∃ y : Cochain (mappingCone φ) M d, δ d (d + 1) y = z)
    (a : Cochain A M d) (ha : δ d (d + 1) a = 0) : ∃ (c : Cochain B M d) (e : Cochain A M p),
      δ d (d + 1) c = 0 ∧ a = (Cochain.ofHom φ).comp c (zero_add d) + δ p d e := by
  obtain ⟨y, hy⟩ := hE (mappingCone.descCochain φ a 0 rfl) (by
    rw [δ_desc' _ _ _ _ _ _ rfl]
    simp [ha, desc_zero])
  rw [eq_desc φ M hp y, δ_desc' _ _ _ _ _ _ rfl, desc_eq_iff] at hy
  obtain ⟨h1, h2⟩ := hy
  refine ⟨(d + 1).negOnePow • (Cochain.ofHom (mappingCone.inr φ)).comp y (zero_add d),
    (mappingCone.inl φ).comp y (show -1 + d = p by omega), by simp [h2], ?_⟩
  rw [← h1, Cochain.comp_units_smul, add_comm]

lemma core_E (p k : ℤ) (hk : k + 1 = p)
    (hI : ∀ b : Cochain B M (p + 1), δ (p + 1) (p + 1 + 1) b = 0 → ∀ g : Cochain A M p,
      δ p (p + 1) g = (Cochain.ofHom φ).comp b (zero_add _) → ∃ y : Cochain B M p, δ p (p + 1) y = b)
    (hS : ∀ a : Cochain A M p, δ p (p + 1) a = 0 → ∃ (c : Cochain B M p) (e : Cochain A M k),
      δ p (p + 1) c = 0 ∧ a = (Cochain.ofHom φ).comp c (zero_add p) + δ k p e)
    (z : Cochain (mappingCone φ) M (p + 1)) (hz : δ (p + 1) (p + 1 + 1) z = 0) :
    ∃ y : Cochain (mappingCone φ) M p, δ p (p + 1) y = z := by
  have hzd := eq_desc φ M (rfl : p + 1 = p + 1) z
  set α := (mappingCone.inl φ).comp z (show -1 + (p + 1) = p by omega)
  set β := (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add (p + 1))
  rw [hzd, δ_desc' _ _ _ _ _ _ rfl, desc_eq_zero_iff] at hz
  obtain ⟨hX, hY⟩ := hz
  obtain ⟨β'', hβ''⟩ := hI β hY (-((p + 1 + 1).negOnePow • α)) (by
    rw [δ_neg, δ_units_smul, eq_neg_of_add_eq_zero_left hX, smul_neg, neg_neg, smul_smul,
      Int.units_mul_self, one_smul])
  obtain ⟨c, e, hc, he⟩ := hS (α + (p + 1 + 1).negOnePow • (Cochain.ofHom φ).comp β'' (zero_add p)) (by
    rw [δ_add, δ_units_smul, δ_ofHom_comp, hβ'', hX])
  refine ⟨mappingCone.descCochain φ e (β'' + (p + 1).negOnePow • c) hk, ?_⟩
  rw [δ_desc' _ _ _ _ _ _ rfl, hzd, desc_eq_iff]
  constructor
  · rw [Cochain.comp_add, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul]
    have he' : δ k p e = α + (p + 1 + 1).negOnePow • (Cochain.ofHom φ).comp β'' (zero_add p) -
        (Cochain.ofHom φ).comp c (zero_add p) := by rw [he]; abel
    rw [he', Int.negOnePow_succ (p + 1)]
    simp only [Units.neg_smul]
    abel
  · rw [δ_add, δ_units_smul, hβ'', hc, smul_zero, add_zero]

lemma sub_iff (X : CochainComplex C ℤ) (n m : ℤ) (hm : m + 1 = n) :
    Subsingleton (CohomologyClass X M n) ↔
      ∀ z : Cochain X M n, δ n (n + 1) z = 0 → ∃ y : Cochain X M m, δ m n y = z := by
  constructor
  · intro hs z hz
    have h0 := Subsingleton.elim (CohomologyClass.mk (Cocycle.mk z (n + 1) rfl hz)) 0
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm] at h0
    simpa using h0
  · intro h
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ m hm]
    exact h _ (Cocycle.δ_eq_zero _ _)

omit [HomologicalComplex.HasHomotopyCofiber φ] in
lemma inj_iff (n m : ℤ) (hm : m + 1 = n) :
    Function.Injective (cpre (Cocycle.ofHom φ) M n n (zero_add n)) ↔
      ∀ b : Cochain B M n, δ n (n + 1) b = 0 → ∀ g : Cochain A M m,
        δ m n g = (Cochain.ofHom φ).comp b (zero_add n) → ∃ y : Cochain B M m, δ m n y = b := by
  constructor
  · intro hi b hb g hg
    have h0 : cpre (Cocycle.ofHom φ) M n n (zero_add n) (CohomologyClass.mk (Cocycle.mk b (n + 1) rfl hb)) = 0 := by
      rw [cpre_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
      exact ⟨g, by simp [zcomp, hg]⟩
    have h1 := (injective_iff_map_eq_zero _).1 hi _ h0
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm] at h1
    simpa using h1
  · intro h
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm] at hx
    obtain ⟨g, hg⟩ := hx
    obtain ⟨y, hy⟩ := h b.1 (Cocycle.δ_eq_zero _ _) g (by simpa [zcomp] using hg)
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
    exact ⟨y, hy⟩

omit [HomologicalComplex.HasHomotopyCofiber φ] in
lemma surj_iff (n m : ℤ) (hm : m + 1 = n) :
    Function.Surjective (cpre (Cocycle.ofHom φ) M n n (zero_add n)) ↔
      ∀ a : Cochain A M n, δ n (n + 1) a = 0 → ∃ (c : Cochain B M n) (e : Cochain A M m),
        δ n (n + 1) c = 0 ∧ a = (Cochain.ofHom φ).comp c (zero_add n) + δ m n e := by
  constructor
  · intro hs a ha
    obtain ⟨x, hx⟩ := hs (CohomologyClass.mk (Cocycle.mk a (n + 1) rfl ha))
    obtain ⟨c, rfl⟩ := x.mk_surjective
    rw [cpre_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ m hm] at hx
    obtain ⟨e, he⟩ := hx
    refine ⟨c.1, -e, Cocycle.δ_eq_zero _ _, ?_⟩
    simp [zcomp] at he
    rw [δ_neg, he]
    abel
  · intro h x
    obtain ⟨a, rfl⟩ := x.mk_surjective
    obtain ⟨c, e, hc, he⟩ := h a.1 (Cocycle.δ_eq_zero _ _)
    refine ⟨CohomologyClass.mk (Cocycle.mk c (n + 1) rfl hc), ?_⟩
    rw [cpre_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ m hm]
    refine ⟨-e, ?_⟩
    simp [zcomp, he]

theorem conn_iff (c : ℤ) :
    (∀ n : ℤ, (n < c - 1 → Function.Bijective (cpre (Cocycle.ofHom φ) M n n (zero_add n))) ∧
      (n < c → Function.Injective (cpre (Cocycle.ofHom φ) M n n (zero_add n)))) ↔
      ∀ n < c, Subsingleton (CohomologyClass (mappingCone φ) M n) := by
  constructor
  · intro h n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    rw [sub_iff M _ (p + 1) p rfl]
    exact core_E φ M p (p - 1) (by omega) ((inj_iff φ M (p + 1) p rfl).1 ((h (p + 1)).2 hn))
      ((surj_iff φ M p (p - 1) (by omega)).1 ((h p).1 (by omega)).2)
  · intro h n
    have hinj : n < c → Function.Injective (cpre (Cocycle.ofHom φ) M n n (zero_add n)) := fun hn =>
      (inj_iff φ M n (n - 1) (by omega)).2 (core_inj φ M n (n - 1) (by omega)
        ((sub_iff M _ n (n - 1) (by omega)).1 (h n hn)))
    refine ⟨fun hn => ⟨hinj (by omega), ?_⟩, hinj⟩
    exact (surj_iff φ M n (n - 1) (by omega)).2 (core_surj φ M n (n - 1) (by omega)
      ((sub_iff M _ (n + 1) n rfl).1 (h (n + 1) (by omega))))

end LateralTheory.E.LeafRelPf

theorem LateralTheory.E.t_E6Cut.LeafRel_of : LateralTheory.E.t_E6Cut.LeafRel := by
  intro R _ F c K L f
  exact LateralTheory.E.LeafRelPf.conn_iff f (res R F) c
