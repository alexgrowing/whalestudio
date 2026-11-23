import Development.EtaleCohomology.EtaleSheaves.CechFiltPf

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.FiltGenPf

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

lemma ofHom_comp_fromSingleMk {X Y : C} {I : CochainComplex C ℤ} (k : ℤ) (h : X ⟶ Y) {q m : ℤ}
    (g : Y ⟶ I.X q) (hq : k + m = q) :
    (Cochain.ofHom ((singleFunctor C k).map h)).comp
      (Cochain.fromSingleMk (p := k) g hq) (zero_add m) = Cochain.fromSingleMk (p := k) (h ≫ g) hq := by
  ext p q' hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  by_cases hp : p = k
  · subst hp
    obtain rfl : q' = q := by lia
    rw [Cochain.fromSingleMk_v, Cochain.fromSingleMk_v]
    change ((HomologicalComplex.single C (ComplexShape.up ℤ) p).map h).f p ≫ _ = _
    simp [HomologicalComplex.single_map_f_self]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

lemma smul_fromSingleMk {X : C} {I : CochainComplex C ℤ} (k : ℤ) (ε : ℤˣ) {q m : ℤ}
    (g : X ⟶ I.X q) (hq : k + m = q) :
    ε • Cochain.fromSingleMk (p := k) g hq = Cochain.fromSingleMk (p := k) (ε • g) hq := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h <;> simp

lemma desc_eta {K L I : CochainComplex C ℤ} (φ : K ⟶ L) {m n : ℤ} (hmn : m + 1 = n)
    (c : Cochain (mappingCone φ) I n) :
    c = mappingCone.descCochain φ ((mappingCone.inl φ).comp c (by lia))
      ((Cochain.ofHom (mappingCone.inr φ)).comp c (zero_add n)) hmn := by
  rw [mappingCone.ext_cochain_from_iff φ m n hmn]
  simp

lemma δ_desc_fromSingle {X Y : C} {I : CochainComplex C ℤ} (k : ℤ) (h : X ⟶ Y) {m m' qa qb qc : ℤ}
    (hm : m + 1 = m') (a : X ⟶ I.X qa) (b : Y ⟶ I.X qb) (ha : k + (m - 1) = qa) (hb : k + m = qb)
    (hc : k + m' = qc) :
    δ m m' (mappingCone.descCochain ((singleFunctor C k).map h) (Cochain.fromSingleMk a ha)
      (Cochain.fromSingleMk b hb) (by lia)) =
    mappingCone.descCochain ((singleFunctor C k).map h)
      (Cochain.fromSingleMk (a ≫ I.d qa qb + m'.negOnePow • (h ≫ b)) hb)
      (Cochain.fromSingleMk (b ≫ I.d qb qc) hc) (by lia) := by
  rw [mappingCone.δ_descCochain _ _ _ _ m' hm, Cochain.δ_fromSingleMk _ _ m qb hb,
    Cochain.δ_fromSingleMk _ _ m' qc hc, ofHom_comp_fromSingleMk, smul_fromSingleMk,
    ← Cochain.fromSingleMk_add]
  rfl

lemma level_of {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ)
    (hk : Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k))) I n))
    (f : K.X k ⟶ I.X (k + (n - 1))) (g : L.X k ⟶ I.X (k + n))
    (hg : g ≫ I.d (k + n) (k + (n + 1)) = 0)
    (hf : f ≫ I.d (k + (n - 1)) (k + n) + (n + 1).negOnePow • (φ.f k ≫ g) = 0) :
    ∃ (a : K.X k ⟶ I.X (k + (n - 1 - 1))) (b : L.X k ⟶ I.X (k + (n - 1))),
      f = a ≫ I.d _ _ + n.negOnePow • (φ.f k ≫ b) ∧ g = b ≫ I.d _ _ := by
  have hk' : Subsingleton (CohomologyClass (mappingCone ((singleFunctor C k).map (φ.f k))) I n) := hk
  let w : Cochain (mappingCone ((singleFunctor C k).map (φ.f k))) I n := mappingCone.descCochain ((singleFunctor C k).map (φ.f k))
    (Cochain.fromSingleMk f (show k + (n - 1) = k + (n - 1) from rfl))
    (Cochain.fromSingleMk g (show k + n = k + n from rfl)) (by lia)
  have hw : δ n (n + 1) w = 0 := by
    simp only [w]
    rw [δ_desc_fromSingle k (φ.f k) rfl f g rfl rfl rfl, hf, hg]
    simp [mappingCone.descCochain]
  have h0 := Subsingleton.elim (CohomologyClass.mk (Cocycle.mk w (n + 1) rfl hw)) 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by lia)] at h0
  obtain ⟨c, hc⟩ := h0
  obtain ⟨a, ha⟩ := Cochain.fromSingleMk_surjective
    ((mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp c (show -1 + (n - 1) = n - 1 - 1 by lia)) (k + (n - 1 - 1)) rfl
  obtain ⟨b, hb⟩ := Cochain.fromSingleMk_surjective
    ((Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp c (zero_add (n - 1))) (k + (n - 1)) rfl
  rw [desc_eta ((singleFunctor C k).map (φ.f k)) (show n - 1 - 1 + 1 = n - 1 by lia) c, ← ha, ← hb,
    δ_desc_fromSingle k (φ.f k) (show n - 1 + 1 = n by lia) a b (by lia) rfl rfl] at hc
  refine ⟨a, b, ?_, ?_⟩
  · have := congrArg (fun x => (mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp x (show -1 + n = n - 1 by lia)) hc
    simp only [w, Cocycle.mk_coe, mappingCone.inl_descCochain] at this
    have := congrArg (Cochain.fromSingleEquiv (show k + (n - 1) = k + (n - 1) from rfl)) this
    simpa using this.symm
  · have := congrArg (fun x => (Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp x (zero_add n)) hc
    simp only [w, Cocycle.mk_coe, mappingCone.inr_descCochain] at this
    have := congrArg (Cochain.fromSingleEquiv (show k + n = k + n from rfl)) this
    simpa using this.symm

lemma δ_desc {K L I : CochainComplex C ℤ} (φ : K ⟶ L) {m n n' : ℤ} (h : m + 1 = n) (hn' : n + 1 = n')
    (α : Cochain K I m) (β : Cochain L I n) :
    δ n n' (mappingCone.descCochain φ α β h) = mappingCone.descCochain φ
      (δ m n α + n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (δ n n' β) (by omega) :=
  mappingCone.δ_descCochain φ α β h n' hn'

def V {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ) (z : Cochain (mappingCone φ) I n) : Prop :=
  (∀ p q (hpq : p + (n - 1) = q), k < p →
    ((mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega)).v p q hpq = 0) ∧
  (∀ p q (hpq : p + n = q), k < p →
    ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v p q hpq = 0)

lemma step {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ)
    (hk : Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k))) I n))
    (z : Cochain (mappingCone φ) I n) (hz : δ n (n + 1) z = 0) (hV : V φ k n z) :
    ∃ c : Cochain (mappingCone φ) I (n - 1), V φ (k - 1) n (z - δ (n - 1) n c) := by
  obtain ⟨hV1, hV2⟩ := hV
  have hzd := desc_eta φ (show n - 1 + 1 = n by omega) z
  generalize hα : (mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega) = α at hV1 hzd
  generalize hβ : (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n) = β at hV2 hzd
  have hV1' : ∀ p q (hpq : p + (n - 1) = q), k < p → α.v p q hpq = 0 := fun p q hpq h => by
    rw [← hα]; exact hV1 p q hpq h
  have hδ := hz
  rw [hzd, δ_desc φ (by omega) rfl] at hδ
  have e1 : δ (n - 1) n α + (n + 1).negOnePow • (Cochain.ofHom φ).comp β (zero_add n) = 0 := by
    have := congrArg (fun x => (mappingCone.inl φ).comp x (show -1 + (n + 1) = n by omega)) hδ
    simpa only [mappingCone.inl_descCochain, Cochain.comp_zero] using this
  have e2 : δ n (n + 1) β = 0 := by
    have := congrArg (fun x => (Cochain.ofHom (mappingCone.inr φ)).comp x (zero_add (n + 1))) hδ
    simpa only [mappingCone.inr_descCochain, Cochain.comp_zero] using this
  have hg : β.v k (k + n) rfl ≫ I.d (k + n) (k + (n + 1)) = 0 := by
    have := Cochain.congr_v e2 k (k + (n + 1)) rfl
    rw [δ_v n (n + 1) rfl β k (k + (n + 1)) rfl (k + n) (k + 1) (by omega) rfl, Cochain.zero_v,
      hV2 (k + 1) (k + (n + 1)) (by omega) (by omega), comp_zero, smul_zero, add_zero] at this
    exact this
  have hf : α.v k (k + (n - 1)) rfl ≫ I.d (k + (n - 1)) (k + n) +
      (n + 1).negOnePow • (φ.f k ≫ β.v k (k + n) rfl) = 0 := by
    have := Cochain.congr_v e1 k (k + n) rfl
    rw [Cochain.add_v, Cochain.units_smul_v,
      δ_v (n - 1) n (by omega) α k (k + n) rfl (k + (n - 1)) (k + 1) (by omega) rfl,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v,
      hV1' (k + 1) (k + n) (by omega) (by omega), comp_zero, smul_zero, add_zero] at this
    exact this
  obtain ⟨a, b, ha, hb⟩ := level_of φ k n hk _ _ hg hf
  refine ⟨mappingCone.descCochain φ (Cochain.single a (n - 1 - 1)) (Cochain.single b (n - 1))
    (by omega), ?_, ?_⟩
  · intro p q hpq hp
    rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inl_descCochain,
      Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v,
      δ_v (n - 1 - 1) (n - 1) (by omega) _ p q hpq (p + (n - 1 - 1)) (p + 1) (by omega) rfl,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      Cochain.single_v_eq_zero a _ (p + 1) q _ (by omega)]
    rcases eq_or_lt_of_le (show k ≤ p by omega) with hkp | hkp
    · subst hkp
      obtain rfl : q = k + (n - 1) := by omega
      have h1 : ((mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega)).v k (k + (n - 1)) hpq =
        α.v k (k + (n - 1)) hpq := by rw [hα]
      rw [Cochain.single_v, Cochain.single_v, h1, ha]
      simp
    · rw [hV1 p q hpq hkp, Cochain.single_v_eq_zero a _ p _ _ (by omega),
        Cochain.single_v_eq_zero b _ p _ _ (by omega)]
      simp
  · intro p q hpq hp
    rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inr_descCochain,
      Cochain.sub_v,
      δ_v (n - 1) n (by omega) _ p q hpq (p + (n - 1)) (p + 1) (by omega) rfl,
      Cochain.single_v_eq_zero b _ (p + 1) q _ (by omega)]
    rcases eq_or_lt_of_le (show k ≤ p by omega) with hkp | hkp
    · subst hkp
      obtain rfl : q = k + n := by omega
      have h2 : ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v k (k + n) hpq =
        β.v k (k + n) hpq := by rw [hβ]
      rw [Cochain.single_v, h2, hb]
      simp
    · rw [(show ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v p q hpq = 0 by rw [hβ]; exact hV2 p q hpq hkp), Cochain.single_v_eq_zero b _ p _ _ (by omega)]
      simp

theorem FiltGen_of : LateralTheory.E.CechFiltPf.FiltGen.{u, v} := by
  intro C _ _ K L I φ n hK hL hI hlev
  have claim : ∀ m : ℕ, ∀ z : Cochain (mappingCone φ) I n, δ n (n + 1) z = 0 →
      ∃ c : Cochain (mappingCone φ) I (n - 1), V φ (-(m : ℤ)) n (z - δ (n - 1) n c) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      refine ⟨0, ?_, ?_⟩
      · intro p q hpq hp
        exact (hK p (by omega)).eq_of_src _ _
      · intro p q hpq hp
        exact (hL p (by omega)).eq_of_src _ _
    | succ m ih =>
      intro z hz
      obtain ⟨c, hc⟩ := ih z hz
      obtain ⟨c', hc'⟩ := step φ (-(m : ℤ)) n (hlev _ (by omega)) (z - δ (n - 1) n c)
        (by rw [δ_sub, δ_δ, sub_zero]; exact hz) hc
      refine ⟨c + c', ?_⟩
      have e : (-((m + 1 : ℕ) : ℤ)) = -(m : ℤ) - 1 := by push_cast; ring
      rw [e, δ_add, ← sub_sub]
      exact hc'
  constructor
  intro x y
  suffices h : ∀ x : CohomologyClass (mappingCone φ) I n, x = 0 by rw [h x, h y]
  intro x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨c, hc1, hc2⟩ := claim (n.toNat + 1) z (Cocycle.δ_eq_zero z (n + 1))
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨c, ?_⟩
  have h0 : (z : Cochain (mappingCone φ) I n) - δ (n - 1) n c = 0 := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    constructor
    · ext p q hpq
      simp only [Cochain.comp_zero, Cochain.zero_v]
      rcases lt_or_ge (-((n.toNat + 1 : ℕ) : ℤ)) p with hp | hp
      · exact hc1 p q hpq hp
      · exact (hI q (by omega)).eq_of_tgt _ _
    · ext p q hpq
      simp only [Cochain.comp_zero, Cochain.zero_v]
      rcases lt_or_ge (-((n.toNat + 1 : ℕ) : ℤ)) p with hp | hp
      · exact hc2 p q hpq hp
      · exact (hI q (by omega)).eq_of_tgt _ _
  rw [sub_eq_zero] at h0
  exact h0.symm

end LateralTheory.E.FiltGenPf
