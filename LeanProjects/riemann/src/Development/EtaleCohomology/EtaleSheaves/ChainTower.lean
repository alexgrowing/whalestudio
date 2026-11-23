import Development.EtaleCohomology.EtaleSheaves.LeafLevelPf
import Development.EtaleCohomology.EtaleSheaves.LeafRelPf

noncomputable section
open CategoryTheory Limits Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.LeafRelPf

namespace LateralTheory.E.ChainTower

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

def Rl {A B : CochainComplex C ℤ} (φ : A ⟶ B) (M : CochainComplex C ℤ) (k m n : ℤ) : Prop :=
  ∀ (α : Cochain A M m) (β : Cochain B M n), δ n (n + 1) β = 0 → δ m n α = (Cochain.ofHom φ).comp β (zero_add n) →
    ∃ (a : Cochain A M k) (b : Cochain B M m), δ m n b = β ∧ δ k m a + (Cochain.ofHom φ).comp b (zero_add m) = α

def El {X Y : C} (g : X ⟶ Y) (M : CochainComplex C ℤ) (k m n : ℤ) : Prop :=
  ∀ (α : X ⟶ M.X m) (β : Y ⟶ M.X n), β ≫ M.d n (n + 1) = 0 → α ≫ M.d m n = g ≫ β →
    ∃ (a : X ⟶ M.X k) (b : Y ⟶ M.X m), b ≫ M.d m n = β ∧ a ≫ M.d k m + g ≫ b = α

theorem sub_iff_Rl {A B : CochainComplex C ℤ} (φ : A ⟶ B) [HomologicalComplex.HasHomotopyCofiber φ]
    (M : CochainComplex C ℤ) (k m n : ℤ) (hk : k + 1 = m) (hm : m + 1 = n) :
    Subsingleton (CohomologyClass (mappingCone φ) M n) ↔ Rl φ M k m n := by
  rw [sub_iff M _ n m hm]
  constructor
  · intro h α β hβ hα
    obtain ⟨y, hy⟩ := h (mappingCone.descCochain φ α (n.negOnePow • β) hm) (by
      rw [δ_desc' _ _ _ _ _ _ rfl, desc_eq_zero_iff]
      refine ⟨?_, by rw [δ_units_smul, hβ, smul_zero]⟩
      rw [hα, Cochain.comp_units_smul, smul_smul, Int.negOnePow_succ, neg_mul, Int.units_mul_self]
      simp)
    rw [eq_desc φ M hk y, δ_desc' _ _ _ _ _ _ hm, desc_eq_iff] at hy
    obtain ⟨h1, h2⟩ := hy
    refine ⟨(mappingCone.inl φ).comp y (show -1 + m = k by omega),
      n.negOnePow • (Cochain.ofHom (mappingCone.inr φ)).comp y (zero_add m), ?_, ?_⟩
    · rw [δ_units_smul, h2, smul_smul, Int.units_mul_self, one_smul]
    · rw [Cochain.comp_units_smul]; exact h1
  · intro h z hz
    have hzd := eq_desc φ M hm z
    set α := (mappingCone.inl φ).comp z (show -1 + n = m by omega)
    set β := (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)
    rw [hzd, δ_desc' _ _ _ _ _ _ rfl, desc_eq_zero_iff] at hz
    obtain ⟨hX, hY⟩ := hz
    obtain ⟨a, b, h1, h2⟩ := h α (n.negOnePow • β) (by rw [δ_units_smul, hY, smul_zero]) (by
      rw [eq_neg_of_add_eq_zero_left hX, Cochain.comp_units_smul, Int.negOnePow_succ]
      simp)
    refine ⟨mappingCone.descCochain φ a (n.negOnePow • b) hk, ?_⟩
    rw [δ_desc' _ _ _ _ _ _ hm, hzd, desc_eq_iff]
    constructor
    · rw [Cochain.comp_units_smul, smul_smul, Int.units_mul_self, one_smul, h2]
    · rw [δ_units_smul, h1, smul_smul, Int.units_mul_self, one_smul]

theorem El_iso {X Y X' Y' : C} {g : X ⟶ Y} {g' : X' ⟶ Y'} (e : X' ≅ X) (e' : Y' ≅ Y) (w : e.hom ≫ g = g' ≫ e'.hom)
    (M : CochainComplex C ℤ) (k m n : ℤ) (h : El g M k m n) : El g' M k m n := by
  intro α β hβ hα
  have w' : g ≫ e'.inv = e.inv ≫ g' := by
    rw [Iso.comp_inv_eq, Category.assoc, ← w, Iso.inv_hom_id_assoc]
  obtain ⟨a, b, h1, h2⟩ := h (e.inv ≫ α) (e'.inv ≫ β) (by simp [hβ]) (by
    rw [Category.assoc, hα, ← Category.assoc, ← w', Category.assoc])
  refine ⟨e.hom ≫ a, e'.hom ≫ b, by simp [h1], ?_⟩
  rw [← Category.assoc g', ← w, Category.assoc, Category.assoc, ← Preadditive.comp_add, h2, Iso.hom_inv_id_assoc]

theorem δ_top {A M : CochainComplex C ℤ} {m n : ℤ} (hm : m + 1 = n) (z : Cochain A M m) (s e d : ℤ) (he : s + m = e)
    (hd : s + n = d) (hz : ∀ q (h : s + 1 + m = q), z.v (s + 1) q h = 0 ∨ A.d s (s + 1) = 0) :
    (δ m n z).v s d hd = z.v s e he ≫ M.d e d := by
  rw [δ_v m n hm z s d hd e (s + 1) (by omega) rfl]
  rcases hz d (by omega) with h | h <;> rw [h] <;> simp

theorem comp_ofHom_v {A B M : CochainComplex C ℤ} (φ : A ⟶ B) {n : ℤ} (z : Cochain B M n) (p q : ℤ) (h : p + n = q) :
    ((Cochain.ofHom φ).comp z (zero_add n)).v p q h = φ.f p ≫ z.v p q h := by
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]

def V {A M : CochainComplex C ℤ} {n : ℤ} (s : ℤ) (z : Cochain A M n) : Prop :=
  ∀ p q (h : p + n = q), s < p → z.v p q h = 0

theorem V_single {A M : CochainComplex C ℤ} {s e : ℤ} (g : A.X s ⟶ M.X e) (n : ℤ) : V s (Cochain.single g n) :=
  fun _ _ _ hp => Cochain.single_v_eq_zero _ _ _ _ _ (by omega)

theorem V_δ {A M : CochainComplex C ℤ} {m n : ℤ} (hm : m + 1 = n) (s : ℤ) (z : Cochain A M m) (hz : V s z) :
    V s (δ m n z) := by
  intro p q h hp
  rw [δ_top hm z p (p + m) q rfl h (fun _ _ => Or.inl (hz _ _ _ (by omega))), hz _ _ _ hp, zero_comp]

def Rs {A B : CochainComplex C ℤ} (φ : A ⟶ B) (M : CochainComplex C ℤ) (k m n s : ℤ) : Prop :=
  ∀ (α : Cochain A M m) (β : Cochain B M n), V s α → V s β → δ n (n + 1) β = 0 →
    δ m n α = (Cochain.ofHom φ).comp β (zero_add n) →
    ∃ (a : Cochain A M k) (b : Cochain B M m), δ m n b = β ∧ δ k m a + (Cochain.ofHom φ).comp b (zero_add m) = α

theorem step {A B : CochainComplex C ℤ} (φ : A ⟶ B) (M : CochainComplex C ℤ) (k m n s : ℤ) (hk : k + 1 = m)
    (hm : m + 1 = n) (hE : El (φ.f s) M (s + k) (s + m) (s + n)) (h : Rs φ M k m n (s - 1)) : Rs φ M k m n s := by
  intro α β vα vβ hβ hα
  obtain ⟨a, b, h1, h2⟩ := hE (α.v s _ rfl) (β.v s _ rfl) (by
      rw [← δ_top rfl β s _ (s + n + 1) rfl (by omega) (fun _ _ => Or.inl (vβ _ _ _ (by omega))), hβ]; rfl) (by
      rw [← δ_top hm α s _ _ rfl rfl (fun _ _ => Or.inl (vα _ _ _ (by omega))), hα, comp_ofHom_v])
  have va := V_single a k
  have vb := V_single b m
  obtain ⟨a', b', h3, h4⟩ := h (α - (δ k m (Cochain.single a k) + (Cochain.ofHom φ).comp (Cochain.single b m) (zero_add m)))
    (β - δ m n (Cochain.single b m)) (by
      intro p q hpq hp
      rw [Cochain.sub_v, Cochain.add_v, comp_ofHom_v]
      rcases lt_or_eq_of_le (show s ≤ p by omega) with h' | h'
      · rw [vα _ _ _ h', V_δ hk s _ va _ _ _ h', vb _ _ _ h']; simp
      · subst h' hpq
        rw [δ_top hk _ s _ _ rfl rfl (fun _ _ => Or.inl (va _ _ _ (by omega))), Cochain.single_v, Cochain.single_v, h2,
          sub_self]) (by
      intro p q hpq hp
      rw [Cochain.sub_v]
      rcases lt_or_eq_of_le (show s ≤ p by omega) with h' | h'
      · rw [vβ _ _ _ h', V_δ hm s _ vb _ _ _ h']; simp
      · subst h' hpq
        rw [δ_top hm _ s _ _ rfl rfl (fun _ _ => Or.inl (vb _ _ _ (by omega))), Cochain.single_v, h1, sub_self])
    (by rw [δ_sub, δ_δ, hβ, sub_zero])
    (by rw [δ_sub, δ_add, δ_δ, zero_add, δ_ofHom_comp, hα, Cochain.comp_sub])
  refine ⟨a' + Cochain.single a k, b' + Cochain.single b m, ?_, ?_⟩
  · rw [δ_add, h3]; abel
  · rw [δ_add, Cochain.comp_add, add_add_add_comm, h4]; abel

theorem base {A B : CochainComplex C ℤ} (φ : A ⟶ B) (M : CochainComplex C ℤ) (hM : ∀ q < 0, IsZero (M.X q))
    (k m n s : ℤ) (hm : m + 1 = n) (hs : s + n < 0) : Rs φ M k m n s := by
  intro α β vα vβ _ _
  have hα : α = 0 := Cochain.ext _ _ (fun p q hpq => by
    rcases lt_or_ge s p with h | h
    · exact vα p q hpq h
    · exact (hM q (by omega)).eq_of_tgt _ _)
  have hβ : β = 0 := Cochain.ext _ _ (fun p q hpq => by
    rcases lt_or_ge s p with h | h
    · exact vβ p q hpq h
    · exact (hM q (by omega)).eq_of_tgt _ _)
  exact ⟨0, 0, by simp [hβ], by simp [hα]⟩

theorem tower {A B : CochainComplex C ℤ} (φ : A ⟶ B) (M : CochainComplex C ℤ) (hM : ∀ q < 0, IsZero (M.X q))
    (hA : ∀ q, 0 < q → IsZero (A.X q)) (hB : ∀ q, 0 < q → IsZero (B.X q)) (k m n : ℤ) (hk : k + 1 = m) (hm : m + 1 = n)
    (hE : ∀ p : ℕ, El (φ.f (-(p : ℤ))) M (-(p : ℤ) + k) (-(p : ℤ) + m) (-(p : ℤ) + n)) : Rl φ M k m n := by
  have ind : ∀ j p : ℕ, n < p + j → Rs φ M k m n (-(p : ℤ)) := by
    intro j
    induction j with
    | zero => intro p hp; exact base φ M hM k m n _ hm (by push_cast at hp; omega)
    | succ j ih =>
      intro p hp
      have h2 := ih (p + 1) (by push_cast at hp ⊢; omega)
      have e : (-((p + 1 : ℕ) : ℤ)) = -(p : ℤ) - 1 := by push_cast; ring
      rw [e] at h2
      exact step φ M k m n _ hk hm (hE p) h2
  intro α β
  exact ind (n.toNat + 1) 0 (by omega) α β (fun p q _ hp => (hA p (by simpa using hp)).eq_of_src _ _)
    (fun p q _ hp => (hB p (by simpa using hp)).eq_of_src _ _)

theorem El_of_single [HasZeroObject C] {X Y : C} (g : X ⟶ Y) (M : CochainComplex C ℤ) (k m n : ℤ) (hk : k + 1 = m)
    (hm : m + 1 = n) (h : Rl ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map g) M k m n) : El g M k m n := by
  refine El_iso (g := ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map g).f 0)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).symm
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).symm
    (by simp [HomologicalComplex.single_map_f_self]) M k m n ?_
  intro α β hβ hα
  have hz : ∀ (Z : C) (p : ℤ), p ≠ 0 → IsZero (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z).X p) :=
    fun Z p hp => HomologicalComplex.isZero_single_obj_X _ _ _ _ hp
  have hd : ∀ (Z : C), ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z).d 0 (0 + 1) = 0 :=
    fun Z => (hz Z _ (by norm_num)).eq_of_tgt _ _
  obtain ⟨a, b, h1, h2⟩ := h (Cochain.single α m) (Cochain.single β n) (Cochain.ext _ _ (fun p q hpq => by
      by_cases hp : p = 0
      · subst hp
        obtain rfl : q = n + 1 := by omega
        rw [δ_top rfl _ 0 n _ (zero_add n) hpq (fun _ _ => Or.inr (hd Y)), Cochain.single_v, hβ]; rfl
      · exact (hz Y p hp).eq_of_src _ _)) (Cochain.ext _ _ (fun p q hpq => by
      by_cases hp : p = 0
      · subst hp
        obtain rfl : n = q := by omega
        rw [δ_top hm _ 0 m _ (zero_add m) hpq (fun _ _ => Or.inr (hd X)), Cochain.single_v, comp_ofHom_v,
          Cochain.single_v, hα]
      · exact (hz X p hp).eq_of_src _ _))
  refine ⟨a.v 0 k (zero_add k), b.v 0 m (zero_add m), ?_, ?_⟩
  · rw [← δ_top hm b 0 m n (zero_add m) (zero_add n) (fun _ _ => Or.inr (hd Y)), h1, Cochain.single_v]
  · rw [← δ_top hk a 0 k m (zero_add k) (zero_add m) (fun _ _ => Or.inr (hd X)), ← comp_ofHom_v, ← Cochain.add_v, h2,
      Cochain.single_v]

theorem chains_zero (R : Type) [CommRing R] (U : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj U).X i) := by
  change IsZero ((((chainsN R).obj U).extend ComplexShape.embeddingDownNat).X i)
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  have : -(j : ℤ) = i := hj
  omega

theorem res_zero (R : Type) [CommRing R] (F : Shv R) (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) := by
  have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 q (by omega)

theorem chains_nat (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p))) =
      ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom := by
  have := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl
  change _ = (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(p : ℤ)) ≫ _
  rw [this]
  unfold chainsXIso
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem tower_body (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E')
    (h : ∀ p : ℕ, ∀ n : ℤ, n < c - p →
      Subsingleton (HK R (LateralTheory.E.LeafLevelPf.cone0 R (f.app (op (SimplexCategory.mk p)))) F n))
    (n : ℤ) (hn : n < c) : Subsingleton (HK R (mappingCone ((chains R).map f)) F n) := by
  refine (sub_iff_Rl _ (res R F) (n - 2) (n - 1) n (by omega) (by omega)).2 ?_
  refine tower _ _ (res_zero R F) (chains_zero R E) (chains_zero R E') _ _ _ (by omega) (by omega) (fun p => ?_)
  refine El_iso (chainsXIso R E p) (chainsXIso R E' p) (chains_nat R f p) _ _ _ _ ?_
  refine El_of_single _ _ _ _ _ (by omega) (by omega) ?_
  exact (sub_iff_Rl _ (res R F) _ _ _ (by omega) (by omega)).1 (h p _ (by omega))

theorem LeafFilt_of : LateralTheory.E.LeafLevelPf.LeafFilt :=
  fun _ R _ F c _ _ f h n hn => tower_body R F c f h n hn

end LateralTheory.E.ChainTower
