import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section
namespace GlobalTheory.EZ.Ext
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

abbrev ext1 (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    HomologicalComplex (CochainComplex C ℤ) (ComplexShape.down ℕ) where
  X a := (K.X a).extend ComplexShape.embeddingDownNat
  d a b := HomologicalComplex.extendMap (K.d a b) ComplexShape.embeddingDownNat
  shape a b h := by rw [K.shape a b h, HomologicalComplex.extendMap_zero]
  d_comp_d' a b c _ _ := by rw [← HomologicalComplex.extendMap_comp, K.d_comp_d, HomologicalComplex.extendMap_zero]

abbrev ext2 (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (ext1 K).extend ComplexShape.embeddingDownNat

lemma fN (a : ℕ) : ComplexShape.embeddingDownNat.f a = -(a : ℤ) := by simp

variable (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))

def kX {p q : ℤ} {a b : ℕ}
    (ha : ComplexShape.embeddingDownNat.f a = p) (hb : ComplexShape.embeddingDownNat.f b = q) :
    ((ext2 K).X p).X q ≅ (K.X a).X b :=
  (HomologicalComplex.eval _ _ q).mapIso (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat ha) ≪≫
    HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat hb

lemma isZero_ext_of_pos {p q : ℤ} (h : 0 < p ∨ 0 < q) : IsZero (((ext2 K).X p).X q) := by
  rcases le_or_gt p 0 with hp | hp
  · have hq : 0 < q := by omega
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a:ℤ) := ⟨(-p).toNat, by omega⟩
    refine IsZero.of_iso ?_ ((HomologicalComplex.eval _ _ q).mapIso
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) (fN a)))
    exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega)
  · exact (HomologicalComplex.eval _ _ q).map_isZero
      (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega))

abbrev kN (a b : ℕ) : ((ext2 K).X (-(a : ℤ))).X (-(b : ℤ)) ≅ (K.X a).X b :=
  kX K (p := -(a : ℤ)) (q := -(b : ℤ)) (a := a) (b := b) (fN a) (fN b)

lemma kN_hom (a b : ℕ) :
    (kN K a b).hom = (HomologicalComplex.extendXIso
      (ext1 K)
      ComplexShape.embeddingDownNat (i := a) (i' := -(a : ℤ)) (fN _)).hom.f (-(b : ℤ)) ≫
      (HomologicalComplex.extendXIso (K.X a) ComplexShape.embeddingDownNat (i := b) (i' := -(b : ℤ)) (fN _)).hom := rfl

lemma kX_d₁ (a b : ℕ) :
    ((ext2 K).d (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ))).f (-(b : ℤ)) ≫ (kN K a b).hom =
      (kN K (a + 1) b).hom ≫ (K.d (a + 1) a).f b := by
  have h := HomologicalComplex.extend_d_eq
    (ext1 K)
    ComplexShape.embeddingDownNat (i := a + 1) (j := a) (i' := -((a + 1 : ℕ) : ℤ)) (j' := -(a : ℤ)) (fN _) (fN _)
  have hh := HomologicalComplex.extendMap_f (K.d (a + 1) a) ComplexShape.embeddingDownNat (i := b) (i' := -(b:ℤ)) (fN _)
  rw [h, kN_hom, kN_hom]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  have e1 : ∀ {A B : CochainComplex C ℤ} (φ : A ≅ B) (n : ℤ), φ.inv.f n ≫ φ.hom.f n = 𝟙 _ := fun φ n => by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [reassoc_of% (e1 _ (-(b : ℤ)))]
  rw [hh]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma kX_d₂ (a b : ℕ) :
    ((ext2 K).X (-(a : ℤ))).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) ≫ (kN K a b).hom =
      (kN K a (b + 1)).hom ≫ (K.X a).d (b + 1) b := by
  have := HomologicalComplex.Hom.comm (HomologicalComplex.extendXIso
    (ext1 K)
    ComplexShape.embeddingDownNat (i := a) (i' := -(a:ℤ)) (fN _)).hom (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ))
  have h2 := HomologicalComplex.extend_d_eq (K.X a) ComplexShape.embeddingDownNat (i := b + 1) (j := b)
    (i' := -((b + 1 : ℕ) : ℤ)) (j' := -(b : ℤ)) (fN _) (fN _)
  rw [kN_hom, kN_hom]
  have e := this =≫ (HomologicalComplex.extendXIso (K.X a) ComplexShape.embeddingDownNat (i := b) (i' := -(b:ℤ)) (fN _)).hom
  simp only [Category.assoc] at e
  rw [← e, h2]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

section Tot
variable [K.HasTotal (ComplexShape.down ℕ)] [(ext2 K).HasTotal (ComplexShape.up ℤ)]

def cmp {p q n : ℤ} (a b m : ℕ) (ha : ComplexShape.embeddingDownNat.f a = p)
    (hb : ComplexShape.embeddingDownNat.f b = q) (hm : ComplexShape.embeddingDownNat.f m = n)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a, b) = m) :
    ((ext2 K).X p).X q ⟶ ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n :=
  (kX K ha hb).hom ≫ K.ιTotal (ComplexShape.down ℕ) a b m h ≫
    ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat hm).inv

lemma cmp_congr {p q n : ℤ} (a b m a' b' m' : ℕ) (ha : ComplexShape.embeddingDownNat.f a = p)
    (hb : ComplexShape.embeddingDownNat.f b = q) (hm : ComplexShape.embeddingDownNat.f m = n)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a, b) = m)
    (ha' : ComplexShape.embeddingDownNat.f a' = p)
    (hb' : ComplexShape.embeddingDownNat.f b' = q) (hm' : ComplexShape.embeddingDownNat.f m' = n)
    (h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a', b') = m') :
    cmp K a b m ha hb hm h = cmp K a' b' m' ha' hb' hm' h' := by
  obtain rfl : a = a' := ComplexShape.embeddingDownNat.injective_f (ha.trans ha'.symm)
  obtain rfl : b = b' := ComplexShape.embeddingDownNat.injective_f (hb.trans hb'.symm)
  obtain rfl : m = m' := ComplexShape.embeddingDownNat.injective_f (hm.trans hm'.symm)
  rfl

def homF (n : ℤ) : ((ext2 K).total (ComplexShape.up ℤ)).X n ⟶
    ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n :=
  (ext2 K).totalDesc (fun p q h =>
    if hpq : p ≤ 0 ∧ q ≤ 0 then
      cmp K (-p).toNat (-q).toNat (-n).toNat (by simp; omega) (by simp; omega)
        (by simp only [ComplexShape.π_def] at h; simp; omega)
        (by simp only [ComplexShape.π_def] at h ⊢; omega)
    else 0)

lemma ι_homF (a b m : ℕ) (h : a + b = m) :
    (ext2 K).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(m : ℤ)) (by simp only [ComplexShape.π_def]; omega) ≫
      homF K (-(m : ℤ)) =
    (kN K a b).hom ≫ K.ιTotal (ComplexShape.down ℕ) a b m h ≫
      ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN m)).inv := by
  rw [homF, HomologicalComplex₂.ι_totalDesc, dif_pos (by omega)]
  exact cmp_congr K _ _ _ a b m _ _ _ _ (fN a) (fN b) (fN m) h

def invC {n : ℤ} (m : ℕ) (hm : ComplexShape.embeddingDownNat.f m = n) :
    ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n ⟶
      ((ext2 K).total (ComplexShape.up ℤ)).X n :=
  ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat hm).hom ≫
    K.totalDesc (fun a b h => (kN K a b).inv ≫ (ext2 K).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) n
      (by simp only [ComplexShape.π_def] at h ⊢; simp at hm; omega))

lemma invC_congr {n : ℤ} (m m' : ℕ) (hm : ComplexShape.embeddingDownNat.f m = n)
    (hm' : ComplexShape.embeddingDownNat.f m' = n) : invC K m hm = invC K m' hm' := by
  obtain rfl : m = m' := ComplexShape.embeddingDownNat.injective_f (hm.trans hm'.symm)
  rfl

def invF (n : ℤ) : ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n ⟶
    ((ext2 K).total (ComplexShape.up ℤ)).X n :=
  if hn : n ≤ 0 then invC K (-n).toNat (by simp; omega) else 0

lemma ι_invF (a b m : ℕ) (h : a + b = m) :
    K.ιTotal (ComplexShape.down ℕ) a b m h ≫
      ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN m)).inv ≫ invF K (-(m : ℤ)) =
    (kN K a b).inv ≫ (ext2 K).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(m : ℤ))
      (by simp only [ComplexShape.π_def]; omega) := by
  rw [invF, dif_pos (by omega), invC_congr K _ m _ (fN m), invC, Iso.inv_hom_id_assoc,
    HomologicalComplex₂.ι_totalDesc]

end Tot

section Tot2
variable [K.HasTotal (ComplexShape.down ℕ)] [(ext2 K).HasTotal (ComplexShape.up ℤ)]

lemma homF_invF (n : ℤ) : homF K n ≫ invF K n = 𝟙 _ := by
  ext p q h
  by_cases hpq : p ≤ 0 ∧ q ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a:ℤ) := ⟨(-p).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, q = -(b:ℤ) := ⟨(-q).toNat, by omega⟩
    obtain rfl : n = -((a + b : ℕ) : ℤ) := by simp only [ComplexShape.π_def] at h; omega
    rw [reassoc_of% (ι_homF K a b (a + b) rfl), ι_invF K a b (a + b) rfl,
      Iso.hom_inv_id_assoc, Category.comp_id]
  · exact (isZero_ext_of_pos K (by omega)).eq_of_src _ _

lemma invF_homF (n : ℤ) : invF K n ≫ homF K n = 𝟙 _ := by
  by_cases hn : n ≤ 0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m:ℤ) := ⟨(-n).toNat, by omega⟩
    rw [← cancel_epi ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN m)).inv]
    ext a b h
    rw [reassoc_of% (ι_invF K a b m h), ι_homF K a b m h, Iso.inv_hom_id_assoc, Category.comp_id]
  · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega)).eq_of_src _ _

lemma negOnePow_negNat (a : ℕ) : (-(a : ℤ)).negOnePow = (-1 : ℤˣ) ^ a := by
  rw [Int.negOnePow_neg, Int.negOnePow_def, zpow_natCast]

lemma homF_comm (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    homF K i ≫ ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).d i j =
      ((ext2 K).total (ComplexShape.up ℤ)).d i j ≫ homF K j := by
  change i + 1 = j at hij
  ext p q h
  by_cases hpq : p ≤ 0 ∧ q ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a:ℤ) := ⟨(-p).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, q = -(b:ℤ) := ⟨(-q).toNat, by omega⟩
    obtain rfl : i = -((a + b : ℕ) : ℤ) := by simp only [ComplexShape.π_def] at h; omega
    rcases Nat.eq_zero_or_pos (a + b) with hab | hab
    · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega)).eq_of_tgt _ _
    obtain ⟨k, hk⟩ : ∃ k, a + b = k + 1 := ⟨a + b - 1, by omega⟩
    obtain rfl : j = -(k : ℤ) := by omega
    rw [reassoc_of% (ι_homF K a b (a + b) rfl),
      HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat (i := a + b) (j := k) (fN _) (fN _),
      Iso.inv_hom_id_assoc]
    simp only [HomologicalComplex₂.total_d, Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
    have hd₁ : (kN K a b).hom ≫ K.d₁ (ComplexShape.down ℕ) a b k ≫
        ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN k)).inv =
        (ext2 K).d₁ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(k : ℤ)) ≫ homF K (-(k : ℤ)) := by
      rcases a with _ | a'
      · rw [K.d₁_eq_zero _ _ _ _ (by intro hr; change _ + 1 = 0 at hr; omega),
          (ext2 K).d₁_eq' _ (i₁' := 1) (by simp only [ComplexShape.up_Rel]; omega) _ _,
          (isZero_ext_of_pos K (p := 1) (q := -(b:ℤ)) (Or.inl one_pos)).eq_of_src
            ((ext2 K).ιTotalOrZero (ComplexShape.up ℤ) 1 (-(b : ℤ)) (-(k : ℤ))) 0]
        simp
      · rw [K.d₁_eq _ (i₁' := a') rfl _ _ (by simp only [ComplexShape.π_def]; omega),
          (ext2 K).d₁_eq _ (i₁' := -(a' : ℤ)) (by simp only [ComplexShape.up_Rel]; omega) _ _
            (by simp only [ComplexShape.π_def]; omega)]
        have e1 : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a' + 1, b) = 1 := rfl
        have e2 : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (-((a' + 1 : ℕ) : ℤ), -(b : ℤ)) = 1 := rfl
        rw [e1, e2, one_smul, one_smul, Category.assoc, Category.assoc, ι_homF K a' b k (by omega),
          reassoc_of% (kX_d₁ K a' b)]
    have hd₂ : (kN K a b).hom ≫ K.d₂ (ComplexShape.down ℕ) a b k ≫
        ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN k)).inv =
        (ext2 K).d₂ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(k : ℤ)) ≫ homF K (-(k : ℤ)) := by
      rcases b with _ | b'
      · rw [K.d₂_eq_zero _ _ _ _ (by intro hr; change _ + 1 = 0 at hr; omega),
          (ext2 K).d₂_eq' _ _ (i₂' := 1) (by simp only [ComplexShape.up_Rel]; omega) _,
          (isZero_ext_of_pos K (p := -(a : ℤ)) (q := 1) (Or.inr one_pos)).eq_of_src
            ((ext2 K).ιTotalOrZero (ComplexShape.up ℤ) (-(a : ℤ)) 1 (-(k : ℤ))) 0]
        simp
      · rw [K.d₂_eq _ _ (i₂' := b') rfl _ (by simp only [ComplexShape.π_def]; omega),
          (ext2 K).d₂_eq _ _ (i₂' := -(b' : ℤ)) (by simp only [ComplexShape.up_Rel]; omega) _
            (by simp only [ComplexShape.π_def]; omega)]
        have e1 : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a, b' + 1) =
          (-1 : ℤˣ) ^ a := rfl
        have e2 : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (-(a : ℤ), -((b' + 1 : ℕ) : ℤ)) = (-(a : ℤ)).negOnePow := rfl
        rw [e1, e2, negOnePow_negNat, Linear.units_smul_comp, Linear.units_smul_comp, Linear.comp_units_smul,
          Category.assoc, Category.assoc, ι_homF K a b' k (by omega), reassoc_of% (kX_d₂ K a b')]
    rw [hd₁, hd₂]
  · exact (isZero_ext_of_pos K (by omega)).eq_of_src _ _

end Tot2

section Tot3
variable [K.HasTotal (ComplexShape.down ℕ)] [(ext2 K).HasTotal (ComplexShape.up ℤ)]

def totIso : (ext2 K).total (ComplexShape.up ℤ) ≅ (K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat :=
  HomologicalComplex.Hom.isoOfComponents (fun n => ⟨homF K n, invF K n, homF_invF K n, invF_homF K n⟩)
    (fun i j h => homF_comm K i j h)

lemma totIso_inv_f (n : ℤ) : (totIso K).inv.f n = invF K n := rfl

end Tot3

def extHE {A B : ChainComplex C ℕ} (e : HomotopyEquiv A B) :
    HomotopyEquiv (A.extend ComplexShape.embeddingDownNat) (B.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap e.hom ComplexShape.embeddingDownNat
  inv := HomologicalComplex.extendMap e.inv ComplexShape.embeddingDownNat
  homotopyHomInvId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((e.homotopyHomInvId.extend ComplexShape.embeddingDownNat).trans
      (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((e.homotopyInvHomId.extend ComplexShape.embeddingDownNat).trans
      (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

section Sheaves
open GlobalTheory.EtC
variable (R : Type) [CommRing R]

def diagSIso (X : SimplicialObject Spc) :
    ((SimplicialObject.whiskering _ _).obj (free R)).obj (bidiag.obj X) ≅ GlobalTheory.EZ.diag.obj ((freeBi R).obj X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact ((free R).map_comp _ _))

def diagIso (X : SimplicialObject Spc) :
    (chains R).obj (bidiag.obj X) ≅ (diagCx ((freeBi R).obj X)).extend ComplexShape.embeddingDownNat :=
  (ComplexShape.embeddingDownNat.extendFunctor _).mapIso ((alternatingFaceMapComplex _).mapIso (diagSIso R X))

set_option backward.isDefEq.respectTransparency false in
lemma diagIso_hom_f (X : SimplicialObject Spc) (n : ℕ) :
    (diagIso R X).hom.f (-(n : ℤ)) = (chainsXIso R (bidiag.obj X) n).hom ≫
      ((diagCx ((freeBi R).obj X)).extendXIso ComplexShape.embeddingDownNat (fN n)).inv := by
  change (HomologicalComplex.extendMap ((alternatingFaceMapComplex _).map (diagSIso R X).hom)
    ComplexShape.embeddingDownNat).f (-(n:ℤ)) = _
  rw [HomologicalComplex.extendMap_f _ _ (fN n)]
  have h1 : ((alternatingFaceMapComplex (Shv R)).map (diagSIso R X).hom).f n = 𝟙 _ := by
    rw [AlgebraicTopology.alternatingFaceMapComplex_map_f]; rfl
  rw [h1, Category.id_comp]
  rfl

lemma ev_awO (X : SimplicialObject Spc) (n a : ℕ) (ha : a ≤ n) :
    (ev ((freeBi R).obj X)).map (awO n a (n - a)) = (free R).map (awP X n a (n - a)) := by
  rw [awO, if_pos (by omega), ev_map_bop, awP]
  exact ((free R).map_comp _ _).symm

end Sheaves

set_option backward.isDefEq.respectTransparency false in

theorem homotopyEquiv_chains_totChains : ∀ (R : Type) [CommRing R] (X : SimplicialObject GlobalTheory.EtC.Spc), (∃ e : HomotopyEquiv (diagCx ((freeBi R).obj X)) (tot ((freeBi R).obj X)), ∀ n : ℕ, e.hom.f n = awF _ n) → ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X), ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n := by
  intro R _ X ⟨e, he⟩
  haveI : (ext2 (dbl ((freeBi R).obj X))).HasTotal (ComplexShape.up ℤ) := hasTotal_biChains R X
  refine ⟨(HomotopyEquiv.ofIso (diagIso R X)).trans ((extHE e).trans
    (HomotopyEquiv.ofIso (totIso (dbl ((freeBi R).obj X))).symm)), fun n => ?_⟩
  change (diagIso R X).hom.f (-(n:ℤ)) ≫ (HomologicalComplex.extendMap e.hom ComplexShape.embeddingDownNat).f (-(n:ℤ)) ≫
    (totIso (dbl ((freeBi R).obj X))).inv.f (-(n:ℤ)) = _
  rw [diagIso_hom_f, HomologicalComplex.extendMap_f _ _ (fN n), he n, totIso_inv_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [awZ, awF]
  congr 1
  simp only [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := ι_invF (dbl ((freeBi R).obj X)) (a : ℕ) (n - a) n (by omega)
  rw [Category.assoc, ev_awO R X n a (by omega)]
  exact (congrArg ((GlobalTheory.EtC.free R).map (awP X n a (n - a)) ≫ ·) h).trans rfl
