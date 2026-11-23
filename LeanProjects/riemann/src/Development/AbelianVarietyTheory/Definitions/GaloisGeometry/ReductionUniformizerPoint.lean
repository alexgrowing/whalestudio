import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

def ideal (S : Finset ι) : X.IdealSheafData := ⨆ i ∈ S, I i

theorem le_ideal {S : Finset ι} {i : ι} (h : i ∈ S) : I i ≤ ideal I S :=
  le_iSup₂ (f := fun i (_ : i ∈ S) => I i) i h

theorem ideal_mono {S S' : Finset ι} (h : S ⊆ S') : ideal I S ≤ ideal I S' :=
  iSup₂_le fun _ hi => le_ideal I (h hi)

@[simp] theorem ideal_empty : ideal I ∅ = ⊥ := by simp [ideal]

@[simp] theorem ideal_singleton (i : ι) : ideal I {i} = I i := by simp [ideal]

def Y (S : Finset ι) : Scheme.{0} := (ideal I S).subscheme

def Yι (S : Finset ι) : Y I S ⟶ X := (ideal I S).subschemeι

instance (S : Finset ι) : IsClosedImmersion (Yι I S) :=
  inferInstanceAs (IsClosedImmersion (ideal I S).subschemeι)

@[simp] theorem ker_Yι (S : Finset ι) : (Yι I S).ker = ideal I S := Scheme.IdealSheafData.ker_subschemeι _

def incl {S S' : Finset ι} (h : S ⊆ S') : Y I S' ⟶ Y I S :=
  Scheme.IdealSheafData.inclusion (ideal_mono I h)

@[reassoc (attr := simp)]
theorem incl_Yι {S S' : Finset ι} (h : S ⊆ S') : incl I h ≫ Yι I S = Yι I S' :=
  Scheme.IdealSheafData.inclusion_subschemeι _

@[simp]
theorem incl_refl (S : Finset ι) : incl I (subset_refl S) = 𝟙 (Y I S) :=
  Scheme.IdealSheafData.inclusion_id _

@[reassoc (attr := simp)]
theorem incl_comp {S S' S'' : Finset ι} (h : S ⊆ S') (h' : S' ⊆ S'') :
    incl I h' ≫ incl I h = incl I (h.trans h') :=
  Scheme.IdealSheafData.inclusion_comp _ _

instance {S S' : Finset ι} (h : S ⊆ S') : IsClosedImmersion (incl I h) := by
  have : IsClosedImmersion (incl I h ≫ Yι I S) := by rw [incl_Yι]; infer_instance
  exact IsClosedImmersion.of_comp (incl I h) (Yι I S)

abbrev Idx (ι : Type) (s : ℕ) : Type := {S : Finset ι // S.card = s + 1}

def Ystr (s : ℕ) : Scheme.{0} := ∐ fun S : Idx ι s => Y I S.1

def inj {s : ℕ} (S : Idx ι s) : Y I S.1 ⟶ Ystr I s := Sigma.ι (fun S : Idx ι s => Y I S.1) S

def Ystrπ (s : ℕ) : Ystr I s ⟶ X := Sigma.desc fun S : Idx ι s => Yι I S.1

@[reassoc (attr := simp)]
theorem inj_Ystrπ {s : ℕ} (S : Idx ι s) : inj I S ≫ Ystrπ I s = Yι I S.1 := Sigma.ι_desc _ _

theorem Ystr_hom_ext {s : ℕ} {Z : Scheme.{0}} {f g : Ystr I s ⟶ Z} (h : ∀ S : Idx ι s, inj I S ≫ f = inj I S ≫ g) :
    f = g :=
  Sigma.hom_ext _ _ h

theorem incl_inj_congr {s : ℕ} {A : Finset ι} {T T' : Idx ι s} (e : T.1 = T'.1) (h : T.1 ⊆ A) (h' : T'.1 ⊆ A) :
    incl I h ≫ inj I T = incl I h' ≫ inj I T' := by
  obtain ⟨T, hT⟩ := T
  obtain ⟨T', hT'⟩ := T'
  simp only at e
  subst e
  rfl

section Face

variable [LinearOrder ι]

def face {s : ℕ} (S : Idx ι (s + 1)) (j : Fin (s + 2)) : Idx ι s :=
  ⟨S.1.erase (S.1.orderEmbOfFin S.2 j), by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), S.2]; rfl⟩

theorem face_subset {s : ℕ} (S : Idx ι (s + 1)) (j : Fin (s + 2)) : (face S j).1 ⊆ S.1 :=
  Finset.erase_subset _ _

theorem orderEmbOfFin_erase {S : Finset ι} {n : ℕ} (h : S.card = n + 1) (k : Fin (n + 1))
    (h' : (S.erase (S.orderEmbOfFin h k)).card = n) (m : Fin n) :
    (S.erase (S.orderEmbOfFin h k)).orderEmbOfFin h' m = S.orderEmbOfFin h (k.succAbove m) := by
  have := Finset.orderEmbOfFin_unique h' (f := fun m => S.orderEmbOfFin h (k.succAbove m))
    (fun m => Finset.mem_erase.2 ⟨fun e => Fin.succAbove_ne k m ((S.orderEmbOfFin h).injective e),
      Finset.orderEmbOfFin_mem _ _ _⟩)
    ((S.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove k))
  exact (congrFun this m).symm

theorem face_face {s : ℕ} (S : Idx ι (s + 2)) {i j : Fin (s + 2)} (hij : i ≤ j) :
    (face (face S j.succ) i).1 = (face (face S i.castSucc) j).1 := by
  simp only [face]
  rw [orderEmbOfFin_erase, orderEmbOfFin_erase,
    Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.2 hij),
    Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.2 hij)]
  exact Finset.erase_right_comm

def δ (s : ℕ) (j : Fin (s + 2)) : Ystr I (s + 1) ⟶ Ystr I s :=
  Sigma.desc fun S : Idx ι (s + 1) => incl I (face_subset S j) ≫ inj I (face S j)

@[reassoc (attr := simp)]
theorem inj_δ {s : ℕ} (j : Fin (s + 2)) (S : Idx ι (s + 1)) :
    inj I S ≫ δ I s j = incl I (face_subset S j) ≫ inj I (face S j) :=
  Sigma.ι_desc _ _

@[reassoc (attr := simp)]
theorem δ_Ystrπ (s : ℕ) (j : Fin (s + 2)) : δ I s j ≫ Ystrπ I s = Ystrπ I (s + 1) :=
  Ystr_hom_ext I fun S => by simp

theorem δ_comp_δ {s : ℕ} {i j : Fin (s + 2)} (hij : i ≤ j) :
    δ I (s + 1) j.succ ≫ δ I s i = δ I (s + 1) i.castSucc ≫ δ I s j :=
  Ystr_hom_ext I fun S => by
    simp only [inj_δ_assoc, Category.assoc, inj_δ, incl_comp_assoc]
    exact incl_inj_congr I (face_face S hij) _ _

end Face

end GlobalTheory.Strata

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

section Fibre

variable {O : Type} [CommRing O] (p : X ⟶ Spec (CommRingCat.of O)) (ϖ : O)

def resMap : Spec (CommRingCat.of (O ⧸ Ideal.span {ϖ})) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ϖ})))

instance : IsClosedImmersion (resMap ϖ) := by
  unfold resMap; exact IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of O) _

abbrev fibre : Scheme.{0} := pullback p (resMap ϖ)

def fibreIdeal : X.IdealSheafData := (pullback.fst p (resMap ϖ)).ker

def toFibre (S : Finset ι) (h : fibreIdeal p ϖ ≤ ideal I S) : Y I S ⟶ fibre p ϖ :=
  IsClosedImmersion.lift (pullback.fst p (resMap ϖ)) (Yι I S) (by rw [ker_Yι]; exact h)

@[reassoc (attr := simp)]
theorem toFibre_fst (S : Finset ι) (h : fibreIdeal p ϖ ≤ ideal I S) :
    toFibre I p ϖ S h ≫ pullback.fst p (resMap ϖ) = Yι I S :=
  IsClosedImmersion.lift_fac _ _ _

theorem fibreIdeal_le_ideal {S : Finset ι} (hS : S.Nonempty) (h : ∀ i, fibreIdeal p ϖ ≤ I i) :
    fibreIdeal p ϖ ≤ ideal I S := by
  obtain ⟨i, hi⟩ := hS
  exact (h i).trans (le_ideal I hi)

@[reassoc (attr := simp)]
theorem incl_toFibre {S S' : Finset ι} (hSS : S ⊆ S') (h : fibreIdeal p ϖ ≤ ideal I S) :
    incl I hSS ≫ toFibre I p ϖ S h = toFibre I p ϖ S' (h.trans (ideal_mono I hSS)) :=
  (cancel_mono (pullback.fst p (resMap ϖ))).1 (by simp)

def toRes (S : Finset ι) (h : fibreIdeal p ϖ ≤ ideal I S) :
    Y I S ⟶ Spec (CommRingCat.of (O ⧸ Ideal.span {ϖ})) :=
  toFibre I p ϖ S h ≫ pullback.snd p (resMap ϖ)

theorem prod_le (i : ι) [Fintype ι] [DecidableEq ι] : ∏ j, I j ≤ I i := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact mul_le_of_le_one_right bot_le le_top

theorem fibreIdeal_le_of_prod [Fintype ι] (h : ∏ j, I j = fibreIdeal p ϖ) (i : ι) :
    fibreIdeal p ϖ ≤ ideal I {i} := by
  classical
  rw [ideal_singleton, ← h]; exact prod_le I i

def IsComponents [Fintype ι] : Prop :=
  ∃ h : ∏ j, I j = fibreIdeal p ϖ, ∀ i, Smooth (toRes I p ϖ {i} (fibreIdeal_le_of_prod I p ϖ h i))

end Fibre

section BaseChange

variable {X' : Scheme.{0}} (f : X' ⟶ X)

def pull : ι → X'.IdealSheafData := fun i => (I i).comap f

theorem ideal_pull (S : Finset ι) : ideal (pull I f) S = (ideal I S).comap f := by
  unfold ideal pull
  exact ((Scheme.IdealSheafData.map_gc f).l_iSup₂).symm

def isoOfEq {J J' : X.IdealSheafData} (e : J = J') : J.subscheme ≅ J'.subscheme where
  hom := Scheme.IdealSheafData.inclusion e.ge
  inv := Scheme.IdealSheafData.inclusion e.le
  hom_inv_id := by simp
  inv_hom_id := by simp

def pullIso (S : Finset ι) : Y (pull I f) S ≅ pullback f (Yι I S) :=
  isoOfEq (ideal_pull I f S) ≪≫ Scheme.IdealSheafData.comapIso (ideal I S) f

@[reassoc (attr := simp)]
theorem pullIso_hom_fst (S : Finset ι) : (pullIso I f S).hom ≫ pullback.fst _ _ = Yι (pull I f) S := by
  change (isoOfEq (ideal_pull I f S)).hom ≫ (Scheme.IdealSheafData.comapIso (ideal I S) f).hom ≫ pullback.fst _ _ = _
  rw [Scheme.IdealSheafData.comapIso_hom_fst]
  exact Scheme.IdealSheafData.inclusion_subschemeι _

def pullMap (S : Finset ι) : Y (pull I f) S ⟶ Y I S := (pullIso I f S).hom ≫ pullback.snd _ _

@[reassoc (attr := simp)]
theorem pullMap_Yι (S : Finset ι) : pullMap I f S ≫ Yι I S = Yι (pull I f) S ≫ f := by
  simp [pullMap, ← pullback.condition]

end BaseChange

theorem nonempty_Ystr {s : ℕ} (S : Idx ι s) (y : Y I S.1) : Nonempty (Ystr I s) := ⟨(inj I S).base y⟩

theorem isEmpty_Ystr {s : ℕ} (h : IsEmpty (Idx ι s)) : IsEmpty (Ystr I s) :=
  ⟨fun x => IsEmpty.false ((Sigma.desc (fun S : Idx ι s => (isEmptyElim S : Y I S.1 ⟶ ∅)) : Ystr I s ⟶ ∅).base x)⟩

theorem nonempty_Y_iff (S : Finset ι) : Nonempty (Y I S) ↔ ((ideal I S).support : Set X).Nonempty := by
  rw [← Set.range_nonempty_iff_nonempty (f := (Yι I S).base)]
  unfold Yι
  rw [← Scheme.IdealSheafData.range_subschemeι]
  rfl

end GlobalTheory.Strata

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

section FibreStr

variable {O : Type} [CommRing O] (p : X ⟶ Spec (CommRingCat.of O)) (ϖ : O)

def YstrToFibre (h : ∀ i, fibreIdeal p ϖ ≤ I i) (s : ℕ) : Ystr I s ⟶ fibre p ϖ :=
  Sigma.desc fun S : Idx ι s =>
    toFibre I p ϖ S.1 (fibreIdeal_le_ideal I p ϖ (Finset.card_pos.1 (by rw [S.2]; omega)) h)

@[reassoc (attr := simp)]
theorem inj_YstrToFibre (h : ∀ i, fibreIdeal p ϖ ≤ I i) {s : ℕ} (S : Idx ι s) :
    inj I S ≫ YstrToFibre I p ϖ h s =
      toFibre I p ϖ S.1 (fibreIdeal_le_ideal I p ϖ (Finset.card_pos.1 (by rw [S.2]; omega)) h) :=
  Sigma.ι_desc _ _

@[reassoc (attr := simp)]
theorem YstrToFibre_fst (h : ∀ i, fibreIdeal p ϖ ≤ I i) (s : ℕ) :
    YstrToFibre I p ϖ h s ≫ pullback.fst p (resMap ϖ) = Ystrπ I s :=
  Ystr_hom_ext I fun S => by simp

@[reassoc (attr := simp)]
theorem δ_YstrToFibre [LinearOrder ι] (h : ∀ i, fibreIdeal p ϖ ≤ I i) (s : ℕ) (j : Fin (s + 2)) :
    δ I s j ≫ YstrToFibre I p ϖ h s = YstrToFibre I p ϖ h (s + 1) :=
  (cancel_mono (pullback.fst p (resMap ϖ))).1 (by simp)

end FibreStr

section BaseChangeStr

variable {X' : Scheme.{0}} (f : X' ⟶ X)

@[reassoc (attr := simp)]
theorem incl_pullMap {S S' : Finset ι} (h : S ⊆ S') :
    incl (pull I f) h ≫ pullMap I f S = pullMap I f S' ≫ incl I h :=
  (cancel_mono (Yι I S)).1 (by simp)

def pullStr (s : ℕ) : Ystr (pull I f) s ⟶ Ystr I s :=
  Sigma.desc fun S : Idx ι s => pullMap I f S.1 ≫ inj I S

@[reassoc (attr := simp)]
theorem inj_pullStr {s : ℕ} (S : Idx ι s) : inj (pull I f) S ≫ pullStr I f s = pullMap I f S.1 ≫ inj I S :=
  Sigma.ι_desc _ _

@[reassoc (attr := simp)]
theorem pullStr_Ystrπ (s : ℕ) : pullStr I f s ≫ Ystrπ I s = Ystrπ (pull I f) s ≫ f :=
  Ystr_hom_ext _ fun S => by simp

@[reassoc]
theorem δ_pullStr [LinearOrder ι] (s : ℕ) (j : Fin (s + 2)) :
    δ (pull I f) s j ≫ pullStr I f s = pullStr I f (s + 1) ≫ δ I s j :=
  Ystr_hom_ext _ fun S => by
    simp only [inj_δ_assoc, inj_pullStr_assoc, Category.assoc]
    rw [inj_pullStr, incl_pullMap_assoc, inj_δ]

end BaseChangeStr

end GlobalTheory.Strata

namespace GlobalTheory.Strata.Example

open MvPolynomial

variable (O : Type) [CommRing O] (ϖ : O)

abbrev A : Type := MvPolynomial (Fin 2) O ⧸ Ideal.span {X 0 * X 1 - C ϖ}

def T (k : Fin 2) : A O ϖ := Ideal.Quotient.mk _ (X k)

abbrev XS : Scheme.{0} := Spec (CommRingCat.of (A O ϖ))

def str : XS O ϖ ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O (A O ϖ)))

def compIdeal (k : Fin 2) : (XS O ϖ).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of (A O ϖ))).inv.hom (T O ϖ k)})

def red : A O ϖ →+* O ⧸ Ideal.span {ϖ} :=
  Ideal.Quotient.lift _ (eval₂Hom (Ideal.Quotient.mk _) (fun _ => 0)) (by
    intro a ha
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self])

theorem reduction_uniformizerPoint (k : Fin 2) : red O ϖ (T O ϖ k) = 0 := by simp [red, T]

theorem mem_support_compIdeal (x : XS O ϖ) (k : Fin 2) (hx : T O ϖ k ∈ x.asIdeal) :
    x ∈ ((compIdeal O ϖ k).support : Set (XS O ϖ)) := by
  rw [compIdeal, Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton,
    basicOpen_eq_of_affine]
  exact fun h' => (PrimeSpectrum.mem_basicOpen (x := (x : PrimeSpectrum (A O ϖ))) _).1 h' hx

theorem isEmpty_Ystr_two : IsEmpty (Ystr (compIdeal O ϖ) 2) :=
  isEmpty_Ystr _ ⟨fun S => by have := S.1.card_le_univ; have h2 := S.2; simp at this; omega⟩

theorem nonempty_Ystr_one (h : ¬ IsUnit ϖ) : Nonempty (Ystr (compIdeal O ϖ) 1) := by
  haveI : Nontrivial (O ⧸ Ideal.span {ϖ}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (O ⧸ Ideal.span {ϖ})
  let x : XS O ϖ := ⟨M.comap (red O ϖ), Ideal.comap_isPrime _ _⟩
  have hx : x ∈ ((ideal (compIdeal O ϖ) Finset.univ).support : Set (XS O ϖ)) := by
    simp only [ideal, Scheme.IdealSheafData.support_iSup, TopologicalSpace.Closeds.coe_iInf, Set.mem_iInter]
    intro k _
    refine mem_support_compIdeal O ϖ x k ?_
    show red O ϖ (T O ϖ k) ∈ M
    rw [reduction_uniformizerPoint]; exact zero_mem _
  obtain ⟨y⟩ := (nonempty_Y_iff (compIdeal O ϖ) Finset.univ).2 ⟨x, hx⟩
  exact nonempty_Ystr (compIdeal O ϖ) (s := 1) ⟨Finset.univ, by simp⟩ y

example : Nonempty (Ystr (compIdeal ℤ 2) 1) ∧ IsEmpty (Ystr (compIdeal ℤ 2) 2) :=
  ⟨nonempty_Ystr_one ℤ 2 (by decide), isEmpty_Ystr_two ℤ 2⟩

end GlobalTheory.Strata.Example

namespace GlobalTheory.Strata

theorem orderEmbOfFin_univ_fin {n : ℕ} (h : (Finset.univ : Finset (Fin n)).card = n) :
    ((Finset.univ : Finset (Fin n)).orderEmbOfFin h : Fin n → Fin n) = id :=
  (Finset.orderEmbOfFin_unique h (f := id) (fun _ => Finset.mem_univ _) strictMono_id).symm

example : (face (ι := Fin 2) (s := 0) ⟨Finset.univ, by simp⟩ 0).1 = {1} ∧
    (face (ι := Fin 2) (s := 0) ⟨Finset.univ, by simp⟩ 1).1 = {0} := by
  simp only [face, orderEmbOfFin_univ_fin, id]
  decide

end GlobalTheory.Strata
