import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusModel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charVal_eq {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal t χ = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (GlobalTheory.splitTorusPointsEquiv S X (Over.mk a) t (Multiplicative.ofAdd χ)).val := by
  unfold charVal
  set g : Sp A ⟶ Spec (torusRing ZU X) := t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) with hg
  have h : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      = Spec.preimage g := by
    conv_lhs => rw [← Spec.map_preimage g]
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← h]
  rfl

theorem charVal_mul {A : Type} [CommRing A] {a : Sp A ⟶ S} (t t' : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal (t * t') χ = charVal t χ * charVal t' χ := by
  simp only [charVal_eq, map_mul, MonoidHom.mul_apply, Units.val_mul]

theorem charVal_one {A : Type} [CommRing A] {a : Sp A ⟶ S} (χ : X) :
    charVal (1 : Over.mk a ⟶ splitTorus S X) χ = 1 := by
  simp only [charVal_eq, map_one, MonoidHom.one_apply, Units.val_one]

theorem charVal_add {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ χ' : X) :
    charVal t (χ + χ') = charVal t χ * charVal t χ' := by
  simp only [charVal_eq, ofAdd_add, map_mul, Units.val_mul]

theorem charVal_zero {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) :
    charVal t 0 = 1 := by
  simp only [charVal_eq, ofAdd_zero, map_one, Units.val_one]

theorem charVal_ext {A : Type} [CommRing A] {a : Sp A ⟶ S} {t t' : Over.mk a ⟶ splitTorus S X}
    (h : ∀ χ, charVal t χ = charVal t' χ) : t = t' := by
  apply (GlobalTheory.splitTorusPointsEquiv S X (Over.mk a)).injective
  ext χ
  have := h χ
  rw [charVal_eq, charVal_eq] at this
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective this

theorem exists_charVal {A : Type} [CommRing A] (a : Sp A ⟶ S) (u : Multiplicative X →* Aˣ) :
    ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = (u (Multiplicative.ofAdd χ)).val := by
  refine ⟨(GlobalTheory.splitTorusPointsEquiv S X (Over.mk a)).symm
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom).comp u), fun χ => ?_⟩
  rw [charVal_eq, MulEquiv.apply_symm_apply]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _

theorem charVal_comp {A B : Type} [CommRing A] [CommRing B] {a : Sp A ⟶ S} {b : Sp B ⟶ S} (g : A →+* B)
    (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk b ⟶ splitTorus S X)
    (h : t'.left = spMap g ≫ t.left) (χ : X) : charVal t' χ = g (charVal t χ) := by
  unfold charVal
  have e : (t'.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp B ⟶ Spec (torusRing ZU X)) =
      Spec.map (CommRingCat.ofHom g) ≫
        (t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp A ⟶ Spec (torusRing ZU X)) := by
    rw [h]; exact Category.assoc _ _ _
  rw [e, Spec.preimage_comp, Spec.preimage_map]
  rfl

theorem left_eq_of_charVal {A B : Type} [CommRing A] [CommRing B] {a : Sp A ⟶ S} {b : Sp B ⟶ S} (g : A →+* B)
    (hg : spMap g ≫ a = b) (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk b ⟶ splitTorus S X)
    (h : ∀ χ, charVal t' χ = g (charVal t χ)) : t'.left = spMap g ≫ t.left := by
  let k : Over.mk b ⟶ Over.mk a := Over.homMk (spMap g) hg
  have : t' = k ≫ t := charVal_ext fun χ => by rw [h, charVal_comp g t (k ≫ t) rfl]
  rw [this]; rfl

def epsUnit {R : Type} [CommRing R] (δ : X →+ R) : Multiplicative X →* (DualNumber R)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun χ => TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ.toAdd)
      map_one' := by ext <;> simp
      map_mul' := fun a b => by ext <;> simp [add_comm] }

def tanPt {R : Type} [CommRing R] (x : Sp R ⟶ S) (δ : X →+ R) : epsAt x ⟶ splitTorus S X :=
  (exists_charVal _ (epsUnit δ)).choose

theorem charVal_tanPt {R : Type} [CommRing R] (x : Sp R ⟶ S) (δ : X →+ R) (χ : X) :
    charVal (tanPt x δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ) :=
  (exists_charVal _ (epsUnit δ)).choose_spec χ

theorem spMap_comp_eps {R A : Type} [CommRing R] [CommRing A] (x : Sp R ⟶ S) (g : DualNumber R →+* A)
    (f : R →+* A) (h : g.comp (algebraMap R (DualNumber R)) = f) :
    spMap g ≫ (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) = spMap f ≫ x := by
  rw [← Category.assoc, ← Spec.map_comp, ← h]; rfl

theorem fst_eps {R : Type} [CommRing R] (x : Sp R ⟶ S) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) = x := by
  rw [spMap_comp_eps x _ (RingHom.id R) (by ext; simp)]
  simp [spMap]

def lieModel {R : Type} [CommRing R] (x : Sp R ⟶ S) : LieModel (splitTorus S X) x (X →+ R) where
  pt := tanPt x
  tan δ := (left_eq_of_charVal _ (fst_eps x) (tanPt x δ) 1 fun χ => by
    rw [charVal_one, charVal_tanPt]; simp).symm
  inj δ δ' h := by
    ext χ
    have := congrArg (fun t => (charVal t χ).snd) h
    simpa [charVal_tanPt] using this
  onto v hv := by
    have h1 : ∀ χ, (charVal v χ).fst = 1 := fun χ => by
      have := charVal_comp (TrivSqZeroExt.fstHom R R R).toRingHom v (1 : Over.mk x ⟶ splitTorus S X)
        (Eq.symm hv) χ
      rw [charVal_one] at this
      exact this.symm
    refine ⟨AddMonoidHom.mk' (fun χ => (charVal v χ).snd) fun a b => ?_, charVal_ext fun χ => ?_⟩
    · simp [charVal_add, TrivSqZeroExt.snd_mul, h1, add_comm]
    · rw [charVal_tanPt]; ext <;> simp [h1]
  add δ δ' := charVal_ext fun χ => by
    rw [charVal_mul, charVal_tanPt, charVal_tanPt, charVal_tanPt]
    ext <;> simp [add_comm]
  smul c δ := left_eq_of_charVal (epsMul c)
    (spMap_comp_eps x _ _ (by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])) _ _ fun χ => by
      rw [charVal_tanPt, charVal_tanPt]
      ext <;> simp [epsMul, mul_comm]

theorem isCocharLie_lieModel {R : Type} [CommRing R] (x : Sp R ⟶ S) :
    IsCocharLie (lieModel (X := X) x) := charVal_tanPt x

theorem IsCocharLie.pt_eq {R : Type} [CommRing R] {x : Sp R ⟶ S} {M M' : LieModel (splitTorus S X) x (X →+ R)}
    (h : IsCocharLie M) (h' : IsCocharLie M') : M.pt = M'.pt :=
  funext fun δ => charVal_ext fun χ => (h δ χ).trans (h' δ χ).symm

theorem lifts_iff {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ S) (c : R →+* R') (δ : X →+ R)
    (δ' : X →+ R') :
    (lieModel x).Lifts c (𝟙 (splitTorus S X).left) δ (tanPt (spMap c ≫ x) δ') ↔ ∀ χ, δ' χ = c (δ χ) := by
  unfold LieModel.Lifts
  rw [Category.comp_id]
  constructor
  · intro h χ
    have := congrArg TrivSqZeroExt.snd (charVal_comp (dualMap c) (tanPt x δ) _ h χ)
    simpa [charVal_tanPt, dualMap] using this
  · intro h
    refine left_eq_of_charVal (dualMap c) ?_ (tanPt x δ) _ fun χ => ?_
    · rw [spMap_comp_eps x _ ((algebraMap R' (DualNumber R')).comp c)
        (by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]), ← Category.assoc, ← Spec.map_comp]
      rfl
    · rw [charVal_tanPt, charVal_tanPt]
      ext <;> simp [dualMap, h]

theorem killsOver_id_iff (Y : AddSubgroup X) {B : Type} [CommRing B] [Nontrivial B] (b : Sp B ⟶ S) :
    KillsOver (𝟙 (splitTorus S X)) Y b ↔ Y = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro χ _
    obtain ⟨t, ht⟩ := exists_charVal (X := X) (spMap (algebraMap B (AddMonoidAlgebra B (X ⧸ Y))) ≫ b)
      (MonoidHom.toHomUnits ((AddMonoidAlgebra.of B (X ⧸ Y)).comp
        (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Y))))
    have ht' : ∀ χ, charVal t χ = AddMonoidAlgebra.single (QuotientAddGroup.mk χ : X ⧸ Y) 1 := ht
    have h1 := h _ _ t fun y hy => by
      rw [ht', (QuotientAddGroup.eq_zero_iff y).2 hy]; rfl
    rw [Category.comp_id] at h1
    have h2 := ht' χ
    rw [h1, charVal_one, AddMonoidAlgebra.one_def] at h2
    exact (QuotientAddGroup.eq_zero_iff χ).1 (AddMonoidAlgebra.single_left_injective one_ne_zero h2).symm
  · rintro rfl A _ g t ht
    rw [Category.comp_id]
    exact charVal_ext fun χ => (ht χ trivial).trans (charVal_one χ).symm

theorem killsOver_sq {B : Type} [CommRing B] (b : Sp B ⟶ S) :
    KillsOver (𝟙 (splitTorus S X) * 𝟙 (splitTorus S X)) (nsmulAddMonoidHom (α := X) 2).range b := by
  intro A _ g t ht
  rw [MonObj.comp_mul, Category.comp_id]
  refine charVal_ext fun χ => ?_
  rw [charVal_mul, ← charVal_add, charVal_one]
  exact ht _ ⟨χ, two_nsmul χ⟩

theorem not_killsOver_mu_two (b : Sp (ZMod 2) ⟶ S) :
    ¬ KillsOver (𝟙 (splitTorus S ℤ)) (nsmulAddMonoidHom (α := ℤ) 2).range b := by
  rw [killsOver_id_iff]
  intro h
  obtain ⟨n, hn⟩ : (1 : ℤ) ∈ (nsmulAddMonoidHom (α := ℤ) 2).range := h ▸ trivial
  have : 2 * n = 1 := by simpa using hn
  omega

end GlobalTheory.CompanionTheory.Ar.TorusModel
