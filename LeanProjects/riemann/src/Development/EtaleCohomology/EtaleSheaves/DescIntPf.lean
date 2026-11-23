import Development.EtaleCohomology.EtaleSheaves.StalkCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut

namespace LateralTheory.E.DescIntPf

def RelZS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {U E : Spc} (u : U ⟶ E) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R u F m)) ∧ Function.Injective (pull R u F n)

theorem relZ_iff (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    RelZ q i n f ↔ RelZS (ZMod q) (tw q i) n (sch.map (Spec.map f)) := Iff.rfl

theorem transfer (R : Type) [CommRing R] (F : Shv R) {U E X' X : Spc} (u : U ⟶ E) (f : X' ⟶ X) (a' : U ⟶ X')
    (a : E ⟶ X) (hsq : u ≫ a = a' ≫ f) (ha : Eqv R a F) (ha' : Eqv R a' F) (n : ℤ) (hu : RelZS R F n u) :
    RelZS R F n f := by
  have key : ∀ m (x : H R X F m), pull R a' F m (pull R f F m x) = pull R u F m (pull R a F m x) := by
    intro m x
    rw [← pull_comp, ← pull_comp, hsq]
  refine ⟨fun m hm y => ?_, fun x x' hxx => ?_⟩
  · obtain ⟨z, hz⟩ := hu.1 m hm (pull R a' F m y)
    obtain ⟨x, rfl⟩ := (ha m).2 z
    refine ⟨x, (ha' m).1 ?_⟩
    rw [key, hz]
  · have h1 := congrArg (pull R a' F n) hxx
    rw [key, key] at h1
    exact (ha n).1 (hu.2 h1)

theorem eqv_of_iso (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := fun n => by
  have h1 : ∀ x, pull R e.inv F n (pull R e.hom F n x) = x := fun x => by
    rw [← pull_comp, e.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R e.hom F n (pull R e.inv F n x) = x := fun x => by
    rw [← pull_comp, e.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem RelZS.of_iso (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (u : U ⟶ E) (u' : U' ⟶ E') (e₁ : U ≅ U')
    (e₂ : E ≅ E') (hsq : u ≫ e₂.hom = e₁.hom ≫ u') (n : ℤ) (hu : RelZS R F n u) : RelZS R F n u' :=
  transfer R F u u' e₁.hom e₂.hom hsq (eqv_of_iso R F e₂) (eqv_of_iso R F e₁) n hu

def EtaleRelativeIsoTruncationFromLevels : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (n : ℤ),
  (∀ (p : ℕ) (m : ℤ), m < n → RelZS R F m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) →
  RelZS R F n (disc.map (u.app (Opposite.op (SimplexCategory.mk 0)))) → RelZS R F n u

def CechSq : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → g.hom.IsIntegral → SpS g →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' →
  ∃ (U E : Spc) (u : U ⟶ E) (a' : U ⟶ sch.obj (Spec Y')) (a : E ⟶ sch.obj (Spec C)),
    u ≫ a = a' ≫ sch.map (Spec.map φ') ∧ Eqv _ a (tw q i) ∧ Eqv _ a' (tw q i) ∧
    (∀ p : ℕ, ∃ (L : CommRingCat.{0}) (l : A ⟶ L) (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : L ⟶ Z),
      P L l ∧ IsPushout φ l wz ψ ∧
      ∀ m, RelZ q i m ψ → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) ∧
    ∃ (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : D ⟶ Z), IsPushout φ (c ≫ g) wz ψ ∧
      ∀ m, RelZ q i m ψ → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk 0))))

theorem DescInt_of (hT : EtaleRelativeIsoTruncationFromLevels) (hC : CechSq) : LateralTheory.E.StalkCut.DescInt := by
  intro hH q _ i n A Y φ hq P hpush hbelow C D c g hCc hDc hgi hgs hDn Y' w φ' hpo
  obtain ⟨U, E, u, a', a, hsq, ha, ha', hlev, Z, wz, ψ, hpo0, h0⟩ :=
    hC hH q i φ hq P @hpush c g hCc hDc hgi hgs Y' w φ' hpo
  rw [relZ_iff]
  refine transfer _ _ u _ a' a hsq ha ha' n (hT _ _ u n (fun p m hm => ?_) (h0 n (hDn Z wz ψ hpo0)))
  obtain ⟨L, l, Z', wz', ψ', hL, hpo', hrel⟩ := hlev p
  exact hrel m (hbelow m hm L l hL Z' wz' ψ' hpo')

end LateralTheory.E.DescIntPf
