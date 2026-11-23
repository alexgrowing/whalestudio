import Development.EtaleCohomology.EtaleSheaves.HensCut

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.PartDiagCut

structure Part (A : Type) [CommRing A] : Type where

  blocks : Finset A
  idem : ∀ e ∈ blocks, IsIdempotentElem e ∧ e ≠ 0
  orth : ∀ e ∈ blocks, ∀ e' ∈ blocks, e ≠ e' → e * e' = 0
  sum_eq : ∑ e ∈ blocks, e = 1

instance (A : Type) [CommRing A] : Preorder (Part A) where
  le P Q := ∀ e' ∈ Q.1, ∃ e ∈ P.1, e' * e = e'
  le_refl P := fun e he => ⟨e, he, (P.idem e he).1.eq⟩
  le_trans P Q R hPQ hQR := fun e'' he'' => by
    obtain ⟨e', he', h1⟩ := hQR e'' he''
    obtain ⟨e, he, h2⟩ := hPQ e' he'
    exact ⟨e, he, by rw [← h1, mul_assoc, h2]⟩

variable {B : Type} [CommRing B]

def S (I : Ideal B) (e : B ⧸ I) : Submonoid B where
  carrier := {s | ∃ t, Ideal.Quotient.mk I s * t * e = e}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨t, ht⟩ ⟨u, hu⟩
    refine ⟨t * u, ?_⟩
    show Ideal.Quotient.mk I (a * b) * (t * u) * e = e
    rw [map_mul]
    calc _ = Ideal.Quotient.mk I a * t * (Ideal.Quotient.mk I b * u * e) := by ring
      _ = e := by rw [hu, ht]

theorem S_mono (I : Ideal B) {e e' : B ⧸ I} (h : e' * e = e') : S I e ≤ S I e' := by
  rintro s ⟨t, ht⟩
  refine ⟨t, ?_⟩
  calc Ideal.Quotient.mk I s * t * e' = Ideal.Quotient.mk I s * t * (e' * e) := by rw [h]
    _ = e' * (Ideal.Quotient.mk I s * t * e) := by ring
    _ = e' := by rw [ht, h]

abbrev PiLocalization₂ (I : Ideal B) (P : Part (B ⧸ I)) : Type := ∀ e : P.1, Localization (S I e.1)

def par {A : Type} [CommRing A] {P Q : Part A} (h : P ≤ Q) (e : Q.1) : P.1 :=
  ⟨Classical.choose (h e.1 e.2), (Classical.choose_spec (h e.1 e.2)).1⟩

theorem par_spec {A : Type} [CommRing A] {P Q : Part A} (h : P ≤ Q) (e : Q.1) : e.1 * (par h e).1 = e.1 :=
  (Classical.choose_spec (h e.1 e.2)).2

def stageMap (I : Ideal B) {P Q : Part (B ⧸ I)} (h : P ≤ Q) : PiLocalization₂ I P →+* PiLocalization₂ I Q :=
  RingHom.pi fun e => (IsLocalization.map (M := S I (par h e).1) (T := S I e.1) (Localization (S I e.1)) (RingHom.id B)
    (S_mono I (par_spec h e)) : Localization (S I (par h e).1) →+* _).comp (Pi.evalRingHom _ (par h e))

def βP (I : Ideal B) (P : Part (B ⧸ I)) : B →+* PiLocalization₂ I P :=
  RingHom.pi fun e => algebraMap B (Localization (S I e.1))

def DiagId : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : Part (B ⧸ I)) (h : P ≤ P),
  stageMap I h = RingHom.id (PiLocalization₂ I P)

def DiagComp : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P Q R : Part (B ⧸ I)) (h1 : P ≤ Q) (h2 : Q ≤ R),
  stageMap I (h1.trans h2) = (stageMap I h2).comp (stageMap I h1)

def DiagNat : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P Q : Part (B ⧸ I)) (h : P ≤ Q),
  (stageMap I h).comp (βP I P) = βP I Q

def PartDirected : Prop := ∀ (A : Type) [CommRing A], IsDirected (Part A) (· ≤ ·) ∧ Nonempty (Part A)

def StageProd : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∀ P : Part (B ⧸ I), ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
    (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (PiLocalization₂ I P ≃+* ∀ k, R k)

def PartA : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : Part (B ⧸ I)),
  Function.Bijective (Ideal.quotientMap (I.map (βP I P)) (βP I P) Ideal.le_comap_map)

def PartB : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : Part (B ⧸ I)) (x : PiLocalization₂ I P),
  x ∈ I.map (βP I P) → IsUnit (1 + x)

def PartC : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B →
  ∀ (P : Part (B ⧸ I)) (p : Polynomial (PiLocalization₂ I P)) (a₀ : PiLocalization₂ I P), p.Monic → p.eval a₀ ∈ I.map (βP I P) →
    IsUnit (Ideal.Quotient.mk (I.map (βP I P)) (p.derivative.eval a₀)) →
    ∃ (Q : Part (B ⧸ I)) (h : P ≤ Q) (a : PiLocalization₂ I Q), (p.map (stageMap I h)).IsRoot a ∧
      a - stageMap I h a₀ ∈ I.map (βP I Q)

def diag (I : Ideal B) (hid : DiagId) (hcomp : DiagComp) : Part (B ⧸ I) ⥤ CommRingCat.{0} where
  obj P := CommRingCat.of (PiLocalization₂ I P)
  map f := CommRingCat.ofHom (stageMap I (leOfHom f))
  map_id P := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_id, CommRingCat.hom_ofHom]
    exact hid B I P _
  map_comp f g := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    exact hcomp B I _ _ _ _ _

def diagβ (I : Ideal B) (hid : DiagId) (hcomp : DiagComp) (hnat : DiagNat) :
    (Functor.const _).obj (CommRingCat.of B) ⟶ diag I hid hcomp where
  app P := CommRingCat.ofHom (βP I P)
  naturality P Q f := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x => ?_
    change βP I Q x = stageMap I (leOfHom f) (βP I P x)
    rw [← RingHom.comp_apply, hnat]

theorem goal_of (hdir : PartDirected) (hid : DiagId) (hcomp : DiagComp) (hnat : DiagNat) (hprod : StageProd)
    (ha : PartA) (hb : PartB) (hc : PartC) : LateralTheory.E.HensCut.PartDiag := by
  intro q B _ _ I hB hq
  have := (hdir (B ⧸ I)).1
  have := (hdir (B ⧸ I)).2
  refine ⟨Part (B ⧸ I), inferInstance, inferInstance, diag I hid hcomp, diagβ I hid hcomp hnat, ?_, ?_, ?_, ?_⟩
  · intro P; exact hprod q B I hB hq P
  · intro P; exact ha B I P
  · intro P x hx
    refine ⟨P, 𝟙 P, ?_⟩
    rw [(diag I hid hcomp).map_id, CommRingCat.hom_id]
    exact hb B I P x hx
  · intro P p a₀ hp h1 h2
    obtain ⟨Q, h, a, h3, h4⟩ := hc B I hB P p a₀ hp h1 h2
    exact ⟨Q, homOfLE h, a, h3, h4⟩

end LateralTheory.E.PartDiagCut
