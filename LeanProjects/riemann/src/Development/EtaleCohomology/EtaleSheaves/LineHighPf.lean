import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.LineHighPf

open LateralTheory.E.t_E2Cut

def QAIC (q : ℕ) (W : Scheme.{0}) : Prop :=
  ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (I : Ideal B), AIC B ∧ IsUnit (q : B) ∧
    Nonempty (W ≅ Spec (CommRingCat.of (B ⧸ I)))

def Cover2 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z →
  ∃ (U V : Scheme.{0}) (f : U ⟶ pullback p (cpt A)) (g : V ⟶ pullback p (cpt A)),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    QAIC q U ∧ QAIC q V ∧ QAIC q (pullback f g)

theorem acyc_of_iso {q : ℕ} {W W' : Scheme.{0}} (e : W ≅ W') (h : Acyc q (sch.obj W')) : Acyc q (sch.obj W) := by
  intro n i hn
  have := h n i hn
  refine ⟨fun x y => ?_⟩
  have hs : ∀ z : Ht q (sch.obj W) n i,
      pull _ (sch.map e.hom) (tw q i) n (pull _ (sch.map e.inv) (tw q i) n z) = z := by
    intro z
    rw [← pull_comp, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [← hs x, ← hs y, Subsingleton.elim (pull _ (sch.map e.inv) (tw q i) n x) (pull _ (sch.map e.inv) (tw q i) n y)]

theorem acyc_of_QAIC (H : Hyp) (hQ : QuotAcyc) {q : ℕ} {W : Scheme.{0}} (h : QAIC q W) : Acyc q (sch.obj W) := by
  obtain ⟨B, _, _, I, hB, hq, ⟨e⟩⟩ := h
  exact acyc_of_iso e (hQ H q B I hB hq)

theorem high_of_cover (H : Hyp) (hM : MV) {q : ℕ} {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
    [IsOpenImmersion g] (hc : Set.range f ∪ Set.range g = Set.univ) (hU : Acyc q (sch.obj U)) (hV : Acyc q (sch.obj V))
    (hW : Acyc q (sch.obj (pullback f g))) (i n : ℤ) (hn : 2 ≤ n) : Subsingleton (Ht q (sch.obj X) n i) := by
  obtain ⟨δ, hδ, -⟩ := hM H (ZMod q) (tw q i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have key : ∀ x : Ht q (sch.obj X) (m + 1) i, x = 0 := by
    intro x
    have h3 := ((hδ f g hc m).2.2 x).1
    have := hU (m + 1) i (by omega)
    have := hV (m + 1) i (by omega)
    have := hW m i (by omega)
    obtain ⟨w, hw⟩ := h3 ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem LineHigh_of (hQ : QuotAcyc) (hM : MV) (hC : Cover2) : LineHigh := by
  intro H q i A _ _ hq Z p hp hZ n hn
  obtain ⟨U, V, f, g, hf, hg, hc, hU, hV, hW⟩ := hC q A hq p hp hZ
  exact high_of_cover H hM f g hc (acyc_of_QAIC H hQ hU) (acyc_of_QAIC H hQ hV) (acyc_of_QAIC H hQ hW) i n hn

theorem fibre_affine (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] :
    Nonempty (pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (cpt A) ≅
      Spec (CommRingCat.of (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)))) := by
  refine ⟨pullbackSpecIso A B (IsLocalRing.ResidueField A) ≪≫ ?_⟩
  exact Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal A)).toRingEquiv).op

def Good {A : Type} [CommRing A] {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A)) : Prop :=
  IsEmpty W ∨ ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B), AIC B ∧
    ∃ e : W ≅ Spec (CommRingCat.of B), e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = w

def ZCov : Prop := ∀ (A : Type) [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z →
  ∃ (U V : Scheme.{0}) (f : U ⟶ Z) (g : V ⟶ Z), IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    Good (f ≫ p) ∧ Good (g ≫ p) ∧ Good (pullback.fst f g ≫ f ≫ p)

def FibCov : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), AICSch Z → ∀ {U V : Scheme.{0}} (f : U ⟶ Z) (g : V ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g],
  Set.range f ∪ Set.range g = Set.univ → Good (f ≫ p) → Good (g ≫ p) → Good (pullback.fst f g ≫ f ≫ p) →
  ∃ (U V : Scheme.{0}) (f : U ⟶ pullback p (cpt A)) (g : V ⟶ pullback p (cpt A)),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    QAIC q U ∧ QAIC q V ∧ QAIC q (pullback f g)

theorem Cover2_of (hZ : ZCov) (hF : FibCov) : Cover2 := by
  intro q A _ _ hq Z p hp hZA
  obtain ⟨U, V, f, g, hf, hg, hc, h1, h2, h3⟩ := hZ A p hp hZA
  exact hF q A hq p hZA f g hc h1 h2 h3

end LateralTheory.E.LineHighPf
