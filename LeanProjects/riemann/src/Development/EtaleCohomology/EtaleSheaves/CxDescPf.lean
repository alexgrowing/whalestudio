import Development.EtaleCohomology.EtaleSheaves.DescentInduction

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CxDescPf

abbrev tr {R : Type} [CommRing R] (K : Cx R) (N : ℕ) : Cx R :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE (-(N : ℤ)))

abbrev trm {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (N : ℕ) : tr K N ⟶ tr L N :=
  HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE (-(N : ℤ)))

def Good {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (I : Cx R) (m : ℤ) : Prop :=
  (∀ j : ℤ, j < m → Function.Bijective (cpull g I j)) ∧ Function.Injective (cpull g I m)

def stupid : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
  ((∀ j : ℤ, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j)) →
    ∀ j : ℤ, Function.Bijective (cpull (trm g 0) I j)) ∧
  ∀ (m : ℤ) (N : ℕ), m + 1 ≤ (N : ℤ) → Good (trm g N) I m → Good g I m

def long : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (m : ℤ) (N : ℕ),
  Good ((CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ)))) I m →
  Good (trm g N) I m → Good (trm g (N + 1)) I m

def shift : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) {A B : Shv R} (φ : A ⟶ B) (p : ℕ) (j : ℤ),
  (Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - p)) →
    Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map φ) I j)) ∧
  (Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - p)) →
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map φ) I j))

theorem CxDesc_of (hS : stupid) (hL : long) (hH : shift) : LateralTheory.E.DescStepPf.CxDesc := by
  intro R _ I _ hI K L _ _ g n hlow hn h0
  obtain ⟨hb, hlim⟩ := hS R I hI g
  have base : Good (trm g 0) I (n + 1) := ⟨fun j _ => hb h0 j, (hb h0 (n + 1)).1⟩
  have step : ∀ N : ℕ, Good (trm g N) I (n + 1) := by
    intro N
    induction N with
    | zero => exact base
    | succ N ih =>
      refine hL R I hI g (n + 1) N ⟨fun j hj => ?_, ?_⟩ ih
      · exact (hH R I (g.f (-((N + 1 : ℕ) : ℤ))) (N + 1) j).1 (hlow (N + 1) (j - ((N + 1 : ℕ) : ℤ)) (by omega))
      · apply (hH R I (g.f (-((N + 1 : ℕ) : ℤ))) (N + 1) (n + 1)).2
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h
          have e : n + 1 - ((0 + 1 : ℕ) : ℤ) = n := by omega
          rw [e]; exact hn (0 + 1)
        · exact (hlow (N + 1) _ (by omega)).1
  have hg := hlim (n + 1) (n + 2).toNat (by omega) (step _)
  exact ⟨hg.1, hg.2⟩

end LateralTheory.E.CxDescPf
