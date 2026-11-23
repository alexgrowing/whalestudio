import Mathlib
import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

private theorem conn_neg (a9 : A9) {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) :
    Conn R f F (-1) := by
  have hs := (a9 R F).1
  refine ⟨fun j hj => ?_, ?_⟩
  · haveI := hs E j (by omega)
    haveI := hs E' j (by omega)
    exact ⟨Function.injective_of_subsingleton _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · haveI := hs E' (-1) (by omega)
    exact Function.injective_of_subsingleton _

private theorem conn_level {R : Type} [CommRing R] {P P' Q Q' : PSh} {f : P ⟶ P'} {g : Q ⟶ Q'}
    (e : Arrow.mk f ≅ Arrow.mk g) (F : Shv R) (n : ℤ) :
    Conn R (disc.map f) F n ↔ Conn R (disc.map g) F n := by
  obtain ⟨a, b, ha, hb, w⟩ := arr_w e
  exact conn_sq R w (eqv_iso R _ F) (eqv_iso R _ F) n

private theorem eqv_level {R : Type} [CommRing R] {P P' Q Q' : PSh} {f : P ⟶ P'} {g : Q ⟶ Q'}
    (e : Arrow.mk f ≅ Arrow.mk g) (F : Shv R) (h : Eqv R (disc.map g) F) : Eqv R (disc.map f) F := by
  obtain ⟨a, b, ha, hb, w⟩ := arr_w e
  exact fun n => ((sq R w (eqv_iso R _ F) (eqv_iso R _ F) n).1).2 (h n)

private theorem conn_all (a1 : A1) (a9 : A9) (b1 : B1) (b2 : B2) (b4 : B4) (hC : Cover) (hE : EqvQA)
    (hD : DescStep) (hL : CechLevels) (q : ℕ) [NeZero q] (i : ℤ) (m : ℕ) :
    ∀ (B : Type) [CommRing B] (J : Ideal B), IsUnit (q : B) →
      (∀ (C : Type) [CommRing C] (χ : B →+* C), χ.IsIntegral → Good C (J.map χ)) →
      Conn (ZMod q) (spMap (Ideal.Quotient.mk J)) (tw q i) ((m : ℤ) - 1) := by
  induction m with
  | zero =>
    intro B _ J _ _
    rw [Nat.cast_zero, zero_sub]
    exact conn_neg a9 _ _
  | succ m ih =>
    intro B _ J hq hG
    obtain ⟨A', _, φ, hφ, hsurj, hQA⟩ := hC B
    obtain ⟨⟨h1, h2, h3, h4⟩, ψ, hψ, hlev, h0⟩ := hL B A' φ J hφ hsurj
    have hψc : Conn (ZMod q) ψ (tw q i) ((m : ℤ) - 1 + 1) := by
      apply hD a1 (ZMod q) (tw q i) ψ ((m : ℤ) - 1)
      · intro p
        obtain ⟨C, _, χ, hχ, ⟨e⟩⟩ := hlev p
        rw [conn_level e]
        apply ih C (J.map χ) (by simpa using hq.map χ)
        intro C' _ χ' hχ'
        rw [Ideal.map_map]
        exact hG C' (χ'.comp χ) (RingHom.IsIntegral.trans _ _ hχ hχ')
      · obtain ⟨e⟩ := h0
        apply eqv_level e
        exact hE a1 a9 b1 b2 q A' (J.map φ) hQA (hG A' φ hφ) (by simpa using hq.map φ) i
    have hmm : ((m : ℤ) - 1 + 1) = ((m + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [hmm] at hψc
    have hqJ : IsUnit ((q : ℕ) : B ⧸ J) := by simpa using hq.map (Ideal.Quotient.mk J)
    have ea := @b4 q _ _ (Spec.map (CommRingCat.ofHom φ)) h1 h2 (unit_spec (A := B) hq) i
    have eb := @b4 q _ _ _ h3 h4 (unit_spec (A := B ⧸ J) hqJ) i
    exact (conn_sq (ZMod q) hψ eb ea _).1 hψc

theorem UpperTheory.etaleCohomology_descent_of_cech_cover :
    A1 → A9 → B1 → B2 → B4 → Cover → HensIdem → EqvQA → DescStep → CechLevels → E1 := by
  intro a1 a9 b1 b2 b4 hC hH hE hD hL q A _ I _ hq i
  by_cases hq0 : q = 0
  · subst hq0
    have h01 : (0 : A) = 1 := isUnit_zero_iff.mp (by simpa using hq)
    haveI : Subsingleton A := subsingleton_of_zero_eq_one h01
    have hb : Function.Bijective (Ideal.Quotient.mk I) :=
      ⟨fun x y _ => Subsingleton.elim x y, Ideal.Quotient.mk_surjective⟩
    haveI : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
      (RingEquiv.ofBijective (Ideal.Quotient.mk I) hb).toCommRingCatIso.isIso_hom
    exact eqv_iso _ _ _
  · haveI : NeZero q := ⟨hq0⟩
    intro n
    have hc := conn_all a1 a9 b1 b2 b4 hC hE hD hL q i (n.toNat + 2) A I hq
      (fun C _ χ hχ => hH A I C χ hχ)
    exact hc.1 n (by push_cast; omega)

end
