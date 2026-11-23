import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP

def LeafFive : Prop := ∀ δ, IsBd δ → ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), Mono P'.hom → Mono P.hom →
  (∀ i, Eqv _ φ.left (tw q i)) → (∀ i, Eqv _ φ.right (tw q i)) → Exc q φ

def LeafChartFact : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
  (I : Ideal (MvPolynomial (Fin d) R)), Ideal.span (Set.range MvPolynomial.X) = I → IsUnit (q : R) →
  ∀ Φ : opn (off (MvPolynomial (Fin d) R) I) ⟶ pr d R,
  Φ.right = (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
    sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) →
  ∃ (P : Arrow Spc) (α : opn (off (MvPolynomial (Fin d) R) I) ⟶ P) (β : P ⟶ pr d R), α ≫ β = Φ ∧
    Mono (opn (off (MvPolynomial (Fin d) R) I)).hom ∧ Mono P.hom ∧
    (∀ i, Eqv _ α.left (tw q i)) ∧ (∀ i, Eqv _ α.right (tw q i)) ∧
    IsPullback P.hom β.left β.right (pr d R).hom ∧ Cover2 (ZMod q) β.right (pr d R).hom

theorem dbl_hom_ext {P : Arrow Spc} {X : Spc} {f g : dbl P ⟶ X} (h0 : dbl.inl P ≫ f = dbl.inl P ≫ g)
    (h1 : dbl.inr P ≫ f = dbl.inr P ≫ g) : f = g := pushout.hom_ext h0 h1

theorem dbl_map_comp {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) :
    dbl.map (α ≫ β) = dbl.map α ≫ dbl.map β := by
  apply dbl_hom_ext
  · rw [inl_map, ← Category.assoc, inl_map, Category.assoc, inl_map, Arrow.comp_right, Category.assoc]
  · rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, Arrow.comp_right, Category.assoc]

theorem pull_comp_apply (q : ℕ) {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (α ≫ β) n i x = Hs.pull q α n i (Hs.pull q β n i x) := by
  apply Subtype.ext
  change GlobalTheory.EtC.pull _ (dbl.map (α ≫ β)) _ n x.1 = GlobalTheory.EtC.pull _ (dbl.map α) _ n (GlobalTheory.EtC.pull _ (dbl.map β) _ n x.1)
  rw [dbl_map_comp, pull_comp]

theorem exc_comp (q : ℕ) {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) (hα : Exc q α) (hβ : Exc q β) :
    Exc q (α ≫ β) := fun n i => by
  have : (Hs.pull q (α ≫ β) n i : Hs q P n i → Hs q P'' n i) = Hs.pull q α n i ∘ Hs.pull q β n i :=
    funext (pull_comp_apply q α β n i)
  rw [this]
  exact (hα n i).comp (hβ n i)

theorem fgt_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = GlobalTheory.EtC.pull _ φ.right _ n (Hs.fgt q P n i x) := by
  change GlobalTheory.EtC.pull _ (dbl.inl P') _ n (GlobalTheory.EtC.pull _ (dbl.map φ) _ n x.1) =
    GlobalTheory.EtC.pull _ φ.right _ n (GlobalTheory.EtC.pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, inl_map, pull_comp]

theorem res_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (c : Ht q P.right n i) :
    GlobalTheory.EtC.pull _ P'.hom (tw q i) n (GlobalTheory.EtC.pull _ φ.right _ n c) =
      GlobalTheory.EtC.pull _ φ.left _ n (GlobalTheory.EtC.pull _ P.hom (tw q i) n c) := by
  rw [← pull_comp, ← pull_comp, Arrow.w φ]

theorem five (δ : ∀ (q : ℕ) (P : Arrow Spc) (n i : ℤ), Ht q P.left n i →+ Hs q P (n + 1) i) (hδ : IsBd δ)
    (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (h' : Mono P'.hom) (h : Mono P.hom)
    (hl : ∀ i, Eqv _ φ.left (tw q i)) (hr : ∀ i, Eqv _ φ.right (tw q i)) (m i : ℤ) :
    Function.Bijective (Hs.pull q φ (m + 1) i) := by
  obtain ⟨hex, hnat, -⟩ := hδ
  obtain ⟨-, e2, e3⟩ := hex q P h m i
  obtain ⟨-, e2', e3'⟩ := hex q P' h' m i
  obtain ⟨e1, -, -⟩ := hex q P h (m + 1) i
  obtain ⟨e1', -, -⟩ := hex q P' h' (m + 1) i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hf : Hs.fgt q P (m + 1) i x = 0 := by
      apply (hr i (m + 1)).1
      rw [← fgt_pull, hx, map_zero, map_zero]
    obtain ⟨u, rfl⟩ := (e3 x).1 hf
    have hu : δ q P' m i (GlobalTheory.EtC.pull _ φ.left _ m u) = 0 := by rw [← hnat q P' P φ h' h m i u]; exact hx
    obtain ⟨w', hw'⟩ := (e2' _).1 hu
    obtain ⟨w, rfl⟩ := (hr i m).2 w'
    rw [res_pull] at hw'
    have := (hl i m).1 hw'
    rw [← this]
    exact (e2 _).2 ⟨w, rfl⟩
  · intro y
    obtain ⟨c, hc⟩ := (hr i (m + 1)).2 (Hs.fgt q P' (m + 1) i y)
    have hc0 : GlobalTheory.EtC.pull _ P.hom (tw q i) (m + 1) c = 0 := by
      apply (hl i (m + 1)).1
      rw [← res_pull, hc, map_zero]
      exact (e1' _).2 ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := (e1 c).1 hc0
    have hd : Hs.fgt q P' (m + 1) i (y - Hs.pull q φ (m + 1) i x) = 0 := by
      rw [map_sub, fgt_pull, hx, hc, sub_self]
    obtain ⟨u', hu'⟩ := (e3' _).1 hd
    obtain ⟨u, rfl⟩ := (hl i m).2 u'
    refine ⟨x + δ q P m i u, ?_⟩
    rw [map_add, hnat q P' P φ h' h m i u, hu', add_sub_cancel]

theorem leafFive : LeafFive := by
  intro δ hδ q P' P φ h' h hl hr n i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact five δ hδ q φ h' h hl hr m i

end LateralTheory.CohomologicalPurity.Thom.ExcP

namespace LateralTheory.CohomologicalPurity.Thom

theorem excision_of_thom_chart_factorization (hBd : LeafBd) (hSp : LeafExcSp) (hFact : ExcP.LeafChartFact) :
    LeafExcP := by
  intro hH q _ d R _ I hI hq Φ hΦ
  obtain ⟨δ, hδ⟩ := hBd
  obtain ⟨P, α, β, hαβ, hm1, hm2, hl, hr, hpb, hcov⟩ := hFact hH q d R I hI hq Φ hΦ
  rw [← hαβ]
  exact ExcP.exc_comp q α β (ExcP.leafFive δ hδ q α hm1 hm2 hl hr) (hSp hH.1 q β hpb hcov)

end LateralTheory.CohomologicalPurity.Thom
