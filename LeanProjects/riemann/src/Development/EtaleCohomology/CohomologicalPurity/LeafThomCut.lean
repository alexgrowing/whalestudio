import Development.EtaleCohomology.CohomologicalPurity.LeafThomCutDef

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafGeo : Prop :=
  (∀ (d : ℕ) (R : Type) [CommRing R], Mono (pr d R).hom) ∧
  (∀ (q N k : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → Inv q (PR N k R)) ∧
  (∀ (d : ℕ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (x : Fin d → A),
    spMap φ ≫ Pj.pt (vec1 x) = Pj.pt (vec1 (φ ∘ x))) ∧
  ∀ (d : ℕ) (A : Type) [CommRing A] (I : Ideal A) (x : Fin d → A), Ideal.span (Set.range x) = I →
    ∃ Φ : opn (off A I) ⟶ pr d A, Φ.right = chart x

def LeafAct : Prop := ∀ (d : ℕ) (A : Type) [CommRing A] (M : Matrix (Fin d) (Fin d) A), IsUnit M.det →
  ∃ g : pr d A ⟶ pr d A,
    (g.right : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A) ≫ prod.fst ≫ Pj.line (d + 1) 0 = prod.fst ≫ Pj.line (d + 1) 0 ∧
    (g.right : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A) ≫ prod.snd = prod.snd ∧
    ∀ x : Fin d → A, chart x ≫ (g.right : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A) = chart (M.mulVec x)

def LeafPB : Prop := A1 → DivisorNaturality → D1 → ∀ (q : ℕ) [NeZero q] (N : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  ∀ n i : ℤ, Function.Bijective (poly q N 0 R N n i)

def LeafHtpy : Prop := A1 → A4 → C4 → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (I : Ideal A), I.FG → IsUnit (q : A) →
  ∀ (h : off (Polynomial A) (I.map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I) (i : ℤ),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i)

def LeafTail : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ i : ℤ,
  Eqv _ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R) (tw q i)

def LeafTau : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  (∃! τ, IsTau q d R τ) ∧ ∀ τ, IsTau q d R τ → ∀ n i : ℤ, Function.Bijective fun a : Ht q (sp R) n i =>
    Hs.act q (P := pr d R) (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _ a) τ

def LeafTauNat : Prop := DivisorNaturality → A11 → ∀ (q : ℕ) [NeZero q] (d : ℕ) (A : Type) [CommRing A], IsUnit (q : A) →
  ∀ τ, IsTau q d A τ →
  (∀ (B : Type) [CommRing B] (φ : A →+* B) (g : pr d B ⟶ pr d A),
    (g.right : PR (d + 1) 0 B ⟶ PR (d + 1) 0 A) ≫ prod.fst ≫ Pj.line (d + 1) 0 = prod.fst ≫ Pj.line (d + 1) 0 →
    (g.right : PR (d + 1) 0 B ⟶ PR (d + 1) 0 A) ≫ prod.snd = prod.snd ≫ spMap φ → IsTau q d B (Hs.pull q g _ _ τ)) ∧
  ∀ r : ℕ, r ∣ q → ∀ τ' : Hs r (pr d A) (2 * d) d, τ'.1 = red q r _ _ _ τ.1 → IsTau r d A τ'

def LeafExcSp : Prop := A1 → ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsPullback P'.hom φ.left φ.right P.hom →
  Cover2 (ZMod q) φ.right P.hom → Exc q φ

def LeafExcP : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)),
  Ideal.span (Set.range MvPolynomial.X) = I → IsUnit (q : R) → ∀ Φ : opn (off (MvPolynomial (Fin d) R) I) ⟶ pr d R,
  Φ.right = (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
    sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) → Exc q Φ

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P := pushout.inl_desc _ _ _

theorem inl_fold (P : Arrow Spc) : dbl.inl P ≫ dbl.fold P = 𝟙 _ := pushout.inl_desc _ _ _

theorem map_comp {P'' P' P : Arrow Spc} (ψ : P'' ⟶ P') (φ : P' ⟶ P) : dbl.map (ψ ≫ φ) = dbl.map ψ ≫ dbl.map φ := by
  refine pushout.hom_ext ?_ ?_
  · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
    rw [inl_map, ← Category.assoc, inl_map, Category.assoc, inl_map, Arrow.comp_right, Category.assoc]
  · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
    rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, Arrow.comp_right, Category.assoc]

theorem map_fold {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.map φ ≫ dbl.fold P = dbl.fold P' ≫ φ.right := by
  refine pushout.hom_ext ?_ ?_
  · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
    rw [← Category.assoc, inl_map, Category.assoc, inl_fold, ← Category.assoc, inl_fold, Category.comp_id, Category.id_comp]
  · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
    rw [← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_fold, ← Category.assoc, dbl.inr_fold, Category.comp_id,
      Category.id_comp]

theorem hs_comp (q : ℕ) {P'' P' P : Arrow Spc} (ψ : P'' ⟶ P') (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q ψ n i (Hs.pull q φ n i x) = Hs.pull q (ψ ≫ φ) n i x :=
  Subtype.ext (by
    change pull _ (dbl.map ψ) _ n (pull _ (dbl.map φ) _ n x.1) = pull _ (dbl.map (ψ ≫ φ)) _ n x.1
    rw [map_comp, pull_comp])

theorem hs_act (h : DivisorNaturality) (q : ℕ) [NeZero q] {P' P : Arrow Spc} (φ : P' ⟶ P) {n m i j : ℤ} (a : Ht q P.right n i)
    (b : Hs q P m j) : Hs.pull q φ _ _ (Hs.act q a b) = Hs.act q (pull _ φ.right _ _ a) (Hs.pull q φ _ _ b) :=
  Subtype.ext (by
    have e : cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ n a)) (pull _ (dbl.map φ) _ m b.1) =
        pull _ (dbl.map φ) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1) := by
      rw [(h q).1, ← pull_comp, ← pull_comp, map_fold]
    change pull _ (dbl.map φ) _ _ (_ - _) = cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ n a))
      (pull _ (dbl.map φ) _ m b.1) - pull _ (dbl.fold P') _ _ (pull _ (dbl.inr P') _ _
        (cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ n a)) (pull _ (dbl.map φ) _ m b.1)))
    rw [e, map_sub, ← pull_comp _ (dbl.inr P'), dbl.inr_map, pull_comp, ← pull_comp _ (dbl.fold P'), ← map_fold, pull_comp])

theorem hom_ext {P' P : Arrow Spc} (h : Mono P.hom) {φ ψ : P' ⟶ P} (e : φ.right = ψ.right) : φ = ψ := by
  refine Arrow.hom_ext _ _ ?_ e
  rw [← cancel_mono P.hom, Arrow.w, Arrow.w, e]

theorem goal_of (hG : LeafGeo) (hA : LeafAct) (hT : LeafTau) (hN : LeafTauNat) (hE : LeafExcP) : LeafThom := by
  intro H d
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have h11 : A11 := H.2.2.2.2.2.2.2.1
  obtain ⟨hm, -, hpt, hΦ⟩ := hG
  choose Φ hΦ using hΦ d
  let τ : ∀ (q : ℕ) (A : Type) [CommRing A], Hs q (pr d A) (2 * d) d := fun q A _ => pick (IsTau q d A)
  have hτ : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → IsTau q d A (τ q A) :=
    fun q _ A _ hq => pick_spec (hT H q d A hq).1.exists
  have huq : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → ∀ t, IsTau q d A t → t = τ q A :=
    fun q _ A _ hq t ht => (hT H q d A hq).1.unique ht (hτ q A hq)
  have hb : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), IsUnit (q : A) →
      Hs.pull q (prMap d φ) _ _ (τ q A) = τ q B := fun q _ A B _ _ φ hq =>
    huq q B (by simpa using hq.map φ) _ ((hN h6 h11 q d A hq _ (hτ q A hq)).1 B φ _
      ((prod.map_fst_assoc (𝟙 (Pj (d + 1) 0)) (spMap φ) (Pj.line (d + 1) 0)).trans
        (congrArg (fun f => prod.fst ≫ f) (Category.id_comp _)))
      (prod.map_snd _ _))
  refine ⟨fun q A _ I x hx => Hs.pull q (Φ A I x hx) _ _ (τ q A), fun q _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro A B _ _ φ I J x hx hy h hq
    have e : opnMap (Spec.map (CommRingCat.ofHom φ)) (off B J) (off A I) h ≫ Φ A I x hx = Φ B J _ hy ≫ prMap d φ := by
      refine hom_ext (hm d A) ?_
      rw [Arrow.comp_right, Arrow.comp_right, hΦ, hΦ]
      change spMap φ ≫ chart x = chart (φ ∘ x) ≫ prod.map (𝟙 _) (spMap φ)
      rw [chart, chart, prod.comp_lift, prod.lift_map, hpt, Category.comp_id, Category.comp_id, Category.id_comp]
    beta_reduce
    rw [hs_comp, e, ← hs_comp, hb q A B φ hq]
  · intro A _ I x M hx hy hq hM
    obtain ⟨g, g1, g2, g3⟩ := hA d A M hM
    have e : Φ A I _ hy = Φ A I x hx ≫ g := by
      refine hom_ext (hm d A) ?_
      rw [Arrow.comp_right, hΦ, hΦ]
      exact (g3 x).symm
    have e2 : Hs.pull q g _ _ (τ q A) = τ q A := huq q A hq _ ((hN h6 h11 q d A hq _ (hτ q A hq)).1 A (RingHom.id A) g g1
      (by
        have : spMap (RingHom.id A) = 𝟙 _ := by
          change sch.map (Spec.map (𝟙 _)) = _
          rw [Spec.map_id, CategoryTheory.Functor.map_id]
        rw [this, Category.comp_id]
        exact g2))
    beta_reduce
    rw [e, ← hs_comp, e2]
  · intro R _ I hx hq n i
    have er : (Φ _ I MvPolynomial.X hx ≫ prMap d (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)).right =
        (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
          sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) := by
      rw [Arrow.comp_right, hΦ]
      change chart _ ≫ prod.map (𝟙 _) (spMap _) = _
      rw [chart, prod.lift_map, Category.comp_id, Category.id_comp]
    have hb2 := (hE H q d R I hx hq _ er _ _).comp ((hT H q d R hq).2 _ (hτ q R hq) n i)
    convert hb2 using 1
    funext a
    refine Eq.symm ((hs_act h6 q _ _ _).trans (congrArg₂ (Hs.act q) ?_ ?_))
    · refine (congrArg (fun f => pull _ f _ n (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ n a)) er).trans ?_
      exact (pull_comp _ _ _ _ _ _).symm.trans (congrArg (fun f => pull _ f _ n a) (prod.lift_snd _ _))
    · exact (hs_comp q _ _ _ _ _).symm.trans (congrArg _ (hb q R _ _ hq))
  · intro r hr A _ I x hx hq
    have : NeZero r := ⟨fun h => NeZero.ne q (by simpa [h] using hr)⟩
    have hr' : IsUnit (r : A) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hr) hq
    have hmem : red q r _ _ _ (τ q A).1 ∈ Hs r (pr d A) (2 * d) d := by
      change pull _ (dbl.inr _) _ _ _ = 0
      have h0 : pull _ (dbl.inr (pr d A)) (tw q d) (2 * d) (τ q A).1 = 0 := (τ q A).2
      rw [pull_red, h0, map_zero]
    have e := huq r A hr' _ ((hN h6 h11 q d A hq _ (hτ q A hq)).2 r hr ⟨_, hmem⟩ rfl)
    change pull _ (dbl.map _) _ _ (τ r A).1 = red q r _ _ _ (pull _ (dbl.map _) _ _ (τ q A).1)
    rw [← e]
    exact pull_red _ _ _ _ _ _

end LateralTheory.CohomologicalPurity.Thom
