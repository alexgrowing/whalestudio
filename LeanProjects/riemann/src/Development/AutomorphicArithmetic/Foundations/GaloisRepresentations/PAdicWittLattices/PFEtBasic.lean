import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFibFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PChart

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem fib_finite {V U : Scheme.{0}} (r : V ⟶ U) [IsFinite r] (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ U) : Finite {y : Spec (CommRingCat.of K) ⟶ V // y ≫ r = x} :=
  (UpperTheory.Gal.TranscendenceTraces.fibFin_of UpperTheory.Gal.TranscendenceTraces.chart_of r K x).to_subtype

private theorem fEt_of_pullback {P Y Z' Z : Scheme.{0}} (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z)
    (d : ℕ) (h : IsPullback v s' s g) (hs : FEt s d) : FEt s' d := by
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h hs.1,
    MorphismProperty.of_isPullback (P := @Etale) h hs.2.1, fun K _ _ x => ?_⟩
  let eqv : {y' : Spec (CommRingCat.of K) ⟶ P // y' ≫ s' = x} ≃
      {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x ≫ g} :=
    { toFun := fun y' => ⟨y'.1 ≫ v, by rw [Category.assoc, h.w, ← Category.assoc, y'.2]⟩
      invFun := fun y => ⟨h.lift y.1 x y.2, h.lift_snd _ _ _⟩
      left_inv := fun y' => Subtype.ext (h.hom_ext (by rw [h.lift_fst]) (by rw [h.lift_snd, y'.2]))
      right_inv := fun y => Subtype.ext (h.lift_fst _ _ _) }
  rw [Nat.card_congr eqv]
  exact hs.2.2 K (x ≫ g)

private theorem fEt_comp {W Y Z : Scheme.{0}} (r : W ⟶ Y) (s : Y ⟶ Z) (d e : ℕ) (hr : FEt r e) (hs : FEt s d) :
    FEt (r ≫ s) (d * e) := by
  haveI := hr.1
  haveI := hr.2.1
  haveI := hs.1
  haveI := hs.2.1
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  haveI : Fintype {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x} :=
    @Fintype.ofFinite _ (fib_finite s K x)
  haveI hfin : ∀ y : {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x},
      Finite {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r = y.1} := fun y => fib_finite r K y.1
  let eqv : {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r ≫ s = x} ≃
      Σ y : {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x},
        {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r = y.1} :=
    { toFun := fun w => ⟨⟨w.1 ≫ r, by rw [Category.assoc]; exact w.2⟩, ⟨w.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [← Category.assoc, p.2.2, p.1.2]⟩
      left_inv := fun w => rfl
      right_inv := by
        intro p
        rcases p with ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
        dsimp only at hw
        subst hw
        rfl }
  rw [Nat.card_congr eqv, Nat.card_sigma, Finset.sum_congr rfl (fun y _ => hr.2.2 K y.1),
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hs.2.2 K x, smul_eq_mul]

private theorem fEt_galois (hp : PtsOfSplits) {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] [Finite G]
    (a : G → (W ⟶ W)) (h : IsGalois c G a) : FEt c (Nat.card G) := by
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2.1
  refine ⟨inferInstance, inferInstance, fun Ω _ _ x => ?_⟩
  obtain ⟨w, hw⟩ := Surjective.surj (f := c) (UpperTheory.Gal.TranscendenceTraces.pt x)
  obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_of c Ω x w hw
  have hsp := h.2.2.2.2.2
  have hac : ∀ g, a g ≫ c = c := hsp.1
  have key : ∀ y : Spec (CommRingCat.of Ω) ⟶ W, y ≫ c = x → ∃! g : G, z ≫ a g = y :=
    fun y hy => hp c c G a hsp Ω z y (by rw [hy, hz])
  let f : G → {y : Spec (CommRingCat.of Ω) ⟶ W // y ≫ c = x} :=
    fun g => ⟨z ≫ a g, by rw [Category.assoc, hac, hz]⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro g g' hgg
      have hv : z ≫ a g = z ≫ a g' := congrArg Subtype.val hgg
      obtain ⟨g0, _, hu⟩ := key (z ≫ a g) (f g).2
      exact (hu g rfl).trans (hu g' hv.symm).symm
    · rintro ⟨y, hy⟩
      obtain ⟨g, hg, _⟩ := key y hy
      exact ⟨g, Subtype.ext hg⟩
  exact (Nat.card_congr (Equiv.ofBijective f hbij)).symm

theorem UpperTheory.Gal.G3.pFEtBasic :
    PtsOfSplits → FEtBasic := by
  intro hp
  exact ⟨fun v s' s g d h hs => fEt_of_pullback v s' s g d h hs, fun r s d e hr hs => fEt_comp r s d e hr hs,
    fun c G _ _ a h => fEt_galois hp c G a h⟩
