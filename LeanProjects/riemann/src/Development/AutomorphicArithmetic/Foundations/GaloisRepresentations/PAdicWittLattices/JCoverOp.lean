import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

namespace UpperTheory.Gal.G3

private theorem isUnit_natCast_sp (l : ℕ) (hl : l ≠ 0) (Ω : Type) [Field Ω] [CharZero Ω] :
    IsUnit ((l : Γ(sp Ω, ⊤))) := by
  have h : IsUnit ((l : Ω)) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hl)
  have h2 := h.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa using h2

private theorem th_pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}} {p : X ⟶ B}
    {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) : T.pull f h = T.pull f' h' := by
  subst e; rfl

private theorem bcMap_comp' {B B' X Y Z : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : Z ⟶ B'} (u : Z ⟶ Y)
    (f : Y ⟶ X) (hu : u ≫ q = r) (hf : f ≫ p = q) (h : (u ≫ f) ≫ p = r) :
    bcMap g u hu ≫ bcMap g f hf = bcMap g (u ≫ f) h := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, bcMap_fst, Category.assoc]
  · rw [Category.assoc, bcMap_snd, bcMap_snd, bcMap_snd]

private theorem lmap_of_key {R : Type*} [Semiring R] {M N P : ℤ → Type*} [∀ m, AddCommMonoid (M m)]
    [∀ m, AddCommMonoid (N m)] [∀ m, AddCommMonoid (P m)] [∀ m, Module R (M m)] [∀ m, Module R (N m)]
    [∀ m, Module R (P m)] (T : ∀ m, M m →ₗ[R] N m) (C : ∀ m, N m →ₗ[R] P m) {I : Type*} [Fintype I]
    (S : I → ∀ m, M m →ₗ[R] P m) (h : ∀ m x, C m (T m x) = ∑ i, S i m x) (x : DirectSum ℤ M) :
    DirectSum.lmap C (DirectSum.lmap T x) = ∑ i, DirectSum.lmap (S i) x := by
  apply DFinsupp.ext
  intro m
  have hs : ∀ s : Finset I, (∑ i ∈ s, DirectSum.lmap (S i) x) m = ∑ i ∈ s, S i m (x m) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, DirectSum.add_apply, ih, DirectSum.lmap_apply]
  rw [hs, DirectSum.lmap_apply, DirectSum.lmap_apply]
  exact h m (x m)

private theorem coverCore (hE : EtnGood) (hS : BcSplits) (hG : BcGal) (hU : CorrUniq) (l : ℕ) [Fact l.Prime]
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [CharZero Ω] (H : HTower k) (g : H.Γ) [IsFinite (H.s g)] [Etale (H.s g)]
    (W : Scheme.{0}) (c : W ⟶ H.Z) (G : Type) [Group G] [Finite G] (a : G → (W ⟶ W)) (I : Type) [Fintype I]
    (σ : I → (W ⟶ H.Y g)) (hσ : ∀ i, (σ i ≫ H.t g) ≫ H.q = c ≫ H.q) (hGal : IsGalois c G a) (hSp : Splits (H.s g) c σ)
    (hEx : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T) :
    ∃ Tm : ∀ m : ℤ, HQ l (sch.obj (H.geomZ Ω)) m 0 →ₗ[ℚ_[l]] HQ l (sch.obj (H.geomZ Ω)) m 0,
      hop l H Ω g = DirectSum.lmap Tm ∧
      (∀ (m : ℤ) (x : HQ l (sch.obj (H.geomZ Ω)) m 0), pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0 (Tm m x) =
        ∑ i, pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0 x) ∧
      ∀ m : ℤ, Function.Injective (pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0) := by
  classical
  have hu := isUnit_natCast_sp l (Fact.out : l.Prime).ne_zero Ω
  have hGood := fun m : ℤ => hE l (sp Ω) hu m 0
  let g₀ : sp Ω ⟶ sp k := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  have hσs : ∀ j, σ j ≫ H.s g ≫ H.q = c ≫ H.q := fun j => by
    rw [← Category.assoc, hSp.choose j]
  have hac : ∀ x, a x ≫ c ≫ H.q = c ≫ H.q := fun x => by
    rw [← Category.assoc, hGal.2.2.2.2.2.choose x]
  obtain ⟨hfin, het, hspl⟩ := hS g₀ H.q (H.s g ≫ H.q) (c ≫ H.q) (H.s g) rfl c rfl I σ hσs
  have hsp' := hspl hSp
  have hgal' := hG g₀ H.q (c ≫ H.q) c rfl G a hac hGal
  choose tr htr using fun m : ℤ => (hGood m).tr (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀)
    (bcMap g₀ (H.s g) rfl) (bcMap_snd _ _ _)
  let Tm : ∀ m : ℤ, HQ l (sch.obj (H.geomZ Ω)) m 0 →ₗ[ℚ_[l]] HQ l (sch.obj (H.geomZ Ω)) m 0 := fun m =>
    tr m ∘ₗ (etn l (sp Ω) m 0).pull (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _)
  have key : ∀ (m : ℤ) (x : HQ l (sch.obj (H.geomZ Ω)) m 0),
      pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0 (Tm m x) =
        ∑ i, pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0 x := by
    intro m x
    have h1 := htr m _ (pullback.snd (c ≫ H.q) g₀) (bcMap g₀ c rfl) (bcMap_snd _ _ _) I
      (fun j => bcMap g₀ (σ j) (hσs j)) (fun j => bcMap_snd _ _ _) hsp'
      ((etn l (sp Ω) m 0).pull (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _) x)
    refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
    have e := bcMap_comp' g₀ (σ i) (H.t g) (hσs i) (H.comm g) (hσ i)
    have h2 := (etn l (sp Ω) m 0).pull_comp (bcMap g₀ (σ i) (hσs i)) (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _)
      (bcMap_snd _ _ _) (by rw [Category.assoc, bcMap_snd, bcMap_snd]) x
    rw [← h2, th_pull_congr _ e _ (bcMap_snd _ _ _)]
    rfl
  have hA : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (DirectSum.lmap Tm) := by
    refine ⟨_, bcMap g₀ c rfl, G, inferInstance, inferInstance, fun x => bcMap g₀ (a x) (hac x), I, inferInstance,
      fun j => bcMap g₀ (σ j) (hσs j), hgal', hsp', fun x => ?_⟩
    have e : ∀ j, bcMap g₀ (σ j) (hσs j) ≫ H.tΩ Ω g = geomMap Ω (c ≫ H.q) (σ j ≫ H.t g) (hσ j) := fun j =>
      bcMap_comp' g₀ (σ j) (H.t g) (hσs j) (H.comm g) (hσ j)
    simp only [e]
    exact lmap_of_key Tm (fun m => pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0)
      (fun i m => pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0) key x
  refine ⟨Tm, ?_, key, fun m => ?_⟩
  · have hh : hop l H Ω g = hEx.choose := by
      unfold hop
      exact dif_pos hEx
    rw [hh]
    exact hU l Ω (pullback.snd H.q g₀) _ _ _ _ hEx.choose_spec hA
  · exact (hGood m).inj _ _ (bcMap g₀ c rfl) (bcMap_snd _ _ _) G _ hgal'

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.jCoverOp :
    EtnGood → BcSplits → BcGal → CorrUniq → PositivityTheory.AutomorphicGaloisHodgeTate.G8.CoverOp := by
  intro hE hS hG hU l _ K H _ g _ _ W c G _ _ a I _ σ hσ hGal hSp hEx n
  obtain ⟨Tm, h1, h2, h3⟩ := coverCore hE hS hG hU l H g W c G a I σ hσ hGal hSp hEx
  refine ⟨h3 n, Tm n, fun x => ?_, ?_⟩
  · rw [h1, DirectSum.lmap_lof]
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.sum_apply]
    exact h2 n x
