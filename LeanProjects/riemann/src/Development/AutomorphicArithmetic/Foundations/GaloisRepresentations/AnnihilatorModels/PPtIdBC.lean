import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PhiKOfNil
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private lemma mem_basicOpen_fn {O : Type} [CommRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of O)) (a : O) (x : Y) :
    x ∈ Y.basicOpen (fn f a) ↔ a ∉ (f x).asIdeal := by
  have h1 : f ⁻¹ᵁ (Spec (CommRingCat.of O)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)
      = Y.basicOpen (fn f a) := Scheme.preimage_basicOpen_top f _
  rw [← h1, basicOpen_eq_of_affine]
  exact Iff.rfl

private lemma flat_h {O O' : Type} [CommRing O] [CommRing O'] (σ : O →+* O') (hσ : σ.Flat)
    {Y Y' : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of O)} {f' : Y' ⟶ Spec (CommRingCat.of O')} {h : Y' ⟶ Y}
    (hp : IsPullback h f' f (Spec.map (CommRingCat.ofHom σ))) : Flat h := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := Flat.SpecMap_iff.2 hσ
  exact MorphismProperty.of_isPullback hp.flip this

private lemma genPt_h {O O' : Type} [CommRing O] [CommRing O'] (σ : O →+* O') (hσ : σ.Flat) (ϖ : O) (ϖ' : O')
    (hr : ∀ P : Ideal O', P.IsPrime → (σ ϖ ∈ P ↔ ϖ' ∈ P))
    {Y Y' : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of O)} {f' : Y' ⟶ Spec (CommRingCat.of O')} {h : Y' ⟶ Y}
    (hp : IsPullback h f' f (Spec.map (CommRingCat.ofHom σ))) (x : Y') (hx : GenPt (fn f' ϖ') x) :
    GenPt (fn f ϖ) (h x) := by
  have key : ∀ w : Y', w ∈ Y'.basicOpen (fn f' ϖ') ↔ h w ∈ Y.basicOpen (fn f ϖ) := by
    intro w
    rw [mem_basicOpen_fn, mem_basicOpen_fn]
    have e : f (h w) = (Spec.map (CommRingCat.ofHom σ)) (f' w) := by
      have := congrArg (fun t => t w) (congrArg (fun t : Y' ⟶ _ => (t : Y' → _)) hp.w)
      simpa using this
    rw [e]
    have := hr (f' w).asIdeal (f' w).isPrime
    change ϖ' ∉ (f' w).asIdeal ↔ σ ϖ ∉ (f' w).asIdeal
    exact (not_congr this).symm
  have := flat_h σ hσ hp
  refine ⟨fun hb => hx.1 ((key x).2 hb), fun x' hx' hs => ?_⟩
  obtain ⟨w, hw, rfl⟩ := Flat.generalizingMap h hs
  have := hx.2 w (fun hb => hx' ((key w).1 hb)) hw
  rw [this]

private lemma twist_comp {κ : Type} [CommRing κ] (φ : κ →+* κ) {Y Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (x : Spec (CommRingCat.of κ) ⟶ Y') (m : ℕ) :
    (twist φ Y)^[m] (x ≫ h) = (twist φ Y')^[m] x ≫ h := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    simp only [twist, Category.assoc]

private lemma twist_base {κ : Type} [CommRing κ] (φ : κ →+* κ) {S Y' : Scheme.{0}} (f' : Y' ⟶ S)
    (β : Spec (CommRingCat.of κ) ⟶ S) (hβ : Spec.map (CommRingCat.ofHom φ) ≫ β = β)
    (x : Spec (CommRingCat.of κ) ⟶ Y') (hx : x ≫ f' = β) (m : ℕ) :
    (twist φ Y')^[m] x ≫ f' = β := by
  induction m generalizing x with
  | zero => exact hx
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    refine ih _ ?_
    simp only [twist, Category.assoc, hx, hβ]

private lemma beta_fix {O' V : Type} [CommRing O'] [CommRing V] [IsLocalRing V] (q : ℕ) (ϖ' : O')
    (hq : ∀ a : O', a ^ q - a ∈ Ideal.span {ϖ'})
    (φ : IsLocalRing.ResidueField V →+* IsLocalRing.ResidueField V) (hφ : ∀ a, φ a = a ^ q)
    (c : CommRingCat.of O' ⟶ CommRingCat.of V)
    (hc : ϖ' ∈ (IsLocalRing.maximalIdeal V).comap c.hom) :
    Spec.map (CommRingCat.ofHom φ) ≫ resPt V ≫ Spec.map c = resPt V ≫ Spec.map c := by
  rw [resPt, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  have h0 : IsLocalRing.residue V (c.hom ϖ') = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hc
  have h1 : IsLocalRing.residue V (c.hom (a ^ q - a)) = 0 := by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hq a)
    rw [← hb, map_mul, map_mul, h0, mul_zero]
  simp only [map_sub, map_pow, sub_eq_zero] at h1
  simpa [hφ] using h1

private lemma closed_mem {O' V : Type} [CommRing O'] [CommRing V] [IsLocalRing V] (ϖ' : O')
    {Y' : Scheme.{0}} (f' : Y' ⟶ Spec (CommRingCat.of O')) (y : Spec (CommRingCat.of V) ⟶ Y')
    (c : CommRingCat.of O' ⟶ CommRingCat.of V) (hc : y ≫ f' = Spec.map c)
    (hx : y (IsLocalRing.closedPoint V) ∉ Y'.basicOpen (fn f' ϖ')) :
    ϖ' ∈ (IsLocalRing.maximalIdeal V).comap c.hom := by
  rw [mem_basicOpen_fn, not_not] at hx
  have e : f' (y (IsLocalRing.closedPoint V)) = (Spec.map c) (IsLocalRing.closedPoint V) := by
    rw [← hc]; rfl
  rw [e] at hx
  exact hx

theorem UpperTheory.Gal.crystallineComparison.ptIdBC_of :
    PtIdBC := by
  classical
  intro l q n O O' _ _ σ hσ ϖ ϖ' hr hq Y Y' f f' h hp T T' g hg hrr hf hId V _ _ _ _ hl y hG φ hφ I _ z hz
  have hG' : GenPt (fn f ϖ) ((y ≫ h) (IsLocalRing.closedPoint V)) := genPt_h σ hσ ϖ ϖ' hr hp _ hG
  let z' : ∀ j, I j → (T j).Sec (y ≫ h) := fun j i => ⟨(z j i).1 ≫ g j, by
    rw [Category.assoc, ← (hg j).w, ← Category.assoc, (z j i).2]⟩
  have hz' : ∀ j, Function.Bijective (z' j) := by
    intro j
    constructor
    · intro i₁ i₂ e
      have e' : (z j i₁).1 ≫ g j = (z j i₂).1 ≫ g j := congrArg Subtype.val e
      refine (hz j).1 (Subtype.ext ((hg j).hom_ext ?_ e'))
      rw [(z j i₁).2, (z j i₂).2]
    · intro w
      obtain ⟨i, hi⟩ := (hz j).2 ⟨(hg j).lift y w.1 w.2.symm, (hg j).lift_fst _ _ _⟩
      refine ⟨i, Subtype.ext ?_⟩
      change (z j i).1 ≫ g j = w.1
      rw [hi]
      exact (hg j).lift_snd _ _ _
  have key := hId V hl (y ≫ h) hG' φ hφ I z' hz'
  let c : CommRingCat.of O' ⟶ CommRingCat.of V := Spec.preimage (y ≫ f')
  have hc : y ≫ f' = Spec.map c := (Spec.map_preimage _).symm
  have hmem := closed_mem ϖ' f' y c hc hG.1
  let β : Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Spec (CommRingCat.of O') := resPt V ≫ y ≫ f'
  have hβ : Spec.map (CommRingCat.ofHom φ) ≫ β = β := by
    simp only [β, hc]
    exact beta_fix q ϖ' hq φ hφ c hmem
  let Λ : (Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Y) → (Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Y') :=
    fun x => if hx : x ≫ f = β ≫ Spec.map (CommRingCat.ofHom σ) then hp.lift x β hx else resPt V ≫ y
  have hΛ : ∀ x' : Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Y', x' ≫ f' = β → Λ (x' ≫ h) = x' := by
    intro x' e
    have hx : (x' ≫ h) ≫ f = β ≫ Spec.map (CommRingCat.ofHom σ) := by
      rw [Category.assoc, hp.w, ← Category.assoc, e]
    simp only [Λ, dif_pos hx]
    apply hp.hom_ext
    · exact hp.lift_fst _ _ _
    · rw [hp.lift_snd, e]
  have hv : ∀ j i, (resPt V ≫ (z j i).1 ≫ (T' j).r) ≫ f' = β := by
    intro j i
    simp only [β, Category.assoc, hf j]
    rw [← Category.assoc (z j i).1, (z j i).2]
  have e1 : ∀ j i, resPt V ≫ (z' j i).1 ≫ (T j).r = (resPt V ≫ (z j i).1 ≫ (T' j).r) ≫ h := by
    intro j i
    change resPt V ≫ ((z j i).1 ≫ g j) ≫ (T j).r = _
    simp only [Category.assoc, hrr j]
  have hfin : ∀ (m : ℕ) j i, Λ ((twist φ Y)^[m] (resPt V ≫ (z' j i).1 ≫ (T j).r))
      = (twist φ Y')^[m] (resPt V ≫ (z j i).1 ≫ (T' j).r) := by
    intro m j i
    rw [e1, twist_comp]
    exact hΛ _ (twist_base φ f' β hβ _ (hv j i) m)
  unfold AltId at key ⊢
  have := congrArg (Multiset.map Λ) key
  rw [pts_map, pts_map] at this
  simpa only [hfin] using this
