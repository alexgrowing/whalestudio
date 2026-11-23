import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSemilocalHomLatticeClassesMod
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory

theorem latSum_tower_reps (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (D G C B : Submodule (𝓞 E) W) (hBC : B ≤ C) (hCG : C ≤ G) (hGD : G ≤ D)
    (hfin : Finite (↥D ⧸ B.comap D.subtype)) :
    ∃ R : Finset W, (∀ x ∈ R, x ∈ G) ∧ R.card = Nat.card (↥G ⧸ C.comap G.subtype) ∧
      ∀ f : W → ℂ, (∀ x, f x ≠ 0 → x ∈ G) → (∀ x y, x - y ∈ B → f x = f y) →
        latSum D B f = ∑ x ∈ R, latSum C B fun y => f (x + y) := by
  classical
  have key : ∀ (P Q : Submodule (𝓞 E) W) (t u : ↥P),
      (Submodule.Quotient.mk t : ↥P ⧸ Q.comap P.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ Q := by
    intro P Q t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    rfl
  set r : (↥G ⧸ C.comap G.subtype) → ↥G :=
    Function.surjInv (Submodule.Quotient.mk_surjective (C.comap G.subtype)) with hr
  set s : (↥C ⧸ B.comap C.subtype) → ↥C :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap C.subtype)) with hs
  set t : (↥D ⧸ B.comap D.subtype) → ↥D :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap D.subtype)) with ht
  have hr' : ∀ z, Submodule.Quotient.mk (r z) = z := fun z => Function.surjInv_eq _ z
  have hs' : ∀ z, Submodule.Quotient.mk (s z) = z := fun z => Function.surjInv_eq _ z
  have ht' : ∀ z, Submodule.Quotient.mk (t z) = z := fun z => Function.surjInv_eq _ z
  have hmem : ∀ p : (↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype), (r p.1 : W) + s p.2 ∈ D :=
    fun p => hGD (G.add_mem (r p.1).2 (hCG (s p.2).2))
  let φ : (↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype) → (↥D ⧸ B.comap D.subtype) :=
    fun p => Submodule.Quotient.mk ⟨_, hmem p⟩
  have hinj : Function.Injective φ := by
    rintro ⟨x, j⟩ ⟨x', j'⟩ h
    have h1 : (r x : W) + s j - (r x' + s j') ∈ B := (key D B _ _).1 h
    have h2 : x = x' := by
      rw [← hr' x, ← hr' x', key]
      have : (r x : W) - r x' = ((r x : W) + s j - (r x' + s j')) + (s j' - s j) := by abel
      rw [this]
      exact C.add_mem (hBC h1) (C.sub_mem (s j').2 (s j).2)
    subst h2
    have h3 : j = j' := by
      rw [← hs' j, ← hs' j', key]
      simpa using h1
    rw [h3]
  haveI hprod : Finite ((↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype)) := Finite.of_injective φ hinj
  haveI : Finite (↥G ⧸ C.comap G.subtype) := Finite.prod_left (↥C ⧸ B.comap C.subtype)
  haveI : Finite (↥C ⧸ B.comap C.subtype) := Finite.prod_right (↥G ⧸ C.comap G.subtype)
  letI := Fintype.ofFinite (↥G ⧸ C.comap G.subtype)
  letI := Fintype.ofFinite (↥C ⧸ B.comap C.subtype)
  letI := Fintype.ofFinite (↥D ⧸ B.comap D.subtype)
  have hrinj : Function.Injective fun z => (r z : W) := by
    intro z w h
    rw [← hr' z, ← hr' w, Subtype.ext h]
  refine ⟨Finset.univ.image fun z => (r z : W), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hx
    exact (r z).2
  · rw [Finset.card_image_of_injective _ hrinj, Nat.card_eq_fintype_card, Finset.card_univ]
  · intro f hf0 hf
    rw [Finset.sum_image fun _ _ _ _ h => hrinj h]
    unfold latSum
    simp only [finsum_eq_sum_of_fintype]
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_of_injective φ hinj _ _ ?_ ?_
    · intro z hz
      by_contra hne
      have hG : (t z : W) ∈ G := hf0 _ hne
      apply hz
      have h1 : (r (Submodule.Quotient.mk ⟨_, hG⟩) : W) - t z ∈ C := (key G C _ ⟨_, hG⟩).1 (hr' _)
      have h1' : (t z : W) - r (Submodule.Quotient.mk ⟨_, hG⟩) ∈ C := by
        simpa using C.neg_mem h1
      have h2 : (s (Submodule.Quotient.mk ⟨_, h1'⟩) : W) - ((t z : W) - r (Submodule.Quotient.mk ⟨_, hG⟩)) ∈ B :=
        (key C B _ ⟨_, h1'⟩).1 (hs' _)
      refine ⟨(Submodule.Quotient.mk ⟨_, hG⟩, Submodule.Quotient.mk ⟨_, h1'⟩), ?_⟩
      refine Eq.trans ?_ (ht' z)
      refine (key D B _ _).2 ?_
      convert h2 using 1
      simp only
      abel
    · intro p
      apply hf
      exact (key D B ⟨_, hmem p⟩ _).1 (ht' _).symm

theorem thInd_congr_of_sub_mem {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x y : HomE X.E a b)
    (h : x - y ∈ mulLat c (homAt S L L')) : A.thInd S L L' c x = A.thInd S L L' c y := by
  have h1 : A.IsLift S L L' c x = A.IsLift S L L' c y := by
    funext s
    unfold Amb.IsLift
    congr 1
    apply propext
    constructor
    · intro hs
      simpa using Submodule.add_mem _ hs h
    · intro hs
      simpa using Submodule.sub_mem _ hs h
  unfold Amb.thInd Amb.liftW
  rw [h1]

theorem latSum_thInd_regroup : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c c' : ℕ) (Ξ : HomE X.E a b → ℂ), A.IndAdd a b S (cA * (c * c')) → IsSdLat L → IsSdLat L' → 0 < cA → 0 < c → 0 < c' → (∀ x, Ξ x ≠ 0 → x ∈ homAt S L L') → (∀ x, ∀ y ∈ mulLat c (homAt S L L'), Ξ (x + y) = Ξ x) → ∃ R : Finset (HomE X.E a b), R.card ≤ c ^ (Module.finrank ℚ X.E * a * b) ∧ ∀ z, latSum (divLat cA (homAt S L L')) (mulLat (c * c') (homAt S L L')) (fun x => Ξ x * A.thInd S L L' (c * c') x z) = ∑ x ∈ R, Ξ x * A.thInd S L L' c x z := by
  intro X A a b S L L' cA c c' Ξ hadd hL hL' hcA hc hc' hsupp hinv
  have hdiv : ∀ (n : ℕ) x, x ∈ homAt S L L' → x ∈ divLat n (homAt S L L') := fun n x hx =>
    Submodule.smul_mem (homAt S L L') (n : 𝓞 X.E) hx
  have hone : ∀ x, x ∈ divLat 1 (homAt S L L') → x ∈ homAt S L L' := fun x hx => by
    simpa [divLat] using hx
  have hBC : mulLat (c * c') (homAt S L L') ≤ mulLat c (homAt S L L') := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(c' : 𝓞 X.E) • x, Submodule.smul_mem _ _ hx, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_mul, mul_smul]
  have hCG : mulLat c (homAt S L L') ≤ divLat 1 (homAt S L L') := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdiv 1 _ (Submodule.smul_mem (homAt S L L') (c : 𝓞 X.E) hx)
  have hfin := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S L L' cA (c * c') hL.1 hL'.1 hcA (Nat.mul_pos hc hc')).1
  have hcard := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S L L' 1 c hL.1 hL'.1 Nat.one_pos hc).2
  obtain ⟨R, hR, hRc, hsum⟩ := latSum_tower_reps X.E (HomE X.E a b) (divLat cA (homAt S L L'))
    (divLat 1 (homAt S L L')) (mulLat c (homAt S L L')) (mulLat (c * c') (homAt S L L')) hBC hCG
    (fun x hx => hdiv cA x (hone x hx)) hfin
  refine ⟨R, by rw [hRc]; simpa using hcard, fun z => ?_⟩
  rw [hsum]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [hadd L L' c c' x hc hc' ⟨hL, hL', Nat.mul_pos hc hc', Dvd.intro_left _ rfl, hdiv _ x (hone x (hR x hx))⟩ z]
    unfold latSum
    rw [mul_finsum]
    exact finsum_congr fun q => by beta_reduce; rw [hinv x _ (Subtype.property _)]
  · intro x hx
    exact hdiv 1 x (hsupp x (left_ne_zero_of_mul hx))
  · intro x y hxy
    rw [thInd_congr_of_sub_mem A S L L' (c * c') x y hxy]
    have := hinv y _ (hBC hxy)
    rw [add_sub_cancel] at this
    rw [this]

end GlobalTheory
