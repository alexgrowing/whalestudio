import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.ArtCoh

theorem ht_subsingleton_of_ringEquiv (q : ℕ) {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (n i : ℤ)
    [h : Subsingleton (Ht q (sp R) n i)] : Subsingleton (Ht q (sp S) n i) := by
  have hid : spMap (e : R →+* S) ≫ spMap (e.symm : S →+* R) = 𝟙 (sp S) := by
    rw [← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by ext x; simp
    rw [this]
    simp
  constructor
  intro x y
  have hx : pull _ (spMap (e : R →+* S)) _ _ (pull _ (spMap (e.symm : S →+* R)) _ _ x) = x := by
    rw [← pull_comp, hid, pull_id]
  have hy : pull _ (spMap (e : R →+* S)) _ _ (pull _ (spMap (e.symm : S →+* R)) _ _ y) = y := by
    rw [← pull_comp, hid, pull_id]
  rw [← hx, ← hy, Subsingleton.elim (pull _ (spMap (e.symm : S →+* R)) _ _ x)
    (pull _ (spMap (e.symm : S →+* R)) _ _ y)]

theorem ht_subsingleton_prod (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ)
    [Subsingleton (Ht q (sp A) n i)] [Subsingleton (Ht q (sp B) n i)] : Subsingleton (Ht q (sp (A × B)) n i) := by
  constructor
  intro x y
  exact (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q A B n i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem ht_subsingleton_of_subsingleton (q : ℕ) (Z : Type) [CommRing Z] [Subsingleton Z] (n i : ℤ) :
    Subsingleton (Ht q (sp Z) n i) := by
  have hfs : RingHom.fst Z Z = RingHom.snd Z Z := by ext x; exact Subsingleton.elim _ _
  constructor
  intro a b
  obtain ⟨x, hx⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q Z Z n i).2 (a, b)
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [hfs] at h1
  rw [← h1, ← h2]

theorem ht_subsingleton_pi (q : ℕ) (n i : ℤ) (ι : Type) [Finite ι] : ∀ (R : ι → Type) [∀ j, CommRing (R j)],
    (∀ j, Subsingleton (Ht q (sp (R j)) n i)) → Subsingleton (Ht q (sp (∀ j, R j)) n i) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro R _ hR
    have := ih (fun a => R (e a)) (fun a => hR (e a))
    exact ht_subsingleton_of_ringEquiv q (RingEquiv.piCongrLeft R e) n i
  | h_empty =>
    intro R _ _
    exact ht_subsingleton_of_subsingleton q _ n i
  | h_option ih =>
    intro R _ hR
    have h1 := hR none
    have h2 := ih (fun a => R (some a)) (fun a => hR (some a))
    have := ht_subsingleton_prod q (R none) (∀ a, R (some a)) n i
    exact ht_subsingleton_of_ringEquiv q (RingEquiv.piOptionEquivProd (R := R)).symm n i

theorem ht_subsingleton_artinian : ∀ (q : ℕ) (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (n i : ℤ),
    (∀ M : MaximalSpectrum K, Subsingleton (Ht q (sp (K ⧸ M.asIdeal)) n i)) → Subsingleton (Ht q (sp K) n i) := by
  intro q K _ _ _ n i h
  have := ht_subsingleton_pi q n i (MaximalSpectrum K) (fun M => K ⧸ M.asIdeal) h
  exact ht_subsingleton_of_ringEquiv q (IsArtinianRing.equivPi K).toRingEquiv.symm n i

end GlobalTheory.EtC.ArtCoh
