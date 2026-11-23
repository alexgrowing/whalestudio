import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConnectedGlobalSections

variable {q : ℕ} [NeZero q] {i : ℤ}

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (t : Sec F U) :
    Sec.res g (n • t) = n • Sec.res g t := map_nsmul ((F.obj.map g.op).hom) n t

theorem res_twGen {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ

theorem prim_map_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    (ζ.map g.appTop.hom).map k.appTop.hom = ζ.map (k ≫ g).appTop.hom := by
  apply Subtype.ext
  simp [Prim.map]
  rfl

theorem nsmul_eq_up {U : Scheme.{0}} (n : ℕ) (t : Sec (tw q i) U) : n • t = (ULift.up (n : ZMod q)) • t := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  rfl

theorem scalar_eq {U : Scheme.{0}} [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c d : ZMod q)
    (h : c.val • twGen i ζ = d.val • twGen i ζ) : c = d := by
  have h0 : (c - d).val • twGen i ζ = 0 := by
    rw [nsmul_eq_up, ZMod.natCast_zmod_val]
    rw [nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
    have : (ULift.up (c - d) : ULift.{1} (ZMod q)) = ULift.up c - ULift.up d := rfl
    rw [this, sub_smul, h, sub_self]
  have hd := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ _ h0
  have hv : (c - d).val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _)
  exact sub_eq_zero.1 ((ZMod.val_eq_zero _).1 hv)

theorem q_nsmul {U : Scheme.{0}} (t : Sec (tw q i) U) (k : ℕ) : (q * k) • t = 0 := by
  rw [nsmul_eq_up]
  have : ((q * k : ℕ) : ZMod q) = 0 := by simp
  rw [this]
  exact zero_smul _ t

theorem sec_eq_nsmul (X : Scheme.{0}) [Nonempty X] (hX : ∀ s : Set X, IsClopen s → s = ∅ ∨ s = Set.univ)
    (ζ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X) : ∃ c : ℕ, y = c • twGen i ζ := by
  classical
  let P : ∀ V : Scheme.{0}, (V ⟶ X) → ℕ → Prop := fun V g c => Sec.res g y = c • twGen i (ζ.map g.appTop.hom)
  have hstab : ∀ c (V W : Scheme.{0}) (g : V ⟶ X) (k : W ⟶ V), P V g c → P W (k ≫ g) c := by
    intro c V W g k h
    simp only [P] at h ⊢
    rw [res_comp, h, res_nsmul, res_twGen, prim_map_comp]
  have hloc := (loc_iff_etale_affine_points X (fun V g => ∃ c, P V g c)
    (fun V W g k ⟨c, h⟩ => ⟨c, hstab c V W g k h⟩)).1 ((GlobalTheory.T.tateTwist_sections_locally_generated q i).2.1 X ζ y)
  let S : ZMod q → Set X := fun c =>
    {x | ∃ (V : Scheme.{0}) (g : V ⟶ X), IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g c.val}
  have hopen : ∀ c, IsOpen (S c) := by
    intro c
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨V, g, hV, hg, hx, hP⟩
    haveI := hg
    refine ⟨Set.range g, ?_, g.isOpenMap.isOpen_range, hx⟩
    rintro _ ⟨v, rfl⟩
    exact ⟨V, g, hV, hg, ⟨v, rfl⟩, hP⟩
  have hcov : ∀ x, ∃ c, x ∈ S c := by
    intro x
    obtain ⟨V, g, hV, hg, hx, n, hn⟩ := hloc x
    refine ⟨(n : ZMod q), V, g, hV, hg, hx, ?_⟩
    simp only [P] at hn ⊢
    rw [hn, nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val]
  have hdisj : ∀ c d x, x ∈ S c → x ∈ S d → c = d := by
    rintro c d x ⟨V, g, -, -, ⟨v, rfl⟩, hP⟩ ⟨V', g', -, -, ⟨v', hv'⟩, hP'⟩
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := g') v v' hv'.symm
    haveI : Nonempty ↥(Limits.pullback g g') := ⟨z⟩
    have h1 := hstab _ _ _ g (pullback.fst g g') hP
    have h2 := hstab _ _ _ g' (pullback.snd g g') hP'
    simp only [P] at h1 h2
    rw [pullback.condition] at h1
    exact scalar_eq _ c d (h1.symm.trans h2)
  obtain ⟨x0⟩ := ‹Nonempty X›
  obtain ⟨c0, hx0⟩ := hcov x0
  have hcompl : (S c0)ᶜ = ⋃ d ∈ ({c0}ᶜ : Set (ZMod q)), S d := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨d, hd⟩ := hcov x
      exact ⟨d, fun h => hx (h ▸ hd), hd⟩
    · rintro ⟨d, hd, hxd⟩ hx
      exact hd (hdisj d c0 x hxd hx)
  have hclopen : IsClopen (S c0) := by
    refine ⟨?_, hopen c0⟩
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_biUnion fun d _ => hopen d
  have huniv : S c0 = Set.univ := by
    rcases hX _ hclopen with h | h
    · rw [h] at hx0; exact absurd hx0 (Set.notMem_empty _)
    · exact h
  refine ⟨c0.val, (sec_ext_glue (ZMod q) (tw q i) X).1 _ _ ?_⟩
  refine (loc_iff_etale_affine_points X (fun _ g => Sec.res g y = Sec.res g (c0.val • twGen i ζ))
    (fun V W g k h => by rw [res_comp, res_comp, h])).2 ?_
  intro x
  obtain ⟨V, g, hV, hg, hx, hP⟩ : x ∈ S c0 := huniv ▸ Set.mem_univ x
  refine ⟨V, g, hV, hg, hx, ?_⟩
  rw [hP, res_nsmul, res_twGen]

end GlobalTheory.EtC.ConnectedGlobalSections

namespace GlobalTheory.EtC.ConnectedGlobalSections

theorem clopen_of_idem (B : Type) [CommRing B] (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (s : Set (Spec (CommRingCat.of B))) (hs : IsClopen s) : s = ∅ ∨ s = Set.univ := by
  obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.1 (show IsClopen (X := PrimeSpectrum B) s from hs)
  rcases hB e he with rfl | rfl
  · left
    change (s : Set (PrimeSpectrum B)) = ∅
    rw [h]; simp <;> rfl
  · right
    change (s : Set (PrimeSpectrum B)) = Set.univ
    rw [h]; simp <;> rfl

end GlobalTheory.EtC.ConnectedGlobalSections

open GlobalTheory.EtC.ConnectedGlobalSections in

theorem GlobalTheory.EtC.h_zero_pull_bijective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A'),
    IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → Nontrivial A' →
    (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) → (∀ e : A', IsIdempotentElem e → e = 0 ∨ e = 1) →
    ∀ i : ℤ, Function.Bijective (pull _ (spMap f) (tw q i) 0) := by
  intro q _ A A' _ _ f hq ⟨ζ0, hζ0⟩ hA' hidA hidA' i
  haveI : Nontrivial A := f.domain_nontrivial
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)
  let g : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom f)
  haveI : Nonempty (Spec (CommRingCat.of A)) := inferInstance
  haveI : Nonempty (Spec (CommRingCat.of A')) := inferInstance
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ⟨ζ0, hq, hζ0⟩
  have hres : Function.Bijective (Sec.res (F := tw q i) g) := by
    constructor
    · change Function.Injective ((tw q i).obj.map g.op).hom
      rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨c, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A hidA) ζ y
      have h0 : c • twGen i (ζ.map g.appTop.hom) = 0 := by
        rw [← res_twGen, ← res_nsmul]; exact hy
      obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 _ _ _ h0
      exact q_nsmul _ k
    · intro y
      obtain ⟨c, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A' hidA') (ζ.map g.appTop.hom) y
      exact ⟨c • twGen i ζ, by rw [res_nsmul, res_twGen]⟩
  have key : ∀ s, pull _ (spMap f) (tw q i) 0 (e _ s) = e _ (Sec.res g s) := fun s => he g s
  have hfun : ⇑(pull _ (spMap f) (tw q i) 0) = e _ ∘ Sec.res g ∘ (e _).symm := by
    funext x
    obtain ⟨s, rfl⟩ := (e _).surjective x
    simp [key]
  rw [hfun]
  exact (e _).bijective.comp (hres.comp (e _).symm.bijective)
