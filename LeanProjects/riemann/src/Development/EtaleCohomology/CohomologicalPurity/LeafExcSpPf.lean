import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem sqw {R : Type} [CommRing R] {K L K' L' : Cx R} {f : K ⟶ L} {f' : K' ⟶ L'} {a : K ⟶ K'} {b : L ⟶ L'}
    (comm : f ≫ b = a ≫ f') (n : ℤ) : f.f n ≫ b.f n = a.f n ≫ f'.f n := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, comm]

theorem chains_sq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    (chains R).map P'.hom ≫ (chains R).map φ.right = (chains R).map φ.left ≫ (chains R).map P.hom := by
  rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map (Arrow.w φ).symm

def coneMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    CochainComplex.mappingCone ((chains R).map P'.hom) ⟶ CochainComplex.mappingCone ((chains R).map P.hom) :=
  CochainComplex.mappingCone.map _ _ ((chains R).map φ.left) ((chains R).map φ.right) (chains_sq R φ)

def LeafConeQI : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsPullback P'.hom φ.left φ.right P.hom →
  Cover2 (ZMod q) φ.right P.hom → QuasiIso (coneMap (ZMod q) φ)

def LeafHsRel : Prop := A1 → ∀ (q : ℕ) (i : ℤ), ∃ e : ∀ (P : Arrow Spc) (n : ℤ), Mono P.hom →
    (Hs q P n i ≃+ Hrel (ZMod q) P.hom (tw q i) n),
  ∀ (P' P : Arrow Spc) (φ : P' ⟶ P) (h' : Mono P'.hom) (h : Mono P.hom) (n : ℤ) (x : Hs q P n i),
    e P' n h' (Hs.pull q φ n i x) = HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n (e P n h x)

def LeafChainsMono : Prop := ∀ (R : Type) [CommRing R] {E' E : Spc} (f : E' ⟶ E), Mono f → ∀ n : ℤ, Mono (((chains R).map f).f n)

def LeafCokIso : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsPullback P'.hom φ.left φ.right P.hom →
  Cover2 (ZMod q) φ.right P.hom → ∀ n : ℤ,
  IsIso (cokernel.map _ _ _ _ (sqw (chains_sq (ZMod q) φ) n))

def LeafConeCok : Prop := ∀ (R : Type) [CommRing R] {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L')
  (a : K ⟶ K') (b : L ⟶ L') (comm : f ≫ b = a ≫ f'), (∀ n, Mono (f.f n)) → (∀ n, Mono (f'.f n)) →
  (∀ n, IsIso (cokernel.map _ _ _ _ (sqw comm n))) → QuasiIso (CochainComplex.mappingCone.map f f' a b comm)

theorem leafExcSp_of (hQ : LeafConeQI) (hR : LeafHsRel) : LeafExcSp := by
  intro h1 q P' P φ hpb hc n i
  have hm : Mono P.hom := hc.2.1
  have hm' : Mono P'.hom := hpb.mono_fst_of_mono
  obtain ⟨e, he⟩ := hR h1 q i
  have := hQ q φ hpb hc
  have hb : Function.Bijective (HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n) := h1 (ZMod q) _ (tw q i) n
  have : (Hs.pull q φ n i : Hs q P n i → Hs q P' n i) =
      (e P' n hm').symm ∘ HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n ∘ e P n hm := by
    funext x
    simp [← he P' P φ hm' hm n x]
  rw [this]
  exact (e P' n hm').symm.bijective.comp (hb.comp (e P n hm).bijective)

theorem leafConeQI_of (hM : LeafChainsMono) (hK : LeafCokIso) (hC : LeafConeCok) : LeafConeQI := by
  intro q P' P φ hpb hc
  have hm : Mono P.hom := hc.2.1
  have hm' : Mono P'.hom := hpb.mono_fst_of_mono
  exact hC (ZMod q) _ _ _ _ (chains_sq (ZMod q) φ) (hM _ _ hm') (hM _ _ hm) (hK q φ hpb hc)

theorem leafExcSp_of' (hM : LeafChainsMono) (hK : LeafCokIso) (hC : LeafConeCok) (hR : LeafHsRel) : LeafExcSp :=
  leafExcSp_of (leafConeQI_of hM hK hC) hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
