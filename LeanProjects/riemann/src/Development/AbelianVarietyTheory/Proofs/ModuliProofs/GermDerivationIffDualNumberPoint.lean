import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.PtDual

variable {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]

def ev (v : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) : Γ(X, W) →+* R :=
  (v.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom

theorem ev_fromSpec (v : Sp R ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom (ev v U h)) ≫ hU.fromSpec = v := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec v hU (isAffineOpen_top _) h
  rw [ev, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, this, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem ev_ext {v v' : Sp R ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U)
    (e : ev v U h = ev v' U h') : v = v' := by
  rw [← ev_fromSpec v hU h, ← ev_fromSpec v' hU h', e]

theorem exists_ev {U : X.Opens} (hU : IsAffineOpen U) (φ : Γ(X, U) →+* R) :
    ∃ (v : Sp R ⟶ X) (h : ⊤ ≤ v ⁻¹ᵁ U), ev v U h = φ := by
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    exact le_top
  refine ⟨_, h, ?_⟩
  have := ev_fromSpec _ hU h
  rw [cancel_mono] at this
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

theorem ev_res (v : Sp R ⟶ X) {W W' : X.Opens} (e : W' ≤ W) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ v ⁻¹ᵁ W') (f : Γ(X, W)) :
    ev v W' h' (resG X e f) = ev v W h f := by
  have : X.presheaf.map (homOfLE e).op ≫ v.appLE W' ⊤ h' = v.appLE W ⊤ h := Scheme.Hom.map_appLE ..
  unfold ev
  rw [← this]
  rfl

theorem ev_comp (φ : R →+* S) (v : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ W)
    (f : Γ(X, W)) : ev (spMap φ ≫ v) W h' f = φ (ev v W h f) := by
  have h1 : v.appLE W ⊤ h ≫ (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ ≫ v).appLE W ⊤ h' :=
    Scheme.Hom.appLE_comp_appLE ..
  have h2 : (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg _ ((Sp S).presheaf.map_id _)).trans (Category.comp_id _)
  have h3 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  unfold ev
  rw [← h1, h2, Category.assoc]
  erw [h3]
  rfl

abbrev pt0 : Sp ℂ ⟶ Sp (DualNumber ℂ) := spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

theorem le_preimage_iff (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ W ↔ ⊤ ≤ (pt0 ≫ v) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  refine ⟨fun h p _ => h (Set.mem_univ _), fun h p _ => ?_⟩
  have hs : Function.Surjective (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hp : (p : PrimeSpectrum (DualNumber ℂ)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    have hx' : x.fst = 0 := hx
    refine (p : PrimeSpectrum (DualNumber ℂ)).isPrime.mem_of_pow_mem 2 ?_
    have : x ^ 2 = 0 := by
      ext <;> simp [pow_two, hx']
    rw [this]
    exact zero_mem _
  obtain ⟨q, rfl⟩ := hp
  exact h (Set.mem_univ q)

theorem fst_ev {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W)
    (f : Γ(X, W)) : (ev v W h f).fst = valAt' y W f := by
  subst hv
  have h' := (le_preimage_iff v W).1 h
  rw [valAt'_eq_valAtHom _ h']
  exact (ev_comp _ v W h h' f).symm

def derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ W) :
    Γ(X, W) →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl (valAt' y W f) + TrivSqZeroExt.inr (δ W f)
  map_one' := by
    have := hδ.mul W h 1 1
    rw [_root_.mul_one, valAt'_one y h, _root_.one_mul, left_eq_add] at this
    ext <;> simp [valAt'_one y h, this]
  map_mul' a b := by
    ext
    · simp [valAt'_mul]
    · simp [hδ.mul W h, mul_comm]
  map_zero' := by
    have := hδ.add W h 0 0
    rw [add_zero, left_eq_add] at this
    ext <;> simp [valAt'_zero, this]
  map_add' a b := by
    ext
    · simp [valAt'_add]
    · simp [hδ.add W h]

theorem fst_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, W)) : (derHom hδ W h f).fst = valAt' y W f := by
  simp [derHom]

theorem snd_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, W)) : (derHom hδ W h f).snd = δ W f := by
  simp [derHom]

theorem derHom_res {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) {W W' : X.Opens} (e : W' ≤ W)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W') (f : Γ(X, W)) : derHom hδ W' h' (resG X e f) = derHom hδ W h f := by
  ext
  · rw [fst_derHom, fst_derHom, valAt'_res y e f h']
  · rw [snd_derHom, snd_derHom, hδ.res W W' e h']

theorem exists_affine (y : Sp ℂ ⟶ X) : ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ y ⁻¹ᵁ U := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  exact ⟨U, hU, (top_le_preimage_iff_mem y U).2 hy⟩

theorem ev_eq_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) {v : Sp (DualNumber ℂ) ⟶ X}
    (hv : pt0 ≫ v = y) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U)
    (e : ev v U h = derHom hδ U h') (W : X.Opens) (k : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)) : (ev v W k f).snd = δ W f := by
  have k' : ⊤ ≤ y ⁻¹ᵁ W := hv ▸ (le_preimage_iff v W).1 k
  obtain ⟨g, hg, hy⟩ := hU.exists_basicOpen_le (V := W) ⟨_, (top_le_preimage_iff_mem y W).1 k'⟩
    ((top_le_preimage_iff_mem y U).1 h')
  have l' : ⊤ ≤ y ⁻¹ᵁ X.basicOpen g := (top_le_preimage_iff_mem y _).2 hy
  have l : ⊤ ≤ v ⁻¹ᵁ X.basicOpen g := (le_preimage_iff v _).2 (hv ▸ l')
  have := hU.isLocalization_basicOpen g
  have e' : ev v _ l = derHom hδ _ l' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
    refine (ev_res v (X.basicOpen_le g) h l a).trans ?_
    rw [e]
    exact (derHom_res hδ (X.basicOpen_le g) h' l' a).symm
  rw [← ev_res v hg k l, e', derHom_res hδ hg k' l', snd_derHom]

open Classical in
theorem exists_ptDer {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) :
    ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  have H : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ⊤ ≤ v ⁻¹ᵁ W := fun W h => (le_preimage_iff v _).2 (hv ▸ h)
  refine ⟨fun W f => if h : ⊤ ≤ v ⁻¹ᵁ W then (ev v W h f).snd else 0, ⟨?_, ?_, ?_⟩, fun W h f => ?_⟩
  · intro W h f f'
    simp only [dif_pos (H W h), map_add, TrivSqZeroExt.snd_add]
  · intro W h f f'
    simp only [dif_pos (H W h), map_mul, DualNumber.snd_mul, fst_ev hv]
    ring
  · intro W W' e h f
    have k := H W (top_le_preimage_mono y e h)
    simp only [dif_pos (H W' h), dif_pos k, ev_res v e k]
  · simp only [dif_pos h]

theorem existsUnique_point {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) :
    ∃! v : Sp (DualNumber ℂ) ⟶ X, pt0 ≫ v = y ∧
      ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  obtain ⟨U, hU, h'⟩ := exists_affine y
  obtain ⟨v, h, e⟩ := exists_ev hU (derHom hδ U h')
  have hv : pt0 ≫ v = y := by
    refine ev_ext hU ((le_preimage_iff v U).1 h) h' (RingHom.ext fun f => ?_)
    rw [ev_comp _ v U h, e]
    exact (fst_derHom hδ U h' f).trans (valAt'_eq_valAtHom y h' f)
  refine ⟨v, ⟨hv, ev_eq_derHom hδ hv hU h h' e⟩, ?_⟩
  rintro w ⟨hw, hw'⟩
  have k : ⊤ ≤ w ⁻¹ᵁ U := (le_preimage_iff w _).2 (hw ▸ h')
  refine ev_ext hU k h (RingHom.ext fun f => ?_)
  rw [e]
  ext
  · rw [fst_ev hw, fst_derHom]
  · rw [hw', snd_derHom]

end GlobalTheory.KS.PtDual

namespace GlobalTheory.KS

theorem ptDer_iff_dualPoint : ∀ (X : Scheme.{0}) (y : Sp ℂ ⟶ X), (∀ δ, PtDer y δ → ∃! v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y → ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f :=
  fun _ _ => ⟨fun _ hδ => PtDual.existsUnique_point hδ, fun _ hv => PtDual.exists_ptDer hv⟩

end GlobalTheory.KS
end
