import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumTransportEquivariant
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.Transp

section General
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V'']

def img (e : V ≃ₗ[K] V') (L : Submodule R V) : Submodule R V' :=
  L.map (e.toLinearMap.restrictScalars R)

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
omit [StarRing K] in
theorem _root_.GlobalTheory.Mass.Transp.mem_img (e : V ≃ₗ[K] V') (L : Submodule R V) (y : V') :
    y ∈ _root_.GlobalTheory.Mass.Transp.img e L ↔ e.symm y ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨e.symm y, hy, by simp⟩

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
omit [StarRing K] in
theorem _root_.GlobalTheory.Mass.Transp.img_symm_img (e : V ≃ₗ[K] V') (L : Submodule R V) :
    _root_.GlobalTheory.Mass.Transp.img e.symm (_root_.GlobalTheory.Mass.Transp.img e L) = L := by
  ext x
  simp [_root_.GlobalTheory.Mass.Transp.mem_img]

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
omit [StarRing K] in
theorem _root_.GlobalTheory.Mass.Transp.img_img_symm (e : V ≃ₗ[K] V') (L : Submodule R V') :
    _root_.GlobalTheory.Mass.Transp.img e (_root_.GlobalTheory.Mass.Transp.img e.symm L) = L := by
  ext x
  simp [_root_.GlobalTheory.Mass.Transp.mem_img]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
theorem _root_.GlobalTheory.Mass.Transp.symm_isom (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) :
    ∀ x y, h (e.symm x) (e.symm y) = h' x y := by
  intro x y
  rw [← he]
  simp

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
private lemma mem_dual_iff_hermitian_lattices (L : Submodule R V) (x : V) :
    x ∈ _root_.Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  unfold _root_.Formalism.HermitianLatticesTheory.dual _root_.Formalism.E.hdual
  simp [Submodule.mem_iInf]

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
theorem _root_.GlobalTheory.Mass.Transp.dual_img (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule R V) :
    _root_.Formalism.HermitianLatticesTheory.dual h' (_root_.GlobalTheory.Mass.Transp.img e L) = _root_.GlobalTheory.Mass.Transp.img e (_root_.Formalism.HermitianLatticesTheory.dual h L) := by
  ext y
  rw [mem_dual_iff_hermitian_lattices, _root_.GlobalTheory.Mass.Transp.mem_img, mem_dual_iff_hermitian_lattices]
  constructor
  · intro hy x hx
    rw [← he, LinearEquiv.apply_symm_apply]
    exact hy (e x) ((_root_.GlobalTheory.Mass.Transp.mem_img e L _).2 (by simpa using hx))
  · intro hy z hz
    rw [_root_.GlobalTheory.Mass.Transp.mem_img] at hz
    have := hy _ hz
    rwa [_root_.GlobalTheory.Mass.Transp.symm_isom e he] at this

theorem discN_img (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule R V) :
    discN h' (img e L) = discN h L := by
  unfold discN idxN
  rw [dual_img e he]
  have h1 : ∀ M : Submodule R V, (img e M).toAddSubgroup
      = M.toAddSubgroup.map (e.toAddEquiv : V →+ V') := by
    intro M; ext y; simp [img]
  rw [h1, h1]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ e.injective

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
omit [StarRing K] in
private lemma isLattice_img_of_isLattice (e : V ≃ₗ[K] V') (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (_root_.GlobalTheory.Mass.Transp.img e L) := by
  refine ⟨hL.fg.map _, ?_⟩
  rw [_root_.GlobalTheory.Mass.Transp.img, Submodule.map_coe, LinearMap.coe_restrictScalars,
    Submodule.span_image (e : V →ₗ[K] V'), hL.span_eq_top, Submodule.map_top]
  exact LinearEquiv.range e

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
theorem _root_.GlobalTheory.Mass.Transp.intLat_img (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule R V)
    (hL : _root_.GlobalTheory.Mass.IsIntLat h L) : _root_.GlobalTheory.Mass.IsIntLat h' (_root_.GlobalTheory.Mass.Transp.img e L) := by
  unfold _root_.GlobalTheory.Mass.IsIntLat _root_.Formalism.HermitianLatticesTheory.IsIntegralLat at *
  refine ⟨isLattice_img_of_isLattice e L hL.1, fun x hx y hy => ?_⟩
  rw [_root_.GlobalTheory.Mass.Transp.mem_img] at hx hy
  rw [← _root_.GlobalTheory.Mass.Transp.symm_isom e he]
  exact hL.2 _ hx _ hy

theorem latsDisc_img (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (n : ℕ)
    (L : Submodule R V) (hL : L ∈ latsDisc (R := R) h n) : img e L ∈ latsDisc (R := R) h' n :=
  ⟨intLat_img e he L hL.1, (discN_img e he L).trans hL.2⟩

def conj (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) : isom h ≃* isom h' where
  toFun g := ⟨(e.symm.trans g.1).trans e, fun x y => by
    simp only [LinearEquiv.trans_apply]
    rw [he, g.2, symm_isom e he]⟩
  invFun g := ⟨(e.trans g.1).trans e.symm, fun x y => by
    simp only [LinearEquiv.trans_apply]
    rw [symm_isom e he, g.2, he]⟩
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' g g' := by ext x; simp

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
private lemma isom_smul_eq_img (g : _root_.Formalism.HermitianLatticesTheory.isom h) (L : Submodule R V) :
    g • L = _root_.GlobalTheory.Mass.Transp.img (g : V ≃ₗ[K] V) L := rfl

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
omit [StarRing K] in
private lemma img_trans_eq_img_img (e₁ : V ≃ₗ[K] V') (e₂ : V' ≃ₗ[K] V'') (L : Submodule R V) :
    _root_.GlobalTheory.Mass.Transp.img (e₁.trans e₂) L =
      _root_.GlobalTheory.Mass.Transp.img e₂ (_root_.GlobalTheory.Mass.Transp.img e₁ L) := by
  ext x
  simp [_root_.GlobalTheory.Mass.Transp.mem_img]

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
theorem _root_.GlobalTheory.Mass.Transp.img_smul (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (g : _root_.Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule R V) : _root_.GlobalTheory.Mass.Transp.img e (g • L) = _root_.GlobalTheory.Mass.Transp.conj e he g • _root_.GlobalTheory.Mass.Transp.img e L := by
  rw [isom_smul_eq_img, isom_smul_eq_img, ← img_trans_eq_img_img, ← img_trans_eq_img_img]
  congr 1
  ext x
  simp [_root_.GlobalTheory.Mass.Transp.conj]

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
private lemma mem_genus_iff_isLattice_and_locally_isom (L M : Submodule R V) : M ∈ _root_.Formalism.HermitianLatticesTheory.genus h L ↔ Submodule.IsLattice K M ∧
    ∀ p : Ideal R, p.IsMaximal → ∃ g ∈ _root_.Formalism.HermitianLatticesTheory.isom h,
      _root_.GlobalTheory.Mass.Transp.img g (_root_.Formalism.HermitianLatticesTheory.loc (K := K) p L) = _root_.Formalism.HermitianLatticesTheory.loc (K := K) p M := Iff.rfl

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
private lemma loc_img_eq_img_loc (e : V ≃ₗ[K] V') (p : Ideal R) (L : Submodule R V) :
    _root_.Formalism.HermitianLatticesTheory.loc (K := K) p (_root_.GlobalTheory.Mass.Transp.img e L) =
      _root_.GlobalTheory.Mass.Transp.img e (_root_.Formalism.HermitianLatticesTheory.loc (K := K) p L) := by
  have hsmul : ∀ (s : R) (y : V'), e.symm (s • y) = s • e.symm y :=
    fun s y => LinearMap.map_smul_of_tower e.symm.toLinearMap s y
  ext y
  rw [_root_.GlobalTheory.Mass.Transp.mem_img]
  unfold _root_.Formalism.HermitianLatticesTheory.loc _root_.Formalism.HermitianLatticesTheory.locS
  show (∃ s ∈ _, s • y ∈ _) ↔ (∃ s ∈ _, s • e.symm y ∈ _)
  simp only [_root_.GlobalTheory.Mass.Transp.mem_img, hsmul]

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
theorem _root_.GlobalTheory.Mass.Transp.genus_img (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L M : Submodule R V)
    (hM : M ∈ _root_.Formalism.HermitianLatticesTheory.genus h L) : _root_.GlobalTheory.Mass.Transp.img e M ∈ _root_.Formalism.HermitianLatticesTheory.genus h' (_root_.GlobalTheory.Mass.Transp.img e L) := by
  rw [mem_genus_iff_isLattice_and_locally_isom] at hM ⊢
  refine ⟨isLattice_img_of_isLattice e M hM.1, fun p hp => ?_⟩
  obtain ⟨g, hg, heq⟩ := hM.2 p hp
  refine ⟨(_root_.GlobalTheory.Mass.Transp.conj e he ⟨g, hg⟩ : _root_.Formalism.HermitianLatticesTheory.isom h'), SetLike.coe_mem _, ?_⟩
  rw [loc_img_eq_img_loc, loc_img_eq_img_loc, ← heq, ← img_trans_eq_img_img, ← img_trans_eq_img_img]
  congr 1
  ext x
  simp [_root_.GlobalTheory.Mass.Transp.conj]

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
private lemma mem_isom_iff_preserves_form (g : V ≃ₗ[K] V) :
    g ∈ _root_.Formalism.HermitianLatticesTheory.isom h ↔ ∀ x y, h (g x) (g y) = h x y :=
  Iff.rfl

open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
theorem _root_.GlobalTheory.Mass.Transp.genus_stable (L : Submodule R V) : _root_.GlobalTheory.Mass.Stable (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) := by
  intro g M hM
  rw [isom_smul_eq_img]
  rw [mem_genus_iff_isLattice_and_locally_isom] at hM ⊢
  refine ⟨isLattice_img_of_isLattice _ M hM.1, fun p hp => ?_⟩
  obtain ⟨g', hg', heq⟩ := hM.2 p hp
  refine ⟨g'.trans g.1, fun x y => ?_, ?_⟩
  · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, (mem_isom_iff_preserves_form _).1 g.2,
      (mem_isom_iff_preserves_form _).1 hg']
  · rw [loc_img_eq_img_loc, img_trans_eq_img_img, heq]

theorem latsDisc_stable (n : ℕ) : Stable (isom h) (latsDisc (R := R) h n) :=
  fun g M hM => latsDisc_img g.1 g.2 n M hM

theorem mass_img (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y)
    (X : Set (Submodule R V)) (Y : Set (Submodule R V'))
    (hX : Stable (isom h) X) (hY : Stable (isom h') Y)
    (h1 : ∀ M ∈ X, img e M ∈ Y) (h2 : ∀ M ∈ Y, img e.symm M ∈ X) :
    orbMass (isom h) X = orbMass (isom h') Y := by
  refine GlobalTheory.Mass.OrbTransport.main _ _ _ _ (conj e he) (img e) X Y (fun _ => 1) hX hY ?_
    (fun g x _ => img_smul e he g x) (fun _ _ => rfl)
  refine ⟨h1, fun a _ b _ hab => ?_, fun M hM => ⟨_, h2 M hM, img_img_symm e M⟩⟩
  rw [← img_symm_img e a, hab, img_symm_img]

end General

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ e : V ≃ₗ[K] V', (∀ x y, h' (e x) (e y) = h x y) → (∀ n : ℕ, orbMass (isom h) (latsDisc (R := 𝓞 K) h n) = orbMass (isom h') (latsDisc (R := 𝓞 K) h' n)) ∧ ∀ L : Submodule (𝓞 K) V, orbMass (isom h) (genus h L) = orbMass (isom h') (genus h' (L.map (e.toLinearMap.restrictScalars (𝓞 K)))) ∧ discN h' (L.map (e.toLinearMap.restrictScalars (𝓞 K))) = discN h L ∧ (IsIntLat h' (L.map (e.toLinearMap.restrictScalars (𝓞 K))) ↔ IsIntLat h L) := by
  intro K V _ _ _ _ _ _ _ _ h _ _ V' _ _ _ _ _ h' _ e he
  refine ⟨fun n => mass_img e he _ _ (latsDisc_stable n) (latsDisc_stable n)
    (latsDisc_img e he n) (latsDisc_img e.symm (symm_isom e he) n), fun L => ⟨?_, discN_img e he L, ?_, intLat_img e he L⟩⟩
  · refine mass_img e he _ (genus h' (img e L)) (genus_stable _) (genus_stable _)
      (genus_img e he L) (fun M hM => ?_)
    have := genus_img e.symm (symm_isom e he) _ M hM
    rwa [img_symm_img] at this
  · intro hL
    have := intLat_img e.symm (symm_isom e he) (img e L) hL
    rwa [img_symm_img] at this

end GlobalTheory.Mass.Transp
