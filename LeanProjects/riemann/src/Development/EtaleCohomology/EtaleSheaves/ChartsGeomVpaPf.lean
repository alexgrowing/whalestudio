import Development.EtaleCohomology.EtaleSheaves.FibreIdem

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof

namespace LateralTheory.E.ChartsGeom_vpaPf

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def chartEquiv {Z : Scheme.{0}} {U : Z.Opens} (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ) (B : Subalgebra A K)
    (hr : φ.range = B.toSubring) : Γ(Z, U) ≃+* B :=
  (RingEquiv.ofBijective φ.rangeRestrict ⟨fun a b h => hi (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩).trans
    (RingEquiv.subringCongr hr)

theorem chartEquiv_apply {Z : Scheme.{0}} {U : Z.Opens} (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ)
    (B : Subalgebra A K) (hr : φ.range = B.toSubring) (s : Γ(Z, U)) : ((chartEquiv φ hi B hr s : B) : K) = φ s := rfl

def chartMap {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ)
    (B : Subalgebra A K) (hr : φ.range = B.toSubring) : Spec (CommRingCat.of B) ⟶ Z :=
  Spec.map (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom) ≫ hU.fromSpec

instance {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ)
    (B : Subalgebra A K) (hr : φ.range = B.toSubring) : IsOpenImmersion (chartMap hU φ hi B hr) := by
  unfold chartMap
  have : IsIso (Spec.map (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom)) := by
    have : IsIso (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom) :=
      (RingEquiv.toCommRingCatIso (chartEquiv φ hi B hr)).isIso_hom
    infer_instance
  infer_instance

theorem chartMap_range {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K)
    (hi : Function.Injective φ) (B : Subalgebra A K) (hr : φ.range = B.toSubring) :
    Set.range (chartMap hU φ hi B hr).base = (U : Set Z) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom)) := by
    have : IsIso (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom) :=
      (RingEquiv.toCommRingCatIso (chartEquiv φ hi B hr)).isIso_hom
    infer_instance
  unfold chartMap
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [Set.range_eq_univ.mpr (Scheme.Hom.surjective _), Set.image_univ]
  exact hU.range_fromSpec

theorem chartMap_comp {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {U : Z.Opens} (hU : IsAffineOpen U)
    (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ) (B : Subalgebra A K) (hr : φ.range = B.toSubring)
    (hA : ∀ a : A, φ (p.appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = algebraMap A K a) :
    chartMap hU φ hi B hr ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  have hp : p = Z.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hr2 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top : U ⟶ ⊤).op ≫
      CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom = CommRingCat.ofHom (algebraMap A B) := by
    ext a
    have := hA a
    simp only [Scheme.Hom.appLE, ConcreteCategory.comp_apply] at this
    simp [chartEquiv_apply]
    exact this
  rw [hp, chartMap, Category.assoc, ← Category.assoc hU.fromSpec, IsAffineOpen.fromSpec_toSpecΓ, ← Spec.map_comp,
    ← Spec.map_comp, ← hr2]
  simp only [Category.assoc]

def ChartData {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K) : Prop :=
  ∃ (U V : Z.Opens) (φU : Γ(Z, U) →+* K) (φV : Γ(Z, V) →+* K) (φW : Γ(Z, U ⊓ V) →+* K),
    IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen (U ⊓ V) ∧ U ⊔ V = ⊤ ∧
    Function.Injective φU ∧ Function.Injective φV ∧ Function.Injective φW ∧
    φU.range = B.toSubring ∧ φV.range = C.toSubring ∧ φW.range = (AdjoinInv B t).toSubring ∧
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s) = φU s) ∧
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s) = φV s) ∧
    (∀ a : A, φU (p.appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = algebraMap A K a) ∧
    (∀ a : A, φV (p.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = algebraMap A K a)

def GeoData : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ ChartData p B C t

def CoverOfData : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K),
    Charts B C t → ChartData p B C t → Cover p B C t

def Overlap : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K), Charts B C t →
  ∀ (U V : Z.Opens) (φU : Γ(Z, U) →+* K) (φV : Γ(Z, V) →+* K) (φW : Γ(Z, U ⊓ V) →+* K)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V), IsAffineOpen (U ⊓ V) → U ⊔ V = ⊤ →
    ∀ (iU : Function.Injective φU) (iV : Function.Injective φV), Function.Injective φW →
    ∀ (rU : φU.range = B.toSubring) (rV : φV.range = C.toSubring), φW.range = (AdjoinInv B t).toSubring →
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s) = φU s) →
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s) = φV s) →
    ∀ (x : PrimeSpectrum B) (y : PrimeSpectrum C),
      (chartMap hU φU iU B rU).base x = (chartMap hV φV iV C rV).base y ↔
        ∃ Q : PrimeSpectrum (AdjoinInv B t), Restr B t Q B x ∧ Restr B t Q C y

theorem coverOfData_of (hO : Overlap) : CoverOfData := by
  intro A _ _ K _ _ Z p B C t hc hd
  obtain ⟨U, V, φU, φV, φW, hU, hV, hW, hUV, iU, iV, iW, rU, rV, rW, cU, cV, aU, aV⟩ := hd
  refine ⟨⟨chartMap hU φU iU B rU, chartMap hV φV iV C rV, inferInstance, inferInstance, ?_,
    chartMap_comp p hU φU iU B rU aU, chartMap_comp p hV φV iV C rV aV,
    hO A K p B C t hc U V φU φV φW hU hV hW hUV iU iV iW rU rV rW cU cV⟩⟩
  rw [chartMap_range, chartMap_range, ← TopologicalSpace.Opens.coe_sup, hUV, TopologicalSpace.Opens.coe_top]

theorem ChartsGeom_of' (hG : GeoData) (hC : CoverOfData) : LateralTheory.E.StdChartsProof.ChartsGeom := by
  intro A _ _ Z p hIL hZ
  obtain ⟨K, hK, hA, B, C, t, hc, hint, hd⟩ := hG A p hIL hZ
  exact ⟨K, hK, hA, B, C, t, hc, hint, hC A K p B C t hc hd⟩

end LateralTheory.E.ChartsGeom_vpaPf
