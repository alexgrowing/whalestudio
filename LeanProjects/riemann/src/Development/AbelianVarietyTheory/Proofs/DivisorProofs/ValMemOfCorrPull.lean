import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpTorsionDefOver
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem valF_spMap_comp {F F' : Type} [Field F] [Field F'] (σ : F →+* F') {X : Scheme.{0}} (x : Sp F ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valF (spMap σ ≫ x) U f = σ (valF x U f) := by
  classical
  have h' : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun y _ => h (show (spMap σ).base y ∈ (⊤ : (Sp F).Opens) from trivial)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ h le_top]
  exact congrArg (fun q => q.hom ((Scheme.Hom.appLE x U ⊤ h).hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

theorem toStk_valF_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valF x U a) = gs x z U a := by
  classical
  rw [valF, dif_pos ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

variable {K : Type} [Field K] (k₀ : Subfield K) {X Y Y' : Scheme.{0}}

theorem valF_mem_of_defOver {x : Sp K ⟶ X} (hx : DefOver k₀ x) (U : X.Opens) (z : Sp K) (h : x z ∈ U)
    (a : Γ(X, U)) : valF x U a ∈ k₀ := by
  obtain ⟨P₀, rfl⟩ := hx
  have h₀ : ⊤ ≤ P₀ ⁻¹ᵁ U := (top_le_iff_mem P₀ U ((spMap k₀.subtype).base z)).2 h
  rw [valF_spMap_comp k₀.subtype P₀ U h₀ a]
  exact (valF P₀ U a).2

theorem gs_mem_of_defOver {x : Sp K ⟶ X} (hx : DefOver k₀ x) (U : X.Opens) (z : Sp K) (h : x z ∈ U)
    (a : Γ(X, U)) : ∃ c ∈ k₀, gs x z U a = toStk z c :=
  ⟨valF x U a, valF_mem_of_defOver k₀ hx U z h a, (toStk_valF_gs x U z h a).symm⟩

variable {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}

theorem val_mem_of_defOver (t : LB.Gen (LB.LinComb L φ ε)) {r : Sp K ⟶ Y} (hr : DefOver k₀ r) (z : Sp K)
    {J : (Sp K ⟶ X) → L.ι} (hJ : Good L z J) : ∃ c ∈ k₀, (val t r z J).val = toStk z c := by
  have hm := hJ.mem φ r
  obtain ⟨c, hc, e⟩ := gs_mem_of_defOver k₀ hr _ z hm (t.s fun k => J (r ≫ φ k)).val
  exact ⟨c, hc, (gs_unit r z _ hm _).symm.trans e⟩

end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory
variable {K : Type} [Field K] (k₀ : Subfield K)

theorem spMap_subtype_cancel {R : Type} [CommRing R] {a b : Sp k₀ ⟶ Sp R}
    (h : spMap k₀.subtype ≫ a = spMap k₀.subtype ≫ b) : a = b := by
  rw [← Spec.map_preimage a, ← Spec.map_preimage b] at h ⊢
  congr 1
  simp only [spMap, ← Spec.map_comp] at h
  have e := Spec.map_injective h
  ext y
  exact congrArg (fun q => q.hom y) e
end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
variable {K : Type} [Field K] (k₀ : Subfield K)

theorem defOver_comp {X Y : Scheme.{0}} {P : Sp K ⟶ X} (hP : DefOver k₀ P) (g : X ⟶ Y) : DefOver k₀ (P ≫ g) := by
  obtain ⟨P₀, rfl⟩ := hP
  exact ⟨P₀ ≫ g, (Category.assoc _ _ _).symm⟩

theorem defOver_spMap {R : Type} [CommRing R] (f : R →+* K) (hf : ∀ a, f a ∈ k₀) : DefOver k₀ (spMap f) :=
  ⟨spMap (f.codRestrict k₀ hf), by simp only [spMap, ← Spec.map_comp]; rfl⟩

theorem defOver_pullback {R : Type} [CommRing R] {A B : Scheme.{0}} {f : A ⟶ Sp R} {g : B ⟶ Sp R}
    {x : Sp K ⟶ pullback f g} (h₁ : DefOver k₀ (x ≫ pullback.fst f g)) (h₂ : DefOver k₀ (x ≫ pullback.snd f g)) :
    DefOver k₀ x := by
  obtain ⟨Q₁, hQ₁⟩ := h₁
  obtain ⟨Q₂, hQ₂⟩ := h₂
  have hw : Q₁ ≫ f = Q₂ ≫ g := spMap_subtype_cancel k₀ (by
    rw [← Category.assoc, hQ₁, ← Category.assoc, hQ₂, Category.assoc, Category.assoc, pullback.condition])
  refine ⟨pullback.lift Q₁ Q₂ hw, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, pullback.lift_fst, hQ₁]
  · rw [Category.assoc, pullback.lift_snd, hQ₂]

variable {X Y : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}

theorem val_spMap_mem {R : Type} [CommRing R] {L : LB X} {φ : Ix → (Sp R ⟶ X)} (t : LB.Gen (LB.LinComb L φ ε))
    (f : R →+* K) (hf : ∀ a, f a ∈ k₀) (z : Sp K) {J : (Sp K ⟶ X) → L.ι} (hJ : Good L z J) :
    ∃ c ∈ k₀, (val t (spMap f) z J).val = toStk z c :=
  val_mem_of_defOver k₀ t (defOver_spMap k₀ f hf) z hJ

end GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

end GlobalTheory.Poinc.Sep
