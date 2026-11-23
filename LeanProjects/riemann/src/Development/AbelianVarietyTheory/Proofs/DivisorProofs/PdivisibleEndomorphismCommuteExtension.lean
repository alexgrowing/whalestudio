import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt

theorem dualBaseChange_hom_natural (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K]
    (Γ' : PDivGroup p R) (g' : Γ' ⟶ Γ') :
    dualHom _ _ (PDivGroup.baseChangeMap K g') ≫ (PerfdLat.dualBaseChange K Γ').hom =
      (PerfdLat.dualBaseChange K Γ').hom ≫ PDivGroup.baseChangeMap K (dualHom _ _ g') := by
  exact PDivGroup.hom_ext fun n => BialgHom.ext fun x => (CartierDual.baseChange_map K (g'.app n) x).symm

theorem latExt_stable {p : ℕ} [Fact p.Prime] {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    {Δ : PDivGroup p R} {𝒜 : PDivGroup p K} [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt]
    (π : 𝒜 ⟶ Δ.baseChange K) (f : 𝒜 ⟶ 𝒜) (h : Δ ⟶ Δ) (e : f ≫ π = π ≫ PDivGroup.baseChangeMap K h) :
    ∀ x ∈ latExt π, rigExtMap f x ∈ latExt π := by
  rintro _ ⟨y, rfl⟩
  refine ⟨rigExtMap h y, ?_⟩
  have h1 := LinearMap.congr_fun (rigExtMap_comp f π) ((Δ.toBase K).rig y)
  have h2 := LinearMap.congr_fun (rigExtMap_comp π (PDivGroup.baseChangeMap K h)) ((Δ.toBase K).rig y)
  have h3 := (Δ.toBase K).rig_naturality (Δ.toBase K) h (PDivGroup.baseChangeMap K h) (fun _ _ => rfl) y
  rw [LinearMap.comp_apply] at h1 h2
  rw [← h1, e, h2, h3]

theorem lattice_stable : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (hR : (p : R) = 0) (hK : (p : K) = 0) (Γ' : PDivGroup p R) (𝒜 : PDivGroup p K) (κ : Γ'.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt] (f f' : 𝒜 ⟶ 𝒜) (g g' : Γ' ⟶ Γ'), PDivGroup.baseChangeMap K g ≫ κ = κ ≫ f → PDivGroup.baseChangeMap K g' ≫ κ = κ ≫ f' → f ≫ w = w ≫ dualHom _ _ f' → ∀ x ∈ lattice κ w, rigExtMap f x ∈ lattice κ w := by
  intro p _ R _ _ _ K _ _ _ hR hK Γ' 𝒜 κ w _ _ f f' g g' hg hg' hw x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · obtain ⟨e, e₀, rfl, h⟩ := hy
    refine ⟨PDivGroup.omegaMap _ _ f e, PDivGroup.omegaMap _ _ g e₀, rigExtMap_rigOfOmega f e, ?_⟩
    rw [← LinearMap.comp_apply (PDivGroup.omegaMap _ _ κ), ← PDivGroup.omegaMap_comp, ← hg,
      PDivGroup.omegaMap_comp, LinearMap.comp_apply, h]
    exact ((Γ'.toBase K).omega_naturality (Γ'.toBase K) g (PDivGroup.baseChangeMap K g) (fun _ _ => rfl) e₀).symm
  · have key : f ≫ weilProj κ w = weilProj κ w ≫ PDivGroup.baseChangeMap K (dualHom _ _ g') := by
      unfold weilProj
      rw [reassoc_of% hw, ← Category.assoc (dualHom _ _ f'), ← dualHom_comp, ← hg', dualHom_comp,
        Category.assoc, dualBaseChange_hom_natural]
      simp only [Category.assoc]
    exact latExt_stable (weilProj κ w) f _ key _ hz

end GlobalTheory.BadPt
