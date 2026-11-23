import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrameStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem exists_local {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {Y : Var F}
    {ρ : Y.X ⟶ gen Z} (hρ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g₀ : GenFrame e ρ) (τ : E →+* ℂ) (y : Y.X) :
    ∃ (U : (gen Z).Opens) (P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn), ρ y ∈ U ∧
      ∀ z : Y.X, ρ z ∈ U → ∃ φ f, Fits g₀ τ z φ f P := by
  obtain ⟨U, hU, φ, f, hy, hφ, -⟩ := GlobalTheory.T.exists_affine_stable_lie_eigenspace_frame E H Dw l Xo c O β Z (ρ y)
  have hg : ⊤ ≤ (genericPt Y ≫ ρ) ⁻¹ᵁ U := gen_le ρ hy
  let χ : Γ(gen Z, U) →+* Y.Fn := evalPt (genericPt Y ≫ ρ) U hg
  have hχ : genericPt Y ≫ ρ = spMap χ ≫ hU.fromSpec := eq_spec_fromSpec hU _ hg
  have hc : constF e Y = χ.comp φ := EigLoc.spMap_inj (by
    have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (GlobalTheory.FlagBundle.ratOf Y).pt_s
    have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
    have h3 : spMap (χ.comp φ) = spMap χ ≫ spMap φ := by rw [← Spec.map_comp]; rfl
    have h4 : spMap (constF e Y) = spMap (algebraMap F Y.Fn) ≫ spMap e.symm.toRingHom := by rw [← Spec.map_comp]; rfl
    have h5 : spMap χ ≫ spMap φ = (genericPt Y ≫ ρ) ≫ genStr Z := by
      rw [hχ, ← hφ]; exact (Category.assoc _ _ _).symm
    rw [h3, h4, h5, ← h1, ← hρ]
    simp only [Category.assoc, h2, Category.comp_id])
  obtain ⟨f', hf'⟩ := f.exists_isMap χ (x' := genericPt Y ≫ ρ ≫ genι Z) hc
    (by rw [← Category.assoc, hχ]; exact Category.assoc _ _ _)
  refine ⟨U, g₀.co f' τ, hy, fun z hz => ?_⟩
  have hs : ⊤ ≤ (stalkPt Y z ≫ ρ) ⁻¹ᵁ U := stalk_le ρ hz
  let ψ : Γ(gen Z, U) →+* Y.X.presheaf.stalk z := evalPt (stalkPt Y z ≫ ρ) U hs
  have hψ : stalkPt Y z ≫ ρ = spMap ψ ≫ hU.fromSpec := eq_spec_fromSpec hU _ hs
  have hcomp : (toFn z).comp ψ = χ := EigLoc.spMap_inj ((cancel_mono hU.fromSpec).1 (by
    have h3 : spMap ((toFn z).comp ψ) = spMap (toFn z) ≫ spMap ψ := by rw [← Spec.map_comp]; rfl
    refine Eq.trans ?_ hχ
    rw [h3, ← spMap_toFn z, Category.assoc, Category.assoc, hψ]))
  obtain ⟨k, hk⟩ := f.exists_isMap ψ (x' := stalkPt Y z ≫ ρ ≫ genι Z) rfl
    (by rw [← Category.assoc, hψ]; exact Category.assoc _ _ _)
  have hc' : constF e Y = (toFn z).comp (ψ.comp φ) := by rw [← RingHom.comp_assoc, hcomp, hc]
  have hm : k.IsMap (toFn z) f' := fun τ i => by
    rw [hf', hk, GlobalTheory.GradedPieces.dual_comp, hcomp]
  exact ⟨_, k, (fits_iff hc' hm).2 rfl⟩

theorem UpperTheory.exists_divisor_frame_generic :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : Var F) (ρ : Y.X ⟶ gen Z) (_ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g₀ : GenFrame e ρ) (τ : E →+* ℂ), ∃ (Δ : Y.Dv) (t : Y.X → Y.Fnˣ), (∀ y, Δ.IsEqn y (t y)) ∧ ∀ y, ∃ φ f P, Fits g₀ τ y φ f P ∧ (t y : Y.Fn) * P.det = 1 := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y ρ hρ g₀ τ
  choose U P hU hP using exists_local hρ g₀ τ
  have hdet : ∀ y, IsUnit (P y).det := fun y => by
    obtain ⟨φ, f, h⟩ := hP y y (hU y)
    exact h.isUnit_det
  let t : Y.X → Y.Fnˣ := fun y => (hdet y).unit⁻¹
  have ht : ∀ y, (t y : Y.Fn) = ((P y).det)⁻¹ := fun y => by
    simp only [t, Units.val_inv_eq_inv_val, IsUnit.unit_spec]
  have hgerm : ∀ y z, ρ z ∈ U y → germOf z (t z) = germOf z (t y) := fun y z hz => by
    obtain ⟨φ, f, h⟩ := hP y z hz
    obtain ⟨φ', f', h'⟩ := hP z z (hU z)
    obtain rfl := h.φ_eq h'
    rw [germOf_eq_iff]
    refine ⟨_, f.isUnit_det_co f' τ, ?_⟩
    have h1 := congrArg Matrix.det (h.eq_mul h')
    rw [det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
    have h2 : (t y : Y.Fn) / (t z : Y.Fn) = toFn z (f.co f' τ).det := by
      rw [ht, ht, h1, div_inv_eq_mul, inv_mul_cancel_left₀ (hdet y).ne_zero]
    exact h2.symm
  refine ⟨show cartierGroup Y.X from ⟨fun y => germOf y (t y), fun y =>
    ⟨ρ ⁻¹ᵁ U y, hU y, t y, fun z hz => hgerm y z hz⟩⟩, t, fun _ => rfl, fun y => ?_⟩
  obtain ⟨φ, f, h⟩ := hP y y (hU y)
  exact ⟨φ, f, P y, h, by rw [ht, inv_mul_cancel₀ (hdet y).ne_zero]⟩
